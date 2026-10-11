/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Contraction
public import Balaban.Multiscale.Analyticity
public import Balaban.Analysis.Contraction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analyticity of the solution of the perturbed system in the data (Proposition 5.1)
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Explicit

variable {G : GeneratingSet d L N₀ k ϱ}

/-- Entry-wise formula for `𝒩` (all matrix products written out as finite sums). -/
noncomputable def Nexp (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ)
    (H : Matrix (G.Ω 1) (G.Ω 1) ℂ) (x : G.Ω 1) : ℂ :=
  ∑ i, (φ₀ x i + δφ (x, i)) * Fs (x, i)
    - ∑ y, ∑ i, H x y * (φ₀ x i - φ₀ y i) * δφ (y, i)
    + 1 / 2 * ((∑ y, H x y * ∑ i, δφ (y, i) * δφ (y, i)) -
        2 * ∑ i, δφ (x, i) * ∑ y, H x y * δφ (y, i))
    + 1 / 2 * ∑ y, H x y * (∑ i, φ₀ y i * φ₀ y i - 1)

theorem Nmap_explicit (a : ℕ → ℝ) (ν : ℝ) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Nmap G a ν α₀ φ₀ Fs δφ x = Nexp φ₀ Fs δφ (dirichletOperator G a ν α₀) x := by
  unfold Nmap Nexp
  rw [commK_mulVec, Rvec_eq]
  have h1 : ∀ i, (liftOp N (dirichletOperator G a ν α₀) *ᵥ δφ) (x, i) =
      ∑ y, dirichletOperator G a ν α₀ x y * δφ (y, i) := by
    intro i; rw [liftOp_mulVec]; rfl
  simp only [h1, restrictField]
  have h2 : (dirichletOperator G a ν α₀ *ᵥ fun y => ∑ i, δφ (y, i) * δφ (y, i)) x =
      ∑ y, dirichletOperator G a ν α₀ x y * ∑ i, δφ (y, i) * δφ (y, i) := rfl
  have h3 : (dirichletOperator G a ν α₀ *ᵥ gdef G φ₀) x =
      ∑ y, dirichletOperator G a ν α₀ x y * (∑ i, φ₀ y i * φ₀ y i - 1) := rfl
  rw [h2, h3]
  ring

end Explicit

section An

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

theorem aa_sum' {ι : Type*} (s : Finset ι) {f : ι → Q → ℂ} {q : Q}
    (h : ∀ i ∈ s, AnalyticAt ℂ (f i) q) : AnalyticAt ℂ (fun q => ∑ i ∈ s, f i q) q :=
  Finset.analyticAt_fun_sum _ h

theorem an_Nexp {G : GeneratingSet d L N₀ k ϱ} {q : Q}
    (φ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ) (Fs dφ : Q → G.Ω 1 × Fin N → ℂ)
    (Hm : Q → Matrix (G.Ω 1) (G.Ω 1) ℂ) (x : G.Ω 1)
    (hφ : ∀ y i, AnalyticAt ℂ (fun q => φ q y i) q)
    (hF : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => Fs q (y, i)) q)
    (hd : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => dφ q (y, i)) q)
    (hH : ∀ y z, AnalyticAt ℂ (fun q => Hm q y z) q) :
    AnalyticAt ℂ (fun q => Nexp (φ q) (Fs q) (dφ q) (Hm q) x) q := by
  unfold Nexp
  have s1 : AnalyticAt ℂ (fun q => ∑ i, (φ q x i + dφ q (x, i)) * Fs q (x, i)) q :=
    aa_sum' _ fun i _ => ((hφ x i).add (hd x i)).mul (hF x i)
  have s2 : AnalyticAt ℂ (fun q => ∑ y, ∑ i, Hm q x y * (φ q x i - φ q y i) * dφ q (y, i)) q :=
    aa_sum' _ fun y _ => aa_sum' _ fun i _ =>
      ((hH x y).mul ((hφ x i).sub (hφ y i))).mul (hd y i)
  have s3 : AnalyticAt ℂ (fun q => ∑ y, Hm q x y * ∑ i, dφ q (y, i) * dφ q (y, i)) q :=
    aa_sum' _ fun y _ => (hH x y).mul (aa_sum' _ fun i _ => (hd y i).mul (hd y i))
  have s4 : AnalyticAt ℂ (fun q => ∑ i, dφ q (x, i) * ∑ y, Hm q x y * dφ q (y, i)) q :=
    aa_sum' _ fun i _ => (hd x i).mul (aa_sum' _ fun y _ => (hH x y).mul (hd y i))
  have s5 : AnalyticAt ℂ (fun q => ∑ y, Hm q x y * (∑ i, φ q y i * φ q y i - 1)) q :=
    aa_sum' _ fun y _ => (hH x y).mul ((aa_sum' _ fun i _ => (hφ y i).mul (hφ y i)).sub
      analyticAt_const)
  exact ((s1.sub s2).add (analyticAt_const.mul (s3.sub (analyticAt_const.mul s4)))).add
    (analyticAt_const.mul s5)

theorem an_Dentry {G : GeneratingSet d L N₀ k ϱ} (a : ℕ → ℝ) (ν : ℝ) {q : Q}
    (α : Q → G.Ω 1 → ℂ) (hα : ∀ x, AnalyticAt ℂ (fun q => α q x) q) (i j : G.Ω 1) :
    AnalyticAt ℂ (fun q => dirichletOperator G a ν (α q) i j) q :=
  (analyticAt_dirichletOperator_apply G a ν (α q) i j).comp (analyticAt_pi_iff.2 hα)

theorem an_dphi {G : GeneratingSet d L N₀ k ϱ} (a : ℕ → ℝ) (ν : ℝ) {q : Q}
    (α : Q → G.Ω 1 → ℂ) (F : Q → G.Ω 1 × Fin N → ℂ)
    (hα : ∀ x, AnalyticAt ℂ (fun q => α q x) q)
    (hF : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => F q (y, i)) q)
    (hdet : (dirichletOperator G a ν (α q)).det ≠ 0) (y : G.Ω 1) (j : Fin N) :
    AnalyticAt ℂ (fun q => (liftOp N (dirichletOperator G a ν (α q))⁻¹ *ᵥ F q) (y, j)) q := by
  have e : ∀ q, (liftOp N (dirichletOperator G a ν (α q))⁻¹ *ᵥ F q) (y, j) =
      ∑ z, (dirichletOperator G a ν (α q))⁻¹ y z * F q (z, j) := by
    intro q; rw [liftOp_mulVec]; rfl
  simp_rw [e]
  exact aa_sum' _ fun z _ =>
    (analyticAt_inv_apply (fun i j => an_Dentry a ν α hα i j) hdet y z).mul (hF z j)

end An

@[fun_prop] theorem aa_fst' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (q : E × F) :
    AnalyticAt ℂ (fun q : E × F => q.1) q := (ContinuousLinearMap.fst ℂ E F).analyticAt q

@[fun_prop] theorem aa_snd' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (q : E × F) :
    AnalyticAt ℂ (fun q : E × F => q.2) q := (ContinuousLinearMap.snd ℂ E F).analyticAt q

@[fun_prop] theorem aa_eval' {ι β : Type*} [Fintype ι] [NormedAddCommGroup β] [NormedSpace ℂ β]
    (i : ι) (q : ι → β) : AnalyticAt ℂ (fun f : ι → β => f i) q :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => β) i).analyticAt q

section Families

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The data space of Proposition 5.1: `(φ₀, α₀, δΨ, f₁)`. -/
abbrev Edat (G : GeneratingSet d L N₀ k ϱ) (N : ℕ) :=
  (Torus d (N₀ * L ^ k) → Fin N → ℂ) × (G.Ω 1 → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) ×
    (G.Ω 1 × Fin N → ℂ)

/-- The variable of the fixed-point map: `(ξ, p)`. -/
abbrev Qvar (G : GeneratingSet d L N₀ k ϱ) (N : ℕ) := (G.Ω 1 → ℂ) × Edat G N

theorem an_pertSource (a : ℕ → ℝ) {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (δΨ : Q → Torus d (N₀ * L ^ k) → Fin N → ℂ) (f₁ : Q → G.Ω 1 × Fin N → ℂ)
    (hΨ : ∀ y i, AnalyticAt ℂ (fun q => δΨ q y i) q)
    (hf : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q => f₁ q (y, i)) q) (y : G.Ω 1) (i : Fin N) :
    AnalyticAt ℂ (fun q => pertSource G a (δΨ q) (f₁ q) (y, i)) q := by
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply]
  refine ((analyticAt_const.mul (hΨ y i)).add ?_).add (hf y i)
  refine aa_sum' _ fun μ _ => ?_
  refine AnalyticAt.add ?_ ?_
  · by_cases h : (y : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G
    · simp only [h, ↓reduceIte]; exact hΨ _ i
    · simp only [h, ↓reduceIte]; exact analyticAt_const
  · by_cases h : (y : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G
    · simp only [h, ↓reduceIte]; exact hΨ _ i
    · simp only [h, ↓reduceIte]; exact analyticAt_const

variable (G) (a : ℕ → ℝ) (ν : ℝ) in
/-- The fixed-point map `T(ξ, p) = ℓ² 𝒩(δφ(δα(ξ)))` with the data `p = (φ₀, α₀, δΨ, f₁)`. -/
noncomputable def Tmap (q : Qvar G N) : G.Ω 1 → ℂ :=
  Smap G a ν q.2.2.1 q.2.1 (pertSource G a q.2.2.2.1 q.2.2.2.2) q.1

theorem an_Tmap (a : ℕ → ℝ) (ν : ℝ) (q : Qvar G N)
    (hdet : (dirichletOperator G a ν (q.2.2.1 + toAlpha G q.1)).det ≠ 0) :
    AnalyticAt ℂ (Tmap G a ν) q := by
  refine analyticAt_pi_iff.2 fun x => ?_
  have hc : ∀ (y : G.Ω 1), AnalyticAt ℂ (fun q : Qvar G N => toAlpha G q.1 y) q := by
    intro y
    unfold toAlpha
    fun_prop
  have hφ : ∀ y i, AnalyticAt ℂ (fun q : Qvar G N => q.2.1 y i) q := fun y i => by fun_prop
  have hα0 : ∀ y, AnalyticAt ℂ (fun q : Qvar G N => q.2.2.1 y) q := fun y => by fun_prop
  have hΨ : ∀ y i, AnalyticAt ℂ (fun q : Qvar G N => q.2.2.2.1 y i) q := fun y i => by fun_prop
  have hf : ∀ (y : G.Ω 1) i, AnalyticAt ℂ (fun q : Qvar G N => q.2.2.2.2 (y, i)) q :=
    fun y i => by fun_prop
  have hF := an_pertSource (G := G) a (q := q) (fun q : Qvar G N => q.2.2.2.1)
    (fun q : Qvar G N => q.2.2.2.2) hΨ hf
  have hα : ∀ y, AnalyticAt ℂ (fun q : Qvar G N => (q.2.2.1 + toAlpha G q.1) y) q := by
    intro y
    simp only [Pi.add_apply]
    exact (hα0 y).add (hc y)
  have hFs : ∀ (y : G.Ω 1) j, AnalyticAt ℂ (fun q : Qvar G N =>
      Fsrc q.2.1 (pertSource G a q.2.2.2.1 q.2.2.2.2) (toAlpha G q.1) (y, j)) q := by
    intro y j
    unfold Fsrc
    exact (hF y j).sub ((hc y).mul (hφ y j))
  have hd := an_dphi (G := G) a ν (q := q) (fun q : Qvar G N => q.2.2.1 + toAlpha G q.1)
    (fun q : Qvar G N => Fsrc q.2.1 (pertSource G a q.2.2.2.1 q.2.2.2.2) (toAlpha G q.1)) hα hFs
    hdet
  have hH := fun y z => an_Dentry (G := G) a ν (q := q) (fun q : Qvar G N => q.2.2.1) hα0 y z
  have hN := an_Nexp (G := G) (q := q) (fun q : Qvar G N => q.2.1)
    (fun q : Qvar G N => pertSource G a q.2.2.2.1 q.2.2.2.2)
    (fun q : Qvar G N => dphi G a ν q.2.2.1 q.2.1 (pertSource G a q.2.2.2.1 q.2.2.2.2)
      (toAlpha G q.1))
    (fun q : Qvar G N => dirichletOperator G a ν q.2.2.1) x hφ hF hd hH
  have hℓ : AnalyticAt ℂ (fun _ : Qvar G N => ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ)) q :=
    analyticAt_const
  have := hℓ.mul hN
  refine this.congr (Filter.Eventually.of_forall fun q' => ?_)
  simp only [Tmap, Smap, Nmap_explicit]
  rfl

theorem continuous_vn : Continuous (vn : (Fin N → ℂ) → ℝ) := by
  unfold vn
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

theorem isOpen_forall_lt {α E : Type*} [Finite α] [TopologicalSpace E] {f : α → E → ℝ}
    {c : α → ℝ} (hf : ∀ a, Continuous (f a)) : IsOpen {p | ∀ a, f a p < c a} := by
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_lt (hf a) continuous_const

/-- The open set of data of Proposition 5.1: the hypotheses (P1)–(P4) with strict inequalities
(`δ₀, δ₁` fixed numbers). -/
def StrictData (G : GeneratingSet d L N₀ k ϱ) (N : ℕ) (δ₀ δ₁ : ℝ) (p : Edat G N) : Prop :=
  (∀ (x : G.Ω 1) (μ : Fin d),
      vn (p.1 ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - p.1 x) <
        δ₀ / G.spacing (x : Torus d (N₀ * L ^ k)) ∧
      vn (p.1 ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - p.1 x) <
        δ₀ / G.spacing (x : Torus d (N₀ * L ^ k))) ∧
  (∀ x : G.Ω 1, vn (fun i => ∑ μ : Fin d, (p.1 ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      p.1 ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * p.1 x i)) <
      δ₀ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) ∧
  (∀ x : G.Ω 1, vn (p.1 x) < 3 / 2) ∧
  (∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.1 x‖ < δ₀) ∧
  (∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.2.2 (x, i)‖ < δ₁) ∧
  (∀ x : dataSites G, vn (p.2.2.1 x) < δ₁) ∧
  (∀ x : G.Ω 1, ‖gdef G p.1 x‖ < δ₁) ∧
  (∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
    ‖negLap (zeroExt (G.Ω 1) (gdef G p.1)) (x : Torus d (N₀ * L ^ k))‖ < δ₁)

theorem isOpen_strictData_aux1 (δ₀ : ℝ) : IsOpen {p : Edat G N | ∀ (x : G.Ω 1) (μ : Fin d),
      vn (p.1 ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) - p.1 x) <
        δ₀ / G.spacing (x : Torus d (N₀ * L ^ k)) ∧
      vn (p.1 ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) - p.1 x) <
        δ₀ / G.spacing (x : Torus d (N₀ * L ^ k))} := by
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun μ => IsOpen.inter ?_ ?_
  · exact isOpen_lt (continuous_vn.comp (by fun_prop)) continuous_const
  · exact isOpen_lt (continuous_vn.comp (by fun_prop)) continuous_const

theorem isOpen_strictData_aux2 (δ₀ : ℝ) : IsOpen {p : Edat G N | ∀ x : G.Ω 1,
    vn (fun i => ∑ μ : Fin d, (p.1 ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      p.1 ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * p.1 x i)) <
      δ₀ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2} := by
  refine isOpen_forall_lt (f := fun (x : G.Ω 1) (p : Edat G N) => vn (fun i => ∑ μ : Fin d,
      (p.1 ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i +
      p.1 ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i - 2 * p.1 x i)))
      (c := fun x => δ₀ / G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) fun x => ?_
  refine continuous_vn.comp (continuous_pi fun i => continuous_finsetSum _ fun μ _ => ?_)
  fun_prop

theorem isOpen_strictData_o3 : IsOpen {p : Edat G N | ∀ x : G.Ω 1, vn (p.1 x) < 3 / 2} :=
  isOpen_forall_lt (f := fun (x : G.Ω 1) (p : Edat G N) => vn (p.1 x))
      (c := fun _ => 3 / 2) fun x => continuous_vn.comp (by fun_prop)

theorem isOpen_strictData_o4 (δ₀ : ℝ) : IsOpen {p : Edat G N | ∀ x : G.Ω 1,
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.1 x‖ < δ₀} :=
  isOpen_forall_lt (f := fun (x : G.Ω 1) (p : Edat G N) =>
      G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.1 x‖) (c := fun _ => δ₀)
      fun x => by fun_prop

theorem isOpen_strictData_o5 (δ₁ : ℝ) : IsOpen {p : Edat G N | ∀ (x : G.Ω 1) (i : Fin N),
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.2.2 (x, i)‖ < δ₁} := by
  have : {p : Edat G N | ∀ (x : G.Ω 1) (i : Fin N),
      G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.2.2 (x, i)‖ < δ₁} =
      {p : Edat G N | ∀ q : G.Ω 1 × Fin N,
        G.spacing (q.1 : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.2.2 q‖ < δ₁} := by
    ext p; simp [Prod.forall]
  rw [this]
  exact isOpen_forall_lt (f := fun (q : G.Ω 1 × Fin N) (p : Edat G N) =>
      G.spacing (q.1 : Torus d (N₀ * L ^ k)) ^ 2 * ‖p.2.2.2 q‖) (c := fun _ => δ₁)
      fun q => by fun_prop

theorem isOpen_strictData_o6 (δ₁ : ℝ) :
    IsOpen {p : Edat G N | ∀ x : dataSites G, vn (p.2.2.1 x) < δ₁} :=
  isOpen_forall_lt (f := fun (x : dataSites G) (p : Edat G N) => vn (p.2.2.1 x))
      (c := fun _ => δ₁) fun x => continuous_vn.comp (by fun_prop)

theorem isOpen_strictData_o7 (δ₁ : ℝ) :
    IsOpen {p : Edat G N | ∀ x : G.Ω 1, ‖gdef G p.1 x‖ < δ₁} :=
  isOpen_forall_lt (f := fun (x : G.Ω 1) (p : Edat G N) => ‖gdef G p.1 x‖)
      (c := fun _ => δ₁) fun x => by unfold gdef; fun_prop

theorem isOpen_strictData_o8 (δ₁ : ℝ) : IsOpen {p : Edat G N | ∀ x : G.Ω 1,
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
    ‖negLap (zeroExt (G.Ω 1) (gdef G p.1)) (x : Torus d (N₀ * L ^ k))‖ < δ₁} := by
  refine isOpen_forall_lt (f := fun (x : G.Ω 1) (p : Edat G N) => G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      ‖negLap (zeroExt (G.Ω 1) (gdef G p.1)) (x : Torus d (N₀ * L ^ k))‖) (c := fun _ => δ₁) fun x => ?_
  have hz : ∀ y : Torus d (N₀ * L ^ k),
      Continuous fun p : Edat G N => zeroExt (G.Ω 1) (gdef G p.1) y := by
    intro y
    by_cases hy : y ∈ G.Ω 1
    · simp only [zeroExt, hy, ↓reduceDIte]
      unfold gdef; fun_prop
    · simp only [zeroExt, hy, ↓reduceDIte]; exact continuous_const
  unfold negLap
  refine continuous_const.mul (continuous_norm.comp (continuous_finsetSum _ fun μ _ => ?_))
  exact ((continuous_const.mul (hz _)).sub (hz _)).sub (hz _)

theorem isOpen_strictData (δ₀ δ₁ : ℝ) : IsOpen {p : Edat G N | StrictData G N δ₀ δ₁ p} := by
  unfold StrictData
  simp only [Set.ofPred_and]
  exact (isOpen_strictData_aux1 δ₀).inter ((isOpen_strictData_aux2 δ₀).inter
    (isOpen_strictData_o3.inter ((isOpen_strictData_o4 δ₀).inter ((isOpen_strictData_o5 δ₁).inter
    ((isOpen_strictData_o6 δ₁).inter ((isOpen_strictData_o7 δ₁).inter
    (isOpen_strictData_o8 δ₁)))))))

theorem StrictData.hyp {a : ℕ → ℝ} {ν : ℝ} (S : GreenSetting G a ν) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀)
    (h1 : 0 ≤ δ₁) (hle0 : δ₀ ≤ deltaStar d L N) (hle1 : δ₁ ≤ deltaStar d L N)
    {p : Edat G N} (hp : StrictData G N δ₀ δ₁ p) :
    Prop51Hyp G a ν p.2.1 p.1 p.2.2.1 p.2.2.2 δ₀ δ₁ := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := hp
  refine ⟨S, h0, h1, hle0, hle1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx μ
    exact ⟨(c1 ⟨x, hx⟩ μ).1.le, (c1 ⟨x, hx⟩ μ).2.le⟩
  · intro x hx; exact (c2 ⟨x, hx⟩).le
  · intro x hx; exact (c3 ⟨x, hx⟩).le
  · intro x; exact (c4 x).le
  · intro x i; exact (c5 x i).le
  · intro x hx; exact (c6 ⟨x, hx⟩).le
  · intro x; exact (c7 x).le
  · intro x; exact (c8 x).le

theorem fixed_of_Smap_fixed {a : ℕ → ℝ} {ν : ℝ} {α₀ : G.Ω 1 → ℂ}
    {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {ξ : G.Ω 1 → ℂ}
    (hfix : Smap G a ν α₀ φ₀ Fs ξ = ξ) :
    Nmap G a ν α₀ φ₀ Fs (dphi G a ν α₀ φ₀ Fs (toAlpha G ξ)) = toAlpha G ξ := by
  funext x
  have hp : ((G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
    exact_mod_cast (by positivity : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≠ 0)
  have := congrFun hfix x
  unfold Smap at this
  simp only [toAlpha]
  rw [eq_div_iff hp, mul_comm]
  exact this

end Families

end Balaban.Background
