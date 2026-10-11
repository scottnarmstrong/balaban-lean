/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Contraction
public import Balaban.Background.ContractionCoreAnalytic
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

section Families

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The data space of Proposition 5.1: `(φ₀, α₀, δΨ, f₁)`. -/
abbrev Edat (G : GeneratingSet d L N₀ k ϱ) (N : ℕ) :=
  (Torus d (N₀ * L ^ k) → Fin N → ℂ) × (G.Ω 1 → ℂ) × (Torus d (N₀ * L ^ k) → Fin N → ℂ) ×
    (G.Ω 1 × Fin N → ℂ)

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

/-- **Proposition 5.1, analyticity.**  On the open set of data satisfying (P1)–(P4) with strict
inequalities, the solution `(δφ, δα)` of the perturbed system (the unique one with
`|δα|₂ ≤ c₆`) is a complex-analytic function of the data `(φ₀, α₀, δΨ, f₁)` (a finite-dimensional
complex vector space), and it satisfies the bounds of `prop51_exists_unique`. -/
theorem prop51_analytic (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (S : GreenSetting G a ν) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁) (hle0 : δ₀ ≤ deltaStar d L N) (hle1 : δ₁ ≤ deltaStar d L N) :
    ∃ sol : Edat G N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ),
      AnalyticOnNhd ℂ sol {p | StrictData G N δ₀ δ₁ p} ∧
      ∀ p : Edat G N, StrictData G N δ₀ δ₁ p →
        IsPerturbed G a ν p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2) (sol p).1 (sol p).2 ∧
        Small G (sol p).2 (cK2 d L N * δ₁) ∧ SupBounds G (sol p).1 (cK2 d L N * δ₁) ∧
        ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
          IsPerturbed G a ν p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2) δφ' δα' →
          Small G δα' (c6 d L N) → δφ' = (sol p).1 ∧ δα' = (sol p).2 := by
  have hPo := isOpen_strictData (G := G) (N := N) δ₀ δ₁
  have hC := coreHyp_small hd h0 h1 hle0 hle1
  have hyp := fun p (hp : StrictData G N δ₀ δ₁ p) => StrictData.hyp S h0 h1 hle0 hle1 hp
  have aΨ : ∀ (p : Edat G N) y i, AnalyticAt ℂ (fun p : Edat G N => p.2.2.1 y i) p :=
    fun p y i => by fun_prop
  have af : ∀ (p : Edat G N) (y : G.Ω 1) i, AnalyticAt ℂ (fun p : Edat G N => p.2.2.2 (y, i)) p :=
    fun p y i => by fun_prop
  obtain ⟨ξs, hanal, hξs, hdφ⟩ := exists_analytic_core
    (P := {p : Edat G N | StrictData G N δ₀ δ₁ p}) (γ := gamma1 d) hPo (ιU := true)
    (fun _ => greenD G a ν) (fun p => dirichletOperator G a ν p.2.1) (fun p => p.2.1)
    (fun p => p.1) (fun p => pertSource G a p.2.2.1 p.2.2.2) (fun _ _ => S.family (N := N))
    (fun p hp => (hyp p hp).setup) hC
    (fun y i p _ => by fun_prop) (fun y p _ => by fun_prop)
    (fun y i p _ => an_pertSource (G := G) a (q := p) (fun p : Edat G N => p.2.2.1)
      (fun p : Edat G N => p.2.2.2) (aΨ p) (af p) y i)
    (fun y z p _ => AnalyticAt.comp (g := fun α : G.Ω 1 → ℂ => dirichletOperator G a ν α y z)
      (f := fun p : Edat G N => p.2.1) (analyticAt_dirichletOperator_apply G a ν p.2.1 y z)
      (by fun_prop))
    (fun y z r hr => (analyticOnNhd_green_apply G hd S.mass S.weights y z r.1
      (alpha_mem_polydisc hr.1)).comp (aa_fst' r))
  have hfixed : ∀ p, StrictData G N δ₀ δ₁ p →
      IsPerturbed G a ν p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2)
        (dphi G (greenD G a ν) p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2) (toAlpha G (ξs p)))
        (toAlpha G (ξs p)) ∧ Small G (toAlpha G (ξs p)) (c6 d L N) := by
    intro p hp
    obtain ⟨hb, hfx, -⟩ := hξs p hp
    rw [mem_closedBall_zero_iff] at hb
    have hs := small_toAlpha G (ξs p) (fun x => (norm_le_pi_norm (ξs p) x).trans hb)
    exact ⟨perturbed_of_fixed S (hyp p hp).alpha0 hC.ρ_nn hC.poly hs (fixed_of_Smap_fixed hfx), hs⟩
  refine ⟨fun p => (dphi G (greenD G a ν) p.2.1 p.1 (pertSource G a p.2.2.1 p.2.2.2)
    (toAlpha G (ξs p)), toAlpha G (ξs p)), ?_, ?_⟩
  · intro p hp
    have hξy : ∀ y, AnalyticAt ℂ (fun p => ξs p y) p := fun y => analyticAt_pi_iff.1 (hanal p hp) y
    have hc : ∀ y : G.Ω 1, AnalyticAt ℂ (fun p : Edat G N => toAlpha G (ξs p) y) p := by
      intro y
      unfold toAlpha
      exact (hξy y).div_const
    refine AnalyticAt.prod ?_ (analyticAt_pi_iff.2 hc)
    refine analyticAt_pi_iff.2 fun ⟨y, j⟩ => ?_
    exact hdφ y j p hp
  · intro p hp
    obtain ⟨δφ, δα, hP, hs, hsup, huniq⟩ := prop51_exists_unique hd (hyp p hp)
    obtain ⟨hPs, hSs⟩ := hfixed p hp
    obtain ⟨e1, e2⟩ := huniq _ _ hPs hSs
    simp only
    rw [e1, e2]
    exact ⟨hP, hs, hsup, huniq⟩

end Families

end Balaban.Background
