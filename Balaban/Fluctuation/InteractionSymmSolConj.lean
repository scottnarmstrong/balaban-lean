/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionSymmSol
public import Balaban.Fluctuation.InteractionSymmRot
public import Balaban.Localization.DecEquivReal

/-!
# Conjugation of the fluctuation problem at complex parameters

`DecEquivReal` treats the fluctuation problem (Theorem I-4a, mode P) for real `α₀`, `φ₀`.  The
expansion terms need the conjugation `s ↦ conj s` on the whole polydisc, where `(φ₀, α₀)` are the
complex decoupled background; here `conj` acts on `s`, `α₀`, `φ₀`, `δα` simultaneously and the
source `(δΨ, f₁)` is real.

* `Nmap_conj_gen`, `dphi_conj_cplx`, `fluctFixed_conj_cplx`: the conjugation identities;
* `Sol_conj`: `Sol (conj s, (conj φ₀, conj α₀, δΨ, f₁)) = conj Sol (s, (φ₀, α₀, δΨ, f₁))`.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

local notation "cj" => starRingEnd ℂ

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- Pointwise complex conjugate of a field `Torus → ℂ^N`. -/
def cjSite {X : Type*} (φ : X → Fin N → ℂ) : X → Fin N → ℂ := fun x i => cj (φ x i)

theorem gdef_cjSite (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : G.Ω 1) :
    cj (gdef G φ₀ x) = gdef G (cjSite φ₀) x := by
  simp [gdef, cjSite]

/-- **Conjugation of `𝒩`** for arbitrary complex `H₀`, `φ₀` and a real source. -/
theorem Nmap_conj_gen (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    {Fs : G.Ω 1 × Fin N → ℂ} (hF : ∀ p, cj (Fs p) = Fs p) (δφ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) :
    cj (Nmap G H₀ ιU φ₀ Fs δφ x) = Nmap G (cjm H₀) ιU (cjSite φ₀) Fs (fun p => cj (δφ p)) x := by
  unfold Nmap
  have e1 : ∀ (u : G.Ω 1 × Fin N → ℂ), cj ((commK H₀ (restrictField G φ₀) *ᵥ u) x) =
      (commK (cjm H₀) (restrictField G (cjSite φ₀)) *ᵥ fun p => cj (u p)) x := by
    intro u
    rw [commK_mulVec, commK_mulVec, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [cjm, restrictField, cjSite]
  have e2 : cj (Rvec H₀ δφ δφ x) = Rvec (cjm H₀) (fun p => cj (δφ p)) (fun p => cj (δφ p)) x := by
    rw [Rvec_eq, Rvec_eq]
    have l1 : ∀ w : G.Ω 1 × Fin N → ℂ, ∀ i,
        cj ((liftOp N H₀ *ᵥ w) (x, i)) = (liftOp N (cjm H₀) *ᵥ fun q => cj (w q)) (x, i) := by
      intro w i; rw [cj_liftOp_mulVec]
    simp only [map_sub, map_sum, map_mul, l1]
    congr 2
    rw [cj_mulVec_apply]
    congr 1
    funext y
    simp
  have half : cj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have e3 : cj ((H₀ *ᵥ gdef G φ₀) x) = ((cjm H₀) *ᵥ gdef G (cjSite φ₀)) x := by
    rw [cj_mulVec_apply]
    congr 1
    funext y
    exact gdef_cjSite φ₀ y
  have e0 : cj (∑ i, (φ₀ (↑x) i + δφ (x, i)) * Fs (x, i)) =
      ∑ i, (cjSite φ₀ (↑x) i + cj (δφ (x, i))) * Fs (x, i) := by
    simp only [map_sum, map_mul, map_add, hF, cjSite]
  cases ιU
  · simp only [Bool.false_eq_true, ite_false, map_add, map_sub, map_mul, e0, e1, e2, half,
      map_zero]
  · simp only [ite_true, map_add, map_sub, map_mul, e0, e1, e2, half, e3]

theorem Fsrc_conj_cplx (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    {Fs : G.Ω 1 × Fin N → ℂ} (hF : ∀ p, cj (Fs p) = Fs p) (δα : G.Ω 1 → ℂ) (p : G.Ω 1 × Fin N) :
    cj (Fsrc (G := G) φ₀ Fs δα p) = Fsrc (G := G) (cjSite φ₀) Fs (fun x => cj (δα x)) p := by
  simp [Fsrc, hF, cjSite]

/-- **Conjugation of `δφ(δα)`** for complex `α₀`, `φ₀`. -/
theorem dphi_conj_cplx {𝒢 𝒢' : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ}
    (h𝒢 : ∀ α, cjm (𝒢 α) = 𝒢' (fun x => cj (α x))) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) {Fs : G.Ω 1 × Fin N → ℂ} (hF : ∀ p, cj (Fs p) = Fs p)
    (δα : G.Ω 1 → ℂ) (p : G.Ω 1 × Fin N) :
    cj (dphi G 𝒢 α₀ φ₀ Fs δα p) =
      dphi G 𝒢' (fun x => cj (α₀ x)) (cjSite φ₀) Fs (fun x => cj (δα x)) p := by
  unfold dphi
  rw [cj_liftOp_mulVec, h𝒢]
  have e1 : (fun x => cj ((α₀ + δα) x)) = (fun x => cj (α₀ x)) + fun x => cj (δα x) := by
    funext x; simp
  rw [e1]
  congr 2
  funext q
  exact Fsrc_conj_cplx φ₀ hF δα q

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **Conjugation of the fluctuation fixed point equation at complex parameters.** -/
theorem fluctFixed_conj_cplx {s : Dec2.DecParams C} (ιU : Bool) (α₀ : H.Ω 1 → ℂ)
    (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (hΨ : ∀ x, IsRealVec (δΨ x))
    {f₁ : H.Ω 1 × Fin N → ℂ} (hf : ∀ p, cj (f₁ p) = f₁ p) {δα : H.Ω 1 → ℂ}
    (h : Dec2.DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα) :
    Dec2.DecFixed C H a ν (fun P => cj (s P)) ιU (fun x => cj (α₀ x)) (cjSite φ₀)
      (pertSource H a δΨ f₁) (fun x => cj (δα x)) := by
  have hF : ∀ p, cj (pertSource H a δΨ f₁ p) = pertSource H a δΨ f₁ p :=
    pertSource_real hΨ hf a
  have h𝒢 := fun β => decG2_conj (C := C) (H := H) (a := a) (ν := ν) s β
  unfold Dec2.DecFixed at h ⊢
  funext x
  have e := congrFun h x
  have := Nmap_conj_gen (dirichletOperator H a ν α₀) ιU φ₀ hF
    (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα) x
  rw [e, cjm_dirichlet] at this
  have hd : dphi H (Dec2.decG C H a ν (fun P => cj (s P))) (fun x => cj (α₀ x)) (cjSite φ₀)
      (pertSource H a δΨ f₁) (fun x => cj (δα x)) =
      fun p => cj (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα p) :=
    funext fun p => (dphi_conj_cplx h𝒢 α₀ φ₀ hF δα p).symm
  rw [hd]
  exact this.symm

end Balaban.Localization.DecEquiv

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

local notation "cj" => starRingEnd ℂ

section Sol

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν BG BG₂ κ eps δ₁ : ℝ}

/-- **Reality of the fluctuation solution map**: for a real source `(δΨ, f₁)`,
`Sol (conj s, (conj φ₀, conj α₀, δΨ, f₁)) = conj Sol (s, (φ₀, α₀, δΨ, f₁))`. -/
theorem Sol_conj
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {α₀ : Hm.Ω 1 → ℂ} {f₁ : Hm.Ω 1 × Fin N → ℂ}
    (hΨ : ∀ x, DecEquiv.IsRealVec (δΨ x)) (hf : ∀ p, cj (f₁ p) = f₁ p)
    (he : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ (φ₀, α₀, δΨ, f₁))
    (he' : StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁
      (DecEquiv.cjSite φ₀, fun x => cj (α₀ x), δΨ, f₁)) :
    Sol (fun P => cj (s P), (DecEquiv.cjSite φ₀, fun x => cj (α₀ x), δΨ, f₁)) =
      (fun p => cj ((Sol (s, (φ₀, α₀, δΨ, f₁))).1 p),
        fun x => cj ((Sol (s, (φ₀, α₀, δΨ, f₁))).2 x)) := by
  have hs' : ∀ P, ‖(fun P => cj (s P)) P‖ < Real.exp κ := fun P => by simpa using hs P
  obtain ⟨hfld, hfix, hs6, -, -, -⟩ := hSol (s, (φ₀, α₀, δΨ, f₁)) hs he
  obtain ⟨hfld', hfix', hs6', -, -, huniq'⟩ :=
    hSol (fun P => cj (s P), (DecEquiv.cjSite φ₀, fun x => cj (α₀ x), δΨ, f₁)) hs' he'
  simp only at hfld hfix hfld' hfix' huniq'
  have hδ : (Sol (fun P => cj (s P), (DecEquiv.cjSite φ₀, fun x => cj (α₀ x), δΨ, f₁))).2 =
      fun x => cj ((Sol (s, (φ₀, α₀, δΨ, f₁))).2 x) :=
    (huniq' _ (DecEquiv.small_conj hs6)
      (DecEquiv.fluctFixed_conj_cplx false α₀ φ₀ δΨ hΨ hf hfix)).symm
  refine Prod.ext ?_ hδ
  show (Sol (fun P => cj (s P), (DecEquiv.cjSite φ₀, fun x => cj (α₀ x), δΨ, f₁))).1 = _
  rw [hfld', hδ]
  funext p
  rw [hfld]
  have h𝒢 := fun β => DecEquiv.decG2_conj (C := coverOf Gp) (H := Hm) (a := compWeight L a₁)
    (ν := ν) s β
  exact (DecEquiv.dphi_conj_cplx h𝒢 α₀ φ₀
    (DecEquiv.pertSource_real hΨ hf (compWeight L a₁)) _ p).symm

end Sol

end Balaban.Localization
