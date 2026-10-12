/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33SymmRay
public import Balaban.Fluctuation.InteractionSymmSolReal
public import Balaban.Fluctuation.InteractionLoc
public import Balaban.Fluctuation.InteractionETerm

/-!
# The symmetry clause of Proposition 3.3 for the terms of a localized expansion

* `TermRot S XW Rσ T`: the terms `T Y x₀ w σ Θ` are `O(N)`-covariant, i.e.
  `T Y (R x₀) (R w) σ (R Θ) = T Y x₀ w σ Θ` for real orthogonal `R`;
* `TermReal S XW Rσ T`: real arguments give real values;
* `termRot_ray`, `termReal_ray`: the ray terms `rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ` of an analytic,
  `O(N)`-invariant (conjugation covariant) family `Ev`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset Matrix Set Metric

local notation "cj" => starRingEnd ℂ

section Def

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

/-- **`O(N)` covariance of a family of terms** `T Y x₀ w σ Θ` of a localized expansion. -/
def TermRot {ι : Type*} (S : Set (RawData d L (N₁ * L ^ m₁) K N))
    (XW : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))) (Rσ : ℝ)
    (T : ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ) : Prop :=
  ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 → ∀ Y, ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ →
    ∀ Θ ∈ S, T Y (DecEquiv.rotSite (cmat Q) xw.1) (DecEquiv.rotSite (cmat Q) xw.2) σ
      (rotRaw (cmat Q) Θ) = T Y xw.1 xw.2 σ Θ

/-- **Reality of a family of terms**: real arguments give real values. -/
def TermReal {ι : Type*} (S : Set (RawData d L (N₁ * L ^ m₁) K N))
    (XW : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))) (Rσ : ℝ)
    (T : ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ) : Prop :=
  ∀ Y, ∀ xw ∈ XW, (∀ x i, (xw.1 x i).im = 0) → (∀ x i, (xw.2 x i).im = 0) →
    ∀ σ : ℂ, ‖σ‖ < Rσ → σ.im = 0 → ∀ Θ ∈ S, IsRealRaw Θ → cj (T Y xw.1 xw.2 σ Θ) = T Y xw.1 xw.2 σ Θ

theorem rotSite_add (R : Matrix (Fin N) (Fin N) ℂ) {X : Type*} (x y : X → Fin N → ℂ) :
    DecEquiv.rotSite R (x + y) = DecEquiv.rotSite R x + DecEquiv.rotSite R y := by
  funext p; simp [DecEquiv.rotSite, Matrix.mulVec_add]

theorem rotSite_smul (R : Matrix (Fin N) (Fin N) ℂ) {X : Type*} (c : ℂ) (x : X → Fin N → ℂ) :
    DecEquiv.rotSite R (c • x) = c • DecEquiv.rotSite R x := by
  funext p; simp [DecEquiv.rotSite, Matrix.mulVec_smul]

theorem cjSite_add {X : Type*} (x y : X → Fin N → ℂ) :
    DecEquiv.cjSite (x + y) = DecEquiv.cjSite x + DecEquiv.cjSite y := by
  funext p i; simp [DecEquiv.cjSite]

theorem cjSite_smul {X : Type*} (c : ℂ) (x : X → Fin N → ℂ) :
    DecEquiv.cjSite (c • x) = cj c • DecEquiv.cjSite x := by
  funext p i; simp [DecEquiv.cjSite]

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν eps δ₁ : ℝ}

theorem rotRaw_mem {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Θ : RawData d L (N₁ * L ^ m₁) K N} (hΘ : Θ ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps) :
    rotRaw (cmat Q) Θ ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps := by
  obtain ⟨D, hD, rfl⟩ := hΘ
  exact ⟨D.rot (cmat Q), xiCData_rot hQ hD, rfl⟩

theorem rotSite_mem_flBall {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (h : ψ' ∈ FlBall Hm δ₁) :
    DecEquiv.rotSite (cmat Q) ψ' ∈ FlBall Hm δ₁ := fun x hx => by
  show vn (cmat Q *ᵥ ψ' x) < δ₁
  rw [vn_rot (isRealOrth_ofReal hQ)]
  exact h x hx


omit [NeZero N₁] [NeZero L] in
theorem TermRot.mono_XW {ι : Type*} {S : Set (RawData d L (N₁ * L ^ m₁) K N)}
    {XW XW' : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    {Rσ : ℝ} {T : ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ} (h : TermRot S XW Rσ T) (hsub : XW' ⊆ XW) :
    TermRot S XW' Rσ T := fun Q hQ Y xw hxw => h Q hQ Y xw (hsub hxw)

omit [NeZero N₁] [NeZero L] in
theorem TermReal.mono_XW {ι : Type*} {S : Set (RawData d L (N₁ * L ^ m₁) K N)}
    {XW XW' : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    {Rσ : ℝ} {T : ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ} (h : TermReal S XW Rσ T) (hsub : XW' ⊆ XW) :
    TermReal S XW' Rσ T := fun Y xw hxw => h Y xw (hsub hxw)

omit [NeZero N₁] [NeZero L] in
/-- Sums of covariant term families (the combination of `LocInt.finsum`). -/
theorem TermRot.finsum {ι κ : Type*} [DecidableEq ι] {S : Set (RawData d L (N₁ * L ^ m₁) K N)}
    {XW : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))} {Rσ : ℝ}
    (𝒯 : Finset κ) (𝒴 : κ → Finset ι)
    {T : κ → ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ} (h : ∀ τ ∈ 𝒯, TermRot S XW Rσ (T τ)) :
    TermRot S XW Rσ (fun Y x w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x w σ Θ else 0) := by
  intro Q hQ Y xw hxw σ hσ Θ hΘ
  refine Finset.sum_congr rfl fun τ hτ => ?_
  split_ifs
  · exact h τ hτ Q hQ Y xw hxw σ hσ Θ hΘ
  · rfl

omit [NeZero N₁] [NeZero L] in
theorem TermReal.finsum {ι κ : Type*} [DecidableEq ι] {S : Set (RawData d L (N₁ * L ^ m₁) K N)}
    {XW : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))} {Rσ : ℝ}
    (𝒯 : Finset κ) (𝒴 : κ → Finset ι)
    {T : κ → ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ} (h : ∀ τ ∈ 𝒯, TermReal S XW Rσ (T τ)) :
    TermReal S XW Rσ (fun Y x w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x w σ Θ else 0) := by
  intro Y xw hxw hx hw σ hσ hσi Θ hΘ hΘr
  simp only
  rw [map_sum]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  split_ifs
  · exact h τ hτ Y xw hxw hx hw σ hσ hσi Θ hΘ hΘr
  · simp


omit [NeZero N₁] [NeZero L] in
/-- Covariance of a combination `c T + c' T'` (the combination of `LocInt.add₂` and `.smul`). -/
theorem TermRot.add_smul {ι : Type*} [DecidableEq ι] {S : Set (RawData d L (N₁ * L ^ m₁) K N)}
    {XW : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))} {Rσ : ℝ}
    {T T' : ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ} (h : TermRot S XW Rσ T) (h' : TermRot S XW Rσ T')
    (𝒴 𝒴' : Finset ι) (c c' : ℂ) :
    TermRot S XW Rσ (fun Y x w σ Θ => (if Y ∈ 𝒴 then c * T Y x w σ Θ else 0) +
      (if Y ∈ 𝒴' then c' * T' Y x w σ Θ else 0)) := by
  intro Q hQ Y xw hxw σ hσ Θ hΘ
  simp only
  rw [h Q hQ Y xw hxw σ hσ Θ hΘ, h' Q hQ Y xw hxw σ hσ Θ hΘ]

omit [NeZero N₁] [NeZero L] in
theorem TermReal.add_smul {ι : Type*} [DecidableEq ι] {S : Set (RawData d L (N₁ * L ^ m₁) K N)}
    {XW : Set ((CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ))} {Rσ : ℝ}
    {T T' : ι → (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
      RawData d L (N₁ * L ^ m₁) K N → ℂ} (h : TermReal S XW Rσ T) (h' : TermReal S XW Rσ T')
    (𝒴 𝒴' : Finset ι) {c c' : ℂ} (hc : cj c = c) (hc' : cj c' = c') :
    TermReal S XW Rσ (fun Y x w σ Θ => (if Y ∈ 𝒴 then c * T Y x w σ Θ else 0) +
      (if Y ∈ 𝒴' then c' * T' Y x w σ Θ else 0)) := by
  intro Y xw hxw hx hw σ hσ hσi Θ hΘ hΘr
  simp only
  rw [map_add]
  congr 1
  · split_ifs
    · rw [map_mul, hc, h Y xw hxw hx hw σ hσ hσi Θ hΘ hΘr]
    · simp
  · split_ifs
    · rw [map_mul, hc', h' Y xw hxw hx hw σ hσ hσi Θ hΘ hΘr]
    · simp

/-- **The ray terms of an `O(N)`-invariant analytic family are `O(N)`-covariant.** -/
theorem termRot_ray {ι : Type*} {Evs : ι → RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y)
      (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁))
    (hinv : ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 → ∀ Y, ∀ u ∈
      XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁, Evs Y (rotU (cmat Q) u) = Evs Y u)
    {ω : ℂ → ℂ} {R₁ Rσ r : ℝ} (hr : 0 < r) (hR₁ : 1 < R₁) :
    TermRot (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
        ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
          (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
      (fun Y x₀ w σ Θ => rayTerm (dl3 (Evs Y) w) ω x₀ σ Θ) := by
  intro Q hQ Y xw hxw σ hσ Θ hΘ
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  exact rayTerm_dl3_equiv (hEv Y) (rotRaw (cmat Q)) (DecEquiv.rotSite (cmat Q))
    (rotSite_add _) (rotSite_smul _)
    (fun Θ hΘ z hz => hinv Q hQ Y (Θ, z) ⟨hΘ, hz⟩)
    (fun Θ hΘ => rotRaw_mem hQ hΘ) (fun z hz => rotSite_mem_flBall hQ hz) hr hΘ
    (fun t ht τ hτ => hxw σ hσ t (hreal1 t ht) τ hτ)

/-- **The ray terms of a conjugation-covariant analytic family are real** for real arguments. -/
theorem termReal_ray {ι : Type*} {Evs : ι → RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y)
      (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁))
    (hreal : ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
      IsRealRaw u.1 → cj (Evs Y u) = Evs Y (cjU u))
    {ω : ℂ → ℂ} (hω : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (ω (t : ℂ)).im = 0)
    {R₁ Rσ r : ℝ} (hr : 0 < r) (hR₁ : 1 < R₁) :
    TermReal (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
        ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
          (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
      (fun Y x₀ w σ Θ => rayTerm (dl3 (Evs Y) w) ω x₀ σ Θ) := by
  intro Y xw hxw hx hw σ hσ hσim Θ hΘ hΘr
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  exact rayTerm_dl3_conj (hEv Y) (DecEquiv.cjSite (N := N)) cjSite_add cjSite_smul
    (fun z hz => hreal Y (Θ, z) ⟨hΘ, hz⟩ hΘr) hr hΘ (Complex.conj_eq_iff_im.2 hσim)
    (funext fun p => funext fun i => Complex.conj_eq_iff_im.2 (hx p i))
    (funext fun p => funext fun i => Complex.conj_eq_iff_im.2 (hw p i))
    (fun t ht => Complex.conj_eq_iff_im.2 (hω t ht))
    (fun t ht τ hτ => hxw σ hσ t (hreal1 t ht) τ hτ)


/-- **The first-order directional terms of an `O(N)`-invariant analytic family are covariant.** -/
theorem termRot_dir {ι : Type*} {Evs : ι → RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y)
      (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁))
    (hinv : ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 → ∀ Y, ∀ u ∈
      XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁, Evs Y (rotU (cmat Q) u) = Evs Y u)
    {ω : ℂ → ℂ} {R₁ Rσ r : ℝ} (hr : 0 < r) (hR₁ : 1 < R₁) :
    TermRot (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
        ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
          (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
      (fun Y x₀ w σ Θ => dirTerm (Evs Y) ω x₀ w σ Θ) := by
  intro Q hQ Y xw hxw σ hσ Θ hΘ
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  exact dirTerm_equiv (isOpen_flBall (N := N) Hm δ₁) (hEv Y) (rotRaw (cmat Q))
    (DecEquiv.rotSite (cmat Q)) (rotSite_add _) (rotSite_smul _)
    (fun Θ hΘ z hz => hinv Q hQ Y (Θ, z) ⟨hΘ, hz⟩)
    (fun Θ hΘ => rotRaw_mem hQ hΘ) (fun z hz => rotSite_mem_flBall hQ hz) hΘ
    (fun t ht => by simpa using hxw σ hσ t (hreal1 t ht) 0 (by simp [hr.le]))

/-- **The first-order directional terms of a conjugation-covariant analytic family are real.** -/
theorem termReal_dir {ι : Type*} {Evs : ι → RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y)
      (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁))
    (hreal : ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
      IsRealRaw u.1 → cj (Evs Y u) = Evs Y (cjU u))
    {ω : ℂ → ℂ} (hω : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (ω (t : ℂ)).im = 0)
    {R₁ Rσ r : ℝ} (hr : 0 < r) (hR₁ : 1 < R₁) :
    TermReal (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
        ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
          (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
      (fun Y x₀ w σ Θ => dirTerm (Evs Y) ω x₀ w σ Θ) := by
  intro Y xw hxw hx hw σ hσ hσim Θ hΘ hΘr
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hline : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (σ * (t : ℂ)) • xw.1 ∈ FlBall Hm δ₁ := fun t ht => by
    simpa using hxw σ hσ t (hreal1 t ht) 0 (by simp [hr.le])
  have h1 : ∀ z ∈ FlBall Hm δ₁, cj (Evs Y (Θ, z)) = Evs Y (Θ, DecEquiv.cjSite z) := fun z hz =>
    hreal Y (Θ, z) ⟨hΘ, hz⟩ hΘr
  have h2 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      DifferentiableAt ℂ (Evs Y) (Θ, (σ * (t : ℂ)) • xw.1) := fun t ht =>
    (hEv Y (Θ, (σ * (t : ℂ)) • xw.1) ⟨hΘ, hline t ht⟩).differentiableAt
  exact dirTerm_conj (Ev := Evs Y) (isOpen_flBall (N := N) Hm δ₁) (DecEquiv.cjSite (N := N))
    cjSite_add cjSite_smul h1 (Complex.conj_eq_iff_im.2 hσim)
    (funext fun p => funext fun i => Complex.conj_eq_iff_im.2 (hx p i))
    (funext fun p => funext fun i => Complex.conj_eq_iff_im.2 (hw p i))
    (fun t ht => Complex.conj_eq_iff_im.2 (hω t ht)) hline h2

end Def

end Balaban.Localization
