/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystem
public import Balaban.Fluctuation.OldTermClassDomain
public import Balaban.Fluctuation.LocalClassDensityIrrelChainX

/-!
# The fields of the inherited terms from the class (route R-LOC, L5; ruling R13)

The final theorem of the new level on the local generating sets (`localFamily_castLocal_of`) takes
the analyticity `hEan`, the bound `hEbd` and the spin covariance `hEr` of the old terms `Eτ` on the
charts of their generating sets.  When the old terms are the irrelevant terms of the class composed
on the generating sets of the class (`OldTermsAreIrrel`), these follow from the clauses of the class
on its term domain, once the chart lies in the term domain (the inclusion of the class domain,
ruling R2) and the bound is given on the term domain (the open input A4-1b (ii), P1 (3.128)).

* `rotRaw_mem_xiCRaw`: the charts `XiCRaw` are invariant under the real rotations;
* `irrelTorus_fields_of_class`: analyticity and spin covariance of the irrelevant term of a label
  on any rotation-invariant set of its term domain (with `Ψ(y)·Ψ(y)` in the slit plane);
* `irrelTorus_bound_of_class`: the bound of the irrelevant term on such a set, in the size of a
  cover `XL ⊇ X` with `d(XL) ≤ d(X) + c`, from its bound on the term domain.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Matrix

section Rot

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The charts `Ξ^c_n(𝔹; σ, ε)` are invariant under the real rotations** (any level `n`). -/
theorem rotRaw_mem_xiCRaw {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ}
    {n : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {r : RawData d L (N₁ * L ^ m₁) K N}
    (hr : r ∈ XiCRaw G a ν n σ ε) : rotRaw (cmat Q) r ∈ XiCRaw G a ν n σ ε := by
  obtain ⟨D, hD, rfl⟩ := hr
  exact ⟨D.rot (cmat Q), xiCData_rot hQ hD, (rawOf_rot _ D).symm⟩

end Rot

section Fields

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Analyticity and spin covariance of the irrelevant term of a label of the class** on any set
`𝒮` of raw data in its term domain `Dom.dom j (Tm.gs j X)` with `Ψ(y)·Ψ(y)` in the slit plane
(`irrelTorus_analyticOnNhd`, `irrelTorus_rot`), scaled by `β⁻¹`. -/
theorem irrelTorus_fields_of_class {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P Dom Tm) (m₀ : ℕ) (i₀ i₁ : Fin N)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hdom : ∀ r ∈ 𝒮, Dom.dom j (Tm.gs j X) r.1 r.2 ∧ dot (r.1 y) (r.1 y) ∈ Complex.slitPlane)
    (β : ℝ) :
    AnalyticOnNhd ℂ (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        (β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2) 𝒮 ∧
      ∀ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 → ∀ r ∈ 𝒮, rotRaw (cmat Q) r ∈ 𝒮 →
        (β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X (rotRaw (cmat Q) r).1 (rotRaw (cmat Q) r).2 =
          (β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2 := by
  refine ⟨fun r hr => ?_, fun Q hQ r hr hr' => ?_⟩
  · exact analyticAt_const.mul
      (irrelTorus_analyticOnNhd hcl m₀ i₀ i₁ hj1 hjk hX hy r (hdom r hr))
  · congr 1
    exact irrelTorus_rot hcl m₀ i₀ i₁ hj1 hjk hX hy
      ⟨(isRealOrth_ofReal hQ).1, (isRealOrth_ofReal hQ).2⟩ (hdom r hr).1 (hdom _ hr').1

/-- **The bound of the irrelevant term of a label on a set of its term domain**, in the size of a
cover `XL` with `d(XL) ≤ d(X) + c`: from the bound `B e^{-(κ_dec - 1) d(X)}` on the term domain
(P1 (3.128), the open input A4-1b (ii)), `‖β⁻¹ ℰ_irrel‖ ≤ |β|⁻¹ B e^{(κ_dec - 1) c}
e^{-(κ_dec - 1) d(XL)}`. -/
theorem irrelTorus_bound_of_class {m₀ : ℕ} {Tm : Terms d L N₁ m₁ (k + 1) N ϱ}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} {i₀ i₁ : Fin N} {j : ℕ}
    {y : CTorus d L N₁ m₁ (k + 1)} {X XL : Set (CTorus d L N₁ m₁ (k + 1))} {B κdec c : ℝ}
    (hB0 : 0 ≤ B) (hκ : 1 ≤ κdec)
    (hle : treeLenCovOne m₀ j XL ≤ treeLenCovOne m₀ j X + c)
    (hB : ∀ Ψ h : Fld d L N₁ m₁ (k + 1) N, Dom.dom j (Tm.gs j X) Ψ h →
      dot (Ψ y) (Ψ y) ∈ Complex.slitPlane →
      ‖irrelTorus m₀ Tm i₀ i₁ j y X Ψ h‖ ≤ B * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {𝒮 : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hdom : ∀ r ∈ 𝒮, Dom.dom j (Tm.gs j X) r.1 r.2 ∧ dot (r.1 y) (r.1 y) ∈ Complex.slitPlane)
    (β : ℝ) :
    ∀ r ∈ 𝒮, ‖(β : ℂ)⁻¹ * irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖ ≤
      |β|⁻¹ * B * Real.exp ((κdec - 1) * c) * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j XL) := by
  intro r hr
  have h := irrel_bound_transfer hB0 hκ hle (hB r.1 r.2 (hdom r hr).1 (hdom r hr).2)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hb : 0 ≤ |β|⁻¹ := inv_nonneg.2 (abs_nonneg β)
  calc |β|⁻¹ * ‖irrelTorus m₀ Tm i₀ i₁ j y X r.1 r.2‖
      ≤ |β|⁻¹ * (B * Real.exp ((κdec - 1) * c) * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j XL)) :=
        mul_le_mul_of_nonneg_left h hb
    _ = _ := by ring

end Fields

end Balaban.Inhabited
