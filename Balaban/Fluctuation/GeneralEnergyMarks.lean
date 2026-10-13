/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralClassRegularC
public import Balaban.Fluctuation.ClassOldTermInputE
public import Balaban.Fluctuation.StepOldTermSplit

/-!
# The old energy terms of a class member in the first-order marks of the step (part 1)

The integrand of the local energy term `ℰ₁^{(k+1)}(z)` is `DΦ₁(s ψ')[M_z ψ']` with
`Φ₁(ψ') = -β V^{(k)}(ψ^{(k)} + ψ') + δℰ_k(ψ')`.  For the class with zero old terms `δℰ_k = 0`, and the
integrand is the sum of the marks of the interaction.  For a class member `C` the derivative of
`δℰ_k` is added.

* `Phi1C_class_eq_zero_add`: `Φ₁^C = Φ₁^{zero} + δℰ_k^C(ψ^{(k)} + ·)` as functions.
* `fderiv_Phi1C_class_eq_zero_add_oldE`: the derivatives add, where both parts are differentiable.
* `EcompAtC_eq_sum_classLabels`: `ℰ_k` is the sum of the label terms `(j, y, X)`.
* `fderiv_dEC_eq_sum_labels`: the derivative of `δℰ_k` is the sum over the labels of the
  derivatives of the label terms at the composed pair of the shifted old spin.
* `fderiv_Phi1C_class_eq_marks_add_oldE_labels`: on the complex chart, at a shift of `shiftDomC p⁺`
  whose composed pairs lie in the class domains (the hypothesis `hdom`), the derivative of `Φ₁^C`
  in a direction `v` is the derivative of `Φ₁^{zero}` plus the label sum; with the marks of the
  zero class (`hzero`), the marks sum plus the label sum.
* `analyticAt_classLabel_shift`, `analyticAt_fderiv_classLabel_shift`: the label terms and their
  derivatives are analytic in the shift at such a point.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-- `Φ₁` of a class member is `Φ₁` of the zero class plus `δℰ_k(ψ^{(k)} + ·)`. -/
theorem Phi1C_class_eq_zero_add :
    S.Phi1C C = fun y => S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) y + S.dEC C (S.psi0C + y) := by
  funext y
  simp only [Phi1C, dEC_zeroClass, add_zero]

theorem Phi1C_zeroClass_eq :
    S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) = fun y => -(S.β : ℂ) * S.VkC (S.psi0C + y) := by
  funext y
  simp only [Phi1C, dEC_zeroClass, add_zero]

/-- **The derivative of `Φ₁` of a class member is the derivative for the zero class plus the
derivative of the old-energy increment**, wherever the interaction and the increment are
differentiable. -/
theorem fderiv_Phi1C_class_eq_zero_add_oldE (y : S.EC)
    (hV : DifferentiableAt ℂ (fun w => S.VkC (S.psi0C + w)) y)
    (hE : DifferentiableAt ℂ (fun w => S.dEC C (S.psi0C + w)) y) :
    fderiv ℂ (S.Phi1C C) y =
      fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) y +
        fderiv ℂ (fun w => S.dEC C (S.psi0C + w)) y := by
  have hz : DifferentiableAt ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) y := by
    rw [S.Phi1C_zeroClass_eq]
    exact (differentiableAt_const _).mul hV
  rw [S.Phi1C_class_eq_zero_add C]
  exact fderiv_add hz hE

end StepSetting

open Classical in
/-- **`ℰ_k` is the sum of the label terms.**  For the label set `𝒯E` of
`mem_classLabels_E_iff`, `ℰ_k(D) = ∑_{(j,y,X) ∈ 𝒯E} ℰ^{(j)}(y, X; ψ_k^{(j)}(D), h)`. -/
theorem EcompAtC_eq_sum_classLabels (C : StepClass d L N₁ m₁ k N ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) N)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)) :
    EcompAtC C.m₀ C.Tm a ν (Nat.le_succ k) D =
      ∑ τ ∈ 𝒯E, C.Tm.E τ.1 τ.2.1 τ.2.2 (composedPairAtC a ν (Nat.le_succ k) τ.1 D).1
        (composedPairAtC a ν (Nat.le_succ k) τ.1 D).2 := by
  subst h𝒯
  rw [sum_classLabels_E_eq_Edens C.m₀ C.Tm
    (fun j => (composedPairAtC a ν (Nat.le_succ k) j D).1)
    (fun j => (composedPairAtC a ν (Nat.le_succ k) j D).2)]
  rfl

namespace StepSetting

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

open Classical in
/-- **The derivative of the old-energy increment is the sum over the labels of the derivatives of
the label terms.** -/
theorem fderiv_dEC_eq_sum_labels
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    (y : S.EC)
    (hd : ∀ τ ∈ 𝒯E, DifferentiableAt ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y) :
    fderiv ℂ (fun w => S.dEC C (S.psi0C + w)) y =
      ∑ τ ∈ 𝒯E, fderiv ℂ (fun w : S.EC =>
        C.Tm.E τ.1 τ.2.1 τ.2.2
          (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y := by
  have e : (fun w => S.dEC C (S.psi0C + w)) = fun w =>
      (∑ τ ∈ 𝒯E, C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) -
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC S.psi0C) := by
    funext w
    unfold dEC
    rw [EcompAtC_eq_sum_classLabels C S.a S.ν _ 𝒯E h𝒯]
  rw [e, fderiv_sub_const]
  exact fderiv_fun_sum hd

section Chart

variable (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **A label term of the old energy is analytic in the complex shift** at a shift of
`shiftDomC p⁺` at which the composed pair lies in the class domain of the label's polymer
(`hdom`; this is the chart inclusion `hchart` of `classOldEnergy_analytic_bound`). -/
theorem analyticAt_classLabel_shift
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hdom : Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).2) :
    AnalyticAt ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ := by
  obtain ⟨⟨h1, h2⟩, hX, hy⟩ := hτ
  have hat := hE τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2 hX hy _ hdom
  exact hat.comp_of_eq
    ((S.analyticAt_composedPairAtC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hy₀
      τ.1)) rfl

open Classical in
include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The first-order marks of the step of a class member: the old energy enters as a sum over the
labels** (part 1 of the energy marks).  At a complex shift `y₀ ∈ shiftDomC p⁺` at which the
composed pairs of every polymer lie in the class domains (`hdom`), for every direction `v`,
`DΦ₁^C(y₀)[v] = DΦ₁^{zero}(y₀)[v] + ∑_{τ ∈ 𝒯E} D(ℰ^{(j_τ)}(y_τ, X_τ) ∘ pair)(y₀)[v]`,
`𝒯E` the label set of the class.  With `y₀ = s ψ'`, `v = M_z ψ'`, this is the integrand of
`E1locC`; the zero-class term is the sum of the marks of the interaction. -/
theorem fderiv_Phi1C_class_eq_zero_add_oldE_labels
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).2)
    (v : S.EC) :
    fderiv ℂ (S.Phi1C C) y₀ v =
      fderiv ℂ (S.Phi1C (zeroClass d L N₁ m₁ k N ϱ)) y₀ v +
        ∑ τ ∈ 𝒯E, fderiv ℂ (fun w : S.EC =>
          C.Tm.E τ.1 τ.2.1 τ.2.2
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ v := by
  have hV := (S.analyticAt_VkC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    hy₀).differentiableAt
  have hEd := (S.analyticAt_dEC_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hE hy₀
    hdom).differentiableAt
  have hlab : ∀ τ ∈ 𝒯E, DifferentiableAt ℂ (fun w : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2) y₀ := by
    intro τ hτ
    subst h𝒯
    obtain ⟨hτ1, hτ2, hτ3, hτ4⟩ := (mem_classLabels_E_iff C.m₀ τ).1 hτ
    exact (S.analyticAt_classLabel_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hE
      hy₀ τ ⟨hτ1, hτ3, hτ4⟩ (hdom τ.1 (Finset.mem_Icc.2 hτ1) τ.2.2 hτ3)).differentiableAt
  rw [S.fderiv_Phi1C_class_eq_zero_add_oldE C y₀ hV hEd,
    S.fderiv_dEC_eq_sum_labels C 𝒯E h𝒯 y₀ hlab]
  simp

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The derivative of a label term in a direction is analytic in the shift** at a point of the
chart (record of analyticity of the old-energy contribution to the marks). -/
theorem analyticAt_fderiv_classLabel_shift
    (hE : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ y X, IsPolyDom C.m₀ j X → y ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        C.Tm.E j y X p.1 p.2) {p | Dom.dom j (C.Tm.gs j X) p.1 p.2})
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hdom : Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).2) (v : S.EC) :
    AnalyticAt ℂ (fun w : S.EC => fderiv ℂ (fun w' : S.EC =>
      C.Tm.E τ.1 τ.2.1 τ.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w'))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w'))).2) w v) y₀ :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp
    (S.analyticAt_classLabel_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hE hy₀ τ
      hτ hdom).fderiv

end Chart

end StepSetting

end Balaban.Fluctuation
