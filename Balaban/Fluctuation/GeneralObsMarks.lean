/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralEnergyMarksBounds
public import Balaban.Fluctuation.ClassOldTermInputM
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The old observable terms of a class member in the first-order marks of the step (part 1)

The integrand of `ℳ₀^{(k+1)}(y; g)_i` is `∂_t ℳ_k(y; ψ^{(k)} + t ψ', g)_i` with
`ℳ_k = φ_k + ∑_{j ≤ k} ℳ^{(j)}`.  For the class with zero old terms the second part vanishes; for a
class member `C` the old observable terms are added.  With the label set `𝒯M` of
`mem_classLabels_M_iff` (labels `(j, y, i, X)`), the component `(y, i)` of the old part is the sum
over the labels with site `y` and component `i`.

* `sum_Mloc_eq_sum_classLabels_M`: the sum `∑_{j ≤ k} ℳ^{(j)}(y; ψ_j, h_j, g)_i` is the sum over the
  labels with site `y` and component `i` of the label terms.
* `McompAtC_class_eq_zero_add_oldM`: `ℳ_k` of a class member is `ℳ_k` of the zero class plus that
  sum, at the composed pairs of the datum.
* `analyticAt_classLabelM_shift`, `analyticAt_fderiv_classLabelM_shift`: each label term and its
  derivative are analytic in the complex shift at a point of the chart.
* `fderiv_McompAtC_class_eq_zero_add_oldM_labels`: the derivative in the field of `ℳ_k(y)_i` is the
  derivative for the zero class plus the sum of the derivatives of the label terms.
* `deriv_McompAtC_ray_class_eq_zero_add_oldM_labels`: the same for the derivative along the ray
  `t ↦ ψ^{(k)} + t ψ'`, the integrand of `ℳ₀`.
* `norm_classLabelM_le`, `norm_fderiv_classLabelM_le`, `norm_sum_fderiv_classLabelsM_le`: the bound
  of a label term, its Cauchy bound in a direction, and the bound of the sum with the summability
  of the weights as an explicit hypothesis.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The old observable part of `ℳ_k` is the sum of the label terms with site `y` and component
`i`.** -/
theorem sum_Mloc_eq_sum_classLabels_M (m₀ : ℕ) (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (ψ h : ℕ → Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ∑ j ∈ Finset.Icc 1 k, Mloc m₀ Tm j y (ψ j) (h j) g i =
    ∑ τ ∈ (((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)).filter
      (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
      Tm.M τ.1 τ.2.1 τ.2.2.2 (ψ τ.1) (h τ.1) g τ.2.2.1 := by
  rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Mloc
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_apply]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single y (fun b _ hb => by simp [hb])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [Fintype.sum_prod_type_right]
  have hin : ∀ X : Set (CTorus d L N₁ m₁ (k + 1)), ∑ x : Fin N,
      (if (IsPolyDom m₀ (j, y, x, X).1 (j, y, x, X).2.2.2 ∧ (j, y, x, X).2.1 ∈ (j, y, x, X).2.2.2) ∧
          (j, y, x, X).2.1 = y ∧ (j, y, x, X).2.2.1 = i then
        Tm.M (j, y, x, X).1 (j, y, x, X).2.1 (j, y, x, X).2.2.2 (ψ (j, y, x, X).1)
          (h (j, y, x, X).1) g (j, y, x, X).2.2.1 else 0) =
      if IsPolyDom m₀ j X ∧ y ∈ X then Tm.M j y X (ψ j) (h j) g i else 0 := by
    intro X
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [Finset.sum_congr rfl (fun X _ => hin X)]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext X
  simp [polysAt]

open Classical in
/-- **`ℳ_k` of a class member is `ℳ_k` of the zero class plus the label sum.**  At a complex datum
`D` of the level `k`, for every site `y` and component `i`, the old part of `ℳ_k(y; D, g)_i` is the
sum over the labels `(j, y, i, X)` of `𝒯M` of `ℳ^{(j)}_i(y, X; ψ_k^{(j)}(D), h, g)`. -/
theorem McompAtC_class_eq_zero_add_oldM (C : StepClass d L N₁ m₁ k N ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) k
      (Nat.le_succ k)) N) (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1))
    (i : Fin N)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯M = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)) :
    McompAtC C.m₀ C.Tm a ν (Nat.le_succ k) D g y i =
      McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm a ν
        (Nat.le_succ k) D g y i +
      ∑ τ ∈ 𝒯M.filter (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
        C.Tm.M τ.1 τ.2.1 τ.2.2.2 (composedPairAtC a ν (Nat.le_succ k) τ.1 D).1
          (composedPairAtC a ν (Nat.le_succ k) τ.1 D).2 g τ.2.2.1 := by
  subst h𝒯
  rw [← sum_Mloc_eq_sum_classLabels_M C.m₀ C.Tm
    (fun j => (composedPairAtC a ν (Nat.le_succ k) j D).1)
    (fun j => (composedPairAtC a ν (Nat.le_succ k) j D).2) g y i]
  have h0 : (zeroClass d L N₁ m₁ k N ϱ).Tm = zeroTerms d L N₁ m₁ (k + 1) N ϱ := rfl
  have h1 : (zeroClass d L N₁ m₁ k N ϱ).m₀ = 0 := rfl
  simp only [h0, h1, McompAtC, Mloc_zero]
  simp

namespace StepSetting

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
/-- **A label term of the old observable is analytic in the complex shift** at a shift of
`shiftDomC p⁺` at which the composed pair lies in the class domain of the label's polymer (`hdom`;
the chart inclusion `hchart` of `classOldObs_analytic_bound`), for a source `‖g‖₁ < 1`. -/
theorem analyticAt_classLabelM_shift
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (hdom : Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).2) :
    AnalyticAt ℂ (fun w : S.EC =>
      C.Tm.M τ.1 τ.2.1 τ.2.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
      y₀ := by
  obtain ⟨⟨h1, h2⟩, hX, hy⟩ := hτ
  have hat := hM τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2.2 hX hy
    ((composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).1,
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).2, g) ⟨hdom, hg⟩
  have hpair := S.analyticAt_composedPairAtC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
    hy₀ τ.1
  have hmap : AnalyticAt ℂ (fun w : S.EC =>
      ((composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1,
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2, g)) y₀ :=
    (analyticAt_fst.comp hpair).prod ((analyticAt_snd.comp hpair).prod analyticAt_const)
  have hpr : AnalyticAt ℂ (fun v : Fin N → ℂ => v τ.2.2.1)
      (C.Tm.M τ.1 τ.2.1 τ.2.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).2 g) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) τ.2.2.1).analyticAt _
  exact hpr.comp_of_eq (hat.comp_of_eq hmap rfl) rfl

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The derivative of a label term in a direction is analytic in the shift** at a point of the
chart (record of analyticity of the old-observable contribution to the marks). -/
theorem analyticAt_fderiv_classLabelM_shift
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (hdom : Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + y₀))).2) (v : S.EC) :
    AnalyticAt ℂ (fun w : S.EC => fderiv ℂ (fun w' : S.EC =>
      C.Tm.M τ.1 τ.2.1 τ.2.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w'))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w'))).2 g τ.2.2.1) w v)
      y₀ :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp
    (S.analyticAt_classLabelM_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hM hg hy₀ τ
      hτ hdom).fderiv

open Classical in
include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ℳ_k` of the zero class is differentiable in the shift** at every point of the chart at which
the composed pairs lie in the class domains: it is `ℳ_k` of the class minus the label sum. -/
theorem differentiableAt_McompAtC_zero_shift
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯M = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2))
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).2)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    DifferentiableAt ℂ (fun w : S.EC =>
      McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psi0C + w)) g y i) y₀ := by
  have hA := (S.analyticAt_McompAtC_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hM hg
    hy₀ hdom y i).differentiableAt
  have hlab : DifferentiableAt ℂ (fun w : S.EC =>
      ∑ τ ∈ 𝒯M.filter (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
        C.Tm.M τ.1 τ.2.1 τ.2.2.2
          (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
      y₀ := by
    refine DifferentiableAt.fun_sum fun τ hτ => ?_
    have hτ' := (Finset.mem_filter.1 hτ).1
    rw [h𝒯] at hτ'
    obtain ⟨h1, h2, h3⟩ := (mem_classLabels_M_iff C.m₀ τ).1 hτ'
    exact (S.analyticAt_classLabelM_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hM hg
      hy₀ τ ⟨h1, h2, h3⟩ (hdom τ.1 (Finset.mem_Icc.2 h1) τ.2.2.2 h2)).differentiableAt
  refine (hA.sub hlab).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp only [Pi.sub_apply]
  rw [McompAtC_class_eq_zero_add_oldM C S.a S.ν _ g y i 𝒯M h𝒯]
  ring

open Classical in
include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The first-order observable object of a class member: the old observable terms enter as a sum
over the labels** (part 1 of the observable marks).  At a complex shift `y₀ ∈ shiftDomC p⁺` at which
the composed pairs of every polymer lie in the class domains (`hdom`), for a source `‖g‖₁ < 1`, a
site `y`, a component `i` and every direction `v`,
`D(ℳ_k(y; ·, g)_i)(y₀)[v] = D(ℳ_k^{zero}(y; ·, g)_i)(y₀)[v]
  + ∑_{τ = (j, y, i, X) ∈ 𝒯M} D(ℳ^{(j)}_i(y, X; pair_j(·), g))(y₀)[v]`. -/
theorem fderiv_McompAtC_class_eq_zero_add_oldM_labels
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯M = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2))
    {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psi0C + y₀))).2)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) (v : S.EC) :
    fderiv ℂ (fun w : S.EC =>
        McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psi0C + w)) g y i) y₀ v =
      fderiv ℂ (fun w : S.EC =>
        McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
          (Nat.le_succ k) (S.dataUC (S.psi0C + w)) g y i) y₀ v +
      ∑ τ ∈ 𝒯M.filter (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
        fderiv ℂ (fun w : S.EC =>
          C.Tm.M τ.1 τ.2.1 τ.2.2.2
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
          y₀ v := by
  have hZ := S.differentiableAt_McompAtC_zero_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁
    hD hM hg 𝒯M h𝒯 hy₀ hdom y i
  have hlab : ∀ τ ∈ 𝒯M.filter (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
      DifferentiableAt ℂ (fun w : S.EC =>
        C.Tm.M τ.1 τ.2.1 τ.2.2.2
          (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
        y₀ := by
    intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).1
    rw [h𝒯] at hτ'
    obtain ⟨h1, h2, h3⟩ := (mem_classLabels_M_iff C.m₀ τ).1 hτ'
    exact (S.analyticAt_classLabelM_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hM hg
      hy₀ τ ⟨h1, h2, h3⟩ (hdom τ.1 (Finset.mem_Icc.2 h1) τ.2.2.2 h2)).differentiableAt
  have e : (fun w : S.EC =>
        McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psi0C + w)) g y i) =
      fun w => McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
          (Nat.le_succ k) (S.dataUC (S.psi0C + w)) g y i +
        ∑ τ ∈ 𝒯M.filter (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
          C.Tm.M τ.1 τ.2.1 τ.2.2.2
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g
            τ.2.2.1 := by
    funext w
    exact McompAtC_class_eq_zero_add_oldM C S.a S.ν _ g y i 𝒯M h𝒯
  rw [e, fderiv_fun_add hZ (DifferentiableAt.fun_sum hlab), fderiv_fun_sum hlab]
  simp

end Chart

end StepSetting

/-- **The derivative along a ray is the derivative in the ray direction.**  For a function
`F` of a complex normed space that is complex-differentiable at `t • v`, the real derivative of
`r ↦ F (r • v)` at `t` is `DF(t v)[v]`. -/
theorem deriv_ray_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → ℂ}
    (v : E) (t : ℝ) (hF : DifferentiableAt ℂ F ((t : ℂ) • v)) :
    deriv (fun r : ℝ => F ((r : ℂ) • v)) t = fderiv ℂ F ((t : ℂ) • v) v := by
  have hγ : HasDerivAt (fun r : ℝ => ((r : ℂ) • v : E)) v t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).smul_const v
  have hf : HasFDerivAt F ((fderiv ℂ F ((t : ℂ) • v)).restrictScalars ℝ) ((t : ℂ) • v) :=
    hF.hasFDerivAt.restrictScalars ℝ
  exact (hf.comp_hasDerivAt t hγ).deriv


/-- **The label term of the old observable is bounded on the class domain.**  For
`κ_dec - 1 ≤ κ_P` and a source `‖g‖₁ < 1`, the component `i` of `ℳ^{(j)}(y, X; Ψ, h, g)` at a pair
in the field domain of the polymer is at most
`c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-(κ_dec - 1) d_j(X))`. -/
theorem norm_classLabelM_le {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ) (hc₉ : 0 ≤ P.c₉)
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N) (hdom : Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2.2) Ψ h) :
    ‖C.Tm.M τ.1 τ.2.1 τ.2.2.2 Ψ h g τ.2.2.1‖ ≤
      P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2.2) := by
  obtain ⟨⟨h1, h2⟩, hX, hy⟩ := hτ
  have hb := hcl.boundM τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2.2 (hm ▸ hX) hy Ψ h g hdom hg
  have key : Real.exp (-P.κ * sizeJ P.m₀ τ.1 τ.2.2.2) ≤
      Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2.2) := by
    unfold sizeJ
    rw [hm]
    refine Real.exp_le_exp.2 ?_
    have := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      C.m₀ τ.1 τ.2.2.2
    nlinarith
  have hpos : 0 ≤ P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) := by
    have : (0 : ℝ) ≤ ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  calc ‖C.Tm.M τ.1 τ.2.1 τ.2.2.2 Ψ h g τ.2.2.1‖
      ≤ vn (C.Tm.M τ.1 τ.2.1 τ.2.2.2 Ψ h g) := norm_apply_le_vn _ _
    _ ≤ P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-P.κ * sizeJ P.m₀ τ.1 τ.2.2.2) := hb.le
    _ ≤ _ := mul_le_mul_of_nonneg_left key hpos

namespace StepSetting

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

open Classical in
include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The integrand of `ℳ₀^{(k+1)}` for a class member**: the derivative of `ℳ_k(y; ψ^{(k)} + r ψ')_i`
along the ray `r ↦ r ψ'`, `ψ' = shiftUC x`, at a real `t` with `t ψ'` in the chart, is the same
derivative for the zero class plus the sum over the labels of the derivatives of the label terms in
the direction `ψ'`. -/
theorem deriv_McompAtC_ray_class_eq_zero_add_oldM_labels
    (hM : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ x X, IsPolyDom C.m₀ j X → x ∈ X →
      AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N => C.Tm.M j x X p.1 p.2.1 p.2.2)
        {p | Dom.dom j (C.Tm.gs j X) p.1 p.2.1 ∧ Def6.l1 p.2.2 < 1})
    {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯M = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2))
    (x : S.E) (t : ℝ) (ht : (t : ℂ) • S.shiftUC x ∈ S.shiftDomC pp)
    (hdom : ∀ j ∈ Finset.Icc 1 k, ∀ X, IsPolyDom C.m₀ j X →
      Dom.dom j (C.Tm.gs j X)
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + (t : ℂ) • S.shiftUC x))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j
          (S.dataUC (S.psi0C + (t : ℂ) • S.shiftUC x))).2)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    deriv (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataUC (S.psiAtC r x)) g y i) t =
      deriv (fun r : ℝ => McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i) t +
      ∑ τ ∈ 𝒯M.filter (fun τ => τ.2.1 = y ∧ τ.2.2.1 = i),
        fderiv ℂ (fun w : S.EC =>
          C.Tm.M τ.1 τ.2.1 τ.2.2.2
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
          ((t : ℂ) • S.shiftUC x) (S.shiftUC x) := by
  have hA := (S.analyticAt_McompAtC_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hM hg
    ht hdom y i).differentiableAt
  have hZ := S.differentiableAt_McompAtC_zero_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁
    hD hM hg 𝒯M h𝒯 ht hdom y i
  have h1 := deriv_ray_eq_fderiv (F := fun w : S.EC => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
    (S.dataUC (S.psi0C + w)) g y i) (S.shiftUC x) t hA
  have h2 := deriv_ray_eq_fderiv (F := fun w : S.EC =>
    McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
      (Nat.le_succ k) (S.dataUC (S.psi0C + w)) g y i) (S.shiftUC x) t hZ
  have h3 := S.fderiv_McompAtC_class_eq_zero_add_oldM_labels C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ
    hpp hδ₁ hD hM hg 𝒯M h𝒯 ht hdom y i (S.shiftUC x)
  have e1 : (fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
      (S.dataUC (S.psiAtC r x)) g y i) = fun r : ℝ => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
      (S.dataUC (S.psi0C + (r : ℂ) • S.shiftUC x)) g y i := rfl
  have e2 : (fun r : ℝ => McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i) =
      fun r : ℝ => McompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k)
        (S.dataUC (S.psi0C + (r : ℂ) • S.shiftUC x)) g y i := rfl
  rw [e1, e2, h1, h2, h3]


include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The Cauchy bound of the mark of a label of the old observable.**  Let `y₀` be a complex shift
and `r > 0` such that the closed ball of radius `r` about `y₀` lies in the chart `shiftDomC p⁺` and
the composed pair of the label's polymer lies in the class domain at every shift of the ball
(`hdom`, the chart inclusion `hchart` of `classOldObs_analytic_bound`).  For a source `‖g‖₁ < 1`
and every direction `v`,
`‖D(ℳ^{(j)}_i(y, X) ∘ pair)(y₀)[v]‖ ≤ c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-(κ_dec - 1) d_j(X)) ‖v‖ / r`. -/
theorem norm_fderiv_classLabelM_le {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hc₉ : 0 ≤ P.c₉) {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    {y₀ : S.EC} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall y₀ r ⊆ S.shiftDomC pp)
    (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1)))
    (hτ : (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (hdom : ∀ w ∈ Metric.closedBall y₀ r, Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
    (v : S.EC) :
    ‖fderiv ℂ (fun w : S.EC =>
      C.Tm.M τ.1 τ.2.1 τ.2.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
        y₀ v‖ ≤
      P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2.2) / r * ‖v‖ := by
  refine norm_fderiv_le_of_closedBall hr ?_ (fun w hw => ?_) v
  · intro w hw
    exact (S.analyticAt_classLabelM_shift C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD
      (fun j h1 h2 x X hX hx => hcl.analyticM j h1 h2 x X (hm ▸ hX) hx) hg (hball hw) τ hτ
      (hdom w hw)).differentiableAt.differentiableWithinAt
  · exact norm_classLabelM_le C hm hcl hκ hc₉ hg τ hτ _ _ (hdom w hw)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The sum of the marks of the labels of the old observable.**  Let `𝒯M'` be a finite set of
labels of the class (for the integrand of `ℳ₀(y)_i`: the labels with site `y` and component `i`),
and suppose that the weights `c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-(κ_dec - 1) d_j(X_τ))` over `𝒯M'`
add up to at most `ρM` (the summability `hρM` of the constructor).  Then
`‖∑_τ D(ℳ_τ ∘ pair)(y₀)[v]‖ ≤ ρM ‖v‖ / r`. -/
theorem norm_sum_fderiv_classLabelsM_le {P : Consts}
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hc₉ : 0 ≤ P.c₉) {g : Fld d L N₁ m₁ (k + 1) N} (hg : Def6.l1 g < 1)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯M, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    {y₀ : S.EC} {r : ℝ} (hr : 0 < r) (hball : Metric.closedBall y₀ r ⊆ S.shiftDomC pp)
    (hdom : ∀ τ ∈ 𝒯M, ∀ w ∈ Metric.closedBall y₀ r, Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2.2)
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
      (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2)
    (v : S.EC) {ρM : ℝ}
    (hρM : ∑ τ ∈ 𝒯M, P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
      Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2.2) ≤ ρM) :
    ‖∑ τ ∈ 𝒯M, fderiv ℂ (fun w : S.EC =>
      C.Tm.M τ.1 τ.2.1 τ.2.2.2
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) τ.1 (S.dataUC (S.psi0C + w))).2 g τ.2.2.1)
        y₀ v‖ ≤ ρM / r * ‖v‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun τ hτ => S.norm_fderiv_classLabelM_le C hC hMX hdm hα hsm ha₁ hc7 hR
    hsmR hβ hpp hδ₁ hD hm hcl hκ hc₉ hg hr hball τ (h𝒯 τ hτ) (hdom τ hτ) v).trans ?_
  rw [← Finset.sum_mul, ← Finset.sum_div]
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hρM hr.le) (norm_nonneg _)

end Chart

end StepSetting

end Balaban.Fluctuation
