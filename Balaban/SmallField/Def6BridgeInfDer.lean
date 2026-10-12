/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeInfLift

/-!
# The bridge Def-6 to I-6: differentiation under the sum over the polymers

For a term family with the analytic premises `PremisesCore` the sum over the polymers of the terms
along affine maps `z ↦ refPt + A_X (z - z₀)` is differentiable and its derivative is the sum of the
derivatives (`hasFDerivAt_tsum_term`), with the Cauchy bound `norm_fderiv_comp_le`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Metric Set

variable {d N : ℕ}

section Aux

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
  {Dom : Set ((Site d → Spin N) × Spin N)}

theorem term_bound_le_wt (hP : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hE0 : 0 ≤ E₀)
    (X : T.polys) :
    E₀ * Real.exp (-κ * T.dist X.1) ≤ E₀ * wt κ X.1 (T.dist X.1) := by
  have := wt_ge (κ := κ) X.1 (hP.dist_nonneg X.1 X.2)
    (Finset.card_pos.mpr ⟨0, hP.zero_mem X.1 X.2⟩) 0 0 (by norm_num) (by norm_num)
  simp only [pow_zero, one_mul] at this
  exact mul_le_mul_of_nonneg_left this hE0

/-- The Cauchy bound of the derivative of a term along a linear map, at a point of the ball of
radius `ρ / 2` around the reference point. -/
theorem norm_fderiv_comp_le (hP : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hρ : 0 < ρ)
    (hE0 : 0 ≤ E₀) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (X : T.polys)
    (Aop : E →L[ℂ] Cfg d N X.1) {a : ℝ} (ha : ‖Aop‖ ≤ a)
    {c : Cfg d N X.1} (hc : c ∈ ball (refPt i₀ ν X.1) (ρ / 2)) :
    ‖(fderiv ℂ (T.term X.1) c).comp Aop‖ ≤ (2 * a * E₀ / ρ) * wt κ X.1 (T.dist X.1) := by
  have hsub : ball c (ρ / 2) ⊆ ball (refPt i₀ ν X.1) ρ := by
    intro y hy
    rw [mem_ball] at hc hy ⊢
    calc dist y (refPt i₀ ν X.1) ≤ dist y c + dist c (refPt i₀ ν X.1) := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hy hc
      _ = ρ := by ring
  have hu0 : 0 ≤ (2 * a * E₀ / ρ) * wt κ X.1 (T.dist X.1) := by
    have : 0 ≤ wt κ X.1 (T.dist X.1) := by unfold wt; positivity
    have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hu0 fun v => ?_
  have hana : AnalyticOnNhd ℂ (T.term X.1) (ball c (ρ / 2)) :=
    (hP.analytic X.1 X.2).mono (hsub.trans (ball_subset_tube i₀ ν ρ X.1))
  have hbd : ∀ y ∈ ball c (ρ / 2), ‖T.term X.1 y‖ ≤ E₀ * Real.exp (-κ * T.dist X.1) :=
    fun y hy => hP.bdd_tube X.1 X.2 y (ball_subset_tube i₀ ν ρ X.1 (hsub hy))
  have h1 := norm_fderiv_apply_le (by linarith : (0 : ℝ) < ρ / 2) hana hbd (Aop v)
  simp only [ContinuousLinearMap.comp_apply]
  refine h1.trans ?_
  have hAv : ‖Aop v‖ ≤ a * ‖v‖ := (Aop.le_opNorm v).trans
    (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hM0 : 0 ≤ E₀ * Real.exp (-κ * T.dist X.1) := by positivity
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  calc E₀ * Real.exp (-κ * T.dist X.1) * ‖Aop v‖ / (ρ / 2)
      ≤ E₀ * Real.exp (-κ * T.dist X.1) * (a * ‖v‖) / (ρ / 2) := by
        gcongr
    _ = (2 * a / ρ) * (E₀ * Real.exp (-κ * T.dist X.1)) * ‖v‖ := by field_simp
    _ ≤ (2 * a / ρ) * (E₀ * wt κ X.1 (T.dist X.1)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (term_bound_le_wt hP hE0 X)
          (by positivity)) (norm_nonneg _)
    _ = (2 * a * E₀ / ρ) * wt κ X.1 (T.dist X.1) * ‖v‖ := by ring

end Aux

/-- The derivatives along the linear maps are summable over the polymers. -/
theorem summable_fderiv_comp {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Aop : ∀ X : T.polys, E →L[ℂ] Cfg d N X.1) {a : ℝ} (ha : ∀ X, ‖Aop X‖ ≤ a) :
    Summable fun X : T.polys => (fderiv ℂ (T.term X.1) (refPt i₀ ν X.1)).comp (Aop X) :=
  Summable.of_norm_bounded ((hP.count_summable).mul_left (2 * a * E₀ / ρ)) fun X =>
    norm_fderiv_comp_le hP hρ hE0 X (Aop X) (ha X) (mem_ball_self (by linarith))

/-- **Differentiation under the sum over the polymers**: for a family with the analytic premises
(`PremisesCore`), the sum over the polymers of the terms along affine maps
`z ↦ refPt + A_X (z - z₀)` with uniformly bounded linear parts is differentiable at `z₀`, and the
derivative is the sum of the derivatives. -/
theorem hasFDerivAt_tsum_term {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ}
    {Dom : Set ((Site d → Spin N) × Spin N)} (hP : PremisesCore T i₀ i₁ ν ρ E₀ κ A K₀ Dom)
    (hρ : 0 < ρ) (hE0 : 0 ≤ E₀) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Aop : ∀ X : T.polys, E →L[ℂ] Cfg d N X.1) {a : ℝ} (ha0 : 0 < a) (ha : ∀ X, ‖Aop X‖ ≤ a)
    (z₀ : E) :
    HasFDerivAt (fun z : E => ∑' X : T.polys, T.term X.1 (refPt i₀ ν X.1 + Aop X (z - z₀)))
      (∑' X : T.polys, (fderiv ℂ (T.term X.1) (refPt i₀ ν X.1)).comp (Aop X)) z₀ := by
  have hr0 : 0 < ρ / (2 * a) := by positivity
  set r : ℝ := ρ / (2 * a) with hr
  have hsum : Summable fun X : T.polys => wt κ X.1 (T.dist X.1) := hP.count_summable
  set u : T.polys → ℝ := fun X => (2 * a * E₀ / ρ) * wt κ X.1 (T.dist X.1) with hu
  have hus : Summable u := hsum.mul_left _
  have hMb : ∀ X : T.polys, ∀ y ∈ ball (refPt i₀ ν X.1) ρ,
      ‖T.term X.1 y‖ ≤ E₀ * Real.exp (-κ * T.dist X.1) := fun X y hy =>
    hP.bdd_tube X.1 X.2 y (ball_subset_tube i₀ ν ρ X.1 hy)
  have hmem : ∀ (X : T.polys) (z : E), z ∈ ball z₀ r →
      refPt i₀ ν X.1 + Aop X (z - z₀) ∈ ball (refPt i₀ ν X.1) (ρ / 2) := by
    intro X z hz
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    calc ‖Aop X (z - z₀)‖ ≤ ‖Aop X‖ * ‖z - z₀‖ := (Aop X).le_opNorm _
      _ ≤ a * ‖z - z₀‖ := mul_le_mul_of_nonneg_right (ha X) (norm_nonneg _)
      _ < a * r := mul_lt_mul_of_pos_left hz ha0
      _ = ρ / 2 := by rw [hr]; field_simp
  have hf : ∀ (X : T.polys) (z : E), z ∈ ball z₀ r →
      HasFDerivAt (fun z : E => T.term X.1 (refPt i₀ ν X.1 + Aop X (z - z₀)))
        ((fderiv ℂ (T.term X.1) (refPt i₀ ν X.1 + Aop X (z - z₀))).comp (Aop X)) z := by
    intro X z hz
    have hc := hmem X z hz
    have hdiff : DifferentiableAt ℂ (T.term X.1) (refPt i₀ ν X.1 + Aop X (z - z₀)) :=
      (hP.analytic X.1 X.2 _
        (ball_subset_tube i₀ ν ρ X.1 (ball_subset_ball (by linarith) hc))).differentiableAt
    have h1 : HasFDerivAt (fun z : E => z - z₀) (ContinuousLinearMap.id ℂ E) z :=
      (hasFDerivAt_id z).sub_const z₀
    have h2 := (Aop X).hasFDerivAt.comp z h1
    have h3 : HasFDerivAt (fun z : E => refPt i₀ ν X.1 + Aop X (z - z₀)) (Aop X) z := by
      simpa using h2.const_add (refPt i₀ ν X.1)
    exact hdiff.hasFDerivAt.comp z h3
  have hf' : ∀ (X : T.polys) (z : E), z ∈ ball z₀ r →
      ‖(fderiv ℂ (T.term X.1) (refPt i₀ ν X.1 + Aop X (z - z₀))).comp (Aop X)‖ ≤ u X :=
    fun X z hz => norm_fderiv_comp_le hP hρ hE0 X (Aop X) (ha X) (hmem X z hz)
  have hf0 : Summable fun X : T.polys => T.term X.1 (refPt i₀ ν X.1 + Aop X (z₀ - z₀)) := by
    simp only [sub_self, map_zero, add_zero]
    refine Summable.of_norm_bounded (hsum.mul_left E₀) fun X => ?_
    exact (hMb X _ (mem_ball_self hρ)).trans (term_bound_le_wt hP hE0 X)
  have := hasFDerivAt_tsum_of_isPreconnected (x₀ := z₀) (x := z₀) hus isOpen_ball
    (convex_ball z₀ r).isPreconnected hf hf' (mem_ball_self hr0) hf0 (mem_ball_self hr0)
  simpa using this

end Balaban.SmallField.Def6
