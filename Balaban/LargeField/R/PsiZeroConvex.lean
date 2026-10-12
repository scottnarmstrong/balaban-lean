/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroAbstract
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.Gradient.Basic

public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Unique critical point of a uniformly convex function on a ball

A `C²` function on a finite-dimensional real inner product space whose Hessian is bounded below by `c > 0` on a
closed ball and whose derivative at the centre is small has exactly one critical point in the ball, the strict
minimizer there (the contraction behind Lemma III.3.3, in the form needed for the effective action).
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Metric Set

namespace Balaban.LargeField

section Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : E → ℝ} {x0 : E} {r c : ℝ}

/-- Along a segment inside the ball, the derivative of `t ↦ DF(y + t (x - y)) (x - y)`. -/
theorem hasDerivAt_dF_line (hF : ∀ x ∈ closedBall x0 r, ContDiffAt ℝ 2 F x) {x y : E}
    (hx : x ∈ closedBall x0 r) (hy : y ∈ closedBall x0 r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s : ℝ => fderiv ℝ F (y + s • (x - y)) (x - y))
      (fderiv ℝ (fderiv ℝ F) (y + t • (x - y)) (x - y) (x - y)) t := by
  have hz : y + t • (x - y) ∈ closedBall x0 r := by
    have : y + t • (x - y) = (1 - t) • y + t • x := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact (convex_closedBall x0 r) hy hx (by linarith [ht.2]) ht.1 (by ring)
  have h2 : ContDiffAt ℝ 1 (fderiv ℝ F) (y + t • (x - y)) :=
    (hF _ hz).fderiv_right (m := 1) (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (y + t • (x - y)))
      (y + t • (x - y)) := (h2.differentiableAt (by norm_num)).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) t := by
    simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
  have hc := hd.comp_hasDerivAt t hl
  have := hc.clm_apply (hasDerivAt_const t (x - y))
  simpa using this

/-- The derivative of `F` is strongly monotone on the ball if the Hessian is bounded below by `c`. -/
theorem dF_strongMono (hF : ∀ x ∈ closedBall x0 r, ContDiffAt ℝ 2 F x)
    (hlow : ∀ x ∈ closedBall x0 r, ∀ v : E, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    {x y : E} (hx : x ∈ closedBall x0 r) (hy : y ∈ closedBall x0 r) :
    c * ‖x - y‖ ^ 2 ≤ (fderiv ℝ F x - fderiv ℝ F y) (x - y) := by
  set ψ : ℝ → ℝ := fun s => fderiv ℝ F (y + s • (x - y)) (x - y) - c * ‖x - y‖ ^ 2 * s with hψ
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ
      (fderiv ℝ (fderiv ℝ F) (y + t • (x - y)) (x - y) (x - y) - c * ‖x - y‖ ^ 2) t := by
    intro t ht
    have := (hasDerivAt_dF_line hF hx hy ht).sub ((hasDerivAt_id t).const_mul (c * ‖x - y‖ ^ 2))
    exact this.congr_deriv (by simp)
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, y + t • (x - y) ∈ closedBall x0 r := by
    intro t ht
    have : y + t • (x - y) = (1 - t) • y + t • x := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact (convex_closedBall x0 r) hy hx (by linarith [ht.2]) ht.1 (by ring)
  have hmono : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hder t ⟨ht.1.le, ht.2.le⟩).deriv]
    have := hlow _ (hz t ⟨ht.1.le, ht.2.le⟩) (x - y)
    linarith
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, mul_zero, sub_zero, mul_one] at h01
  have e : y + (x - y) = x := by abel
  rw [e] at h01
  rw [sub_apply]
  linarith

/-- A critical point in the ball is a strict minimizer on the ball. -/
theorem F_strictMin (hF : ∀ x ∈ closedBall x0 r, ContDiffAt ℝ 2 F x)
    (hlow : ∀ x ∈ closedBall x0 r, ∀ v : E, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    {x y : E} (hx : x ∈ closedBall x0 r) (hy : y ∈ closedBall x0 r)
    (hcrit : fderiv ℝ F x = 0) : F x + c / 2 * ‖y - x‖ ^ 2 ≤ F y := by
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ closedBall x0 r := by
    intro t ht
    have : x + t • (y - x) = (1 - t) • x + t • y := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact (convex_closedBall x0 r) hx hy (by linarith [ht.2]) ht.1 (by ring)
  set ψ : ℝ → ℝ := fun s => F (x + s • (y - x)) - c / 2 * ‖y - x‖ ^ 2 * s ^ 2 with hψ
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt ψ
      (fderiv ℝ F (x + t • (y - x)) (y - x) - c * ‖y - x‖ ^ 2 * t) t := by
    intro t ht
    have hd : HasFDerivAt F (fderiv ℝ F (x + t • (y - x))) (x + t • (y - x)) :=
      ((hF _ (hz t ht)).differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have h1 := hd.comp_hasDerivAt t hl
    have h2 : HasDerivAt (fun s : ℝ => c / 2 * ‖y - x‖ ^ 2 * s ^ 2)
        (c / 2 * ‖y - x‖ ^ 2 * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul (c / 2 * ‖y - x‖ ^ 2))
    exact (h1.sub h2).congr_deriv (by ring)
  have hmono : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rw [(hder t ht').deriv]
    have hm := dF_strongMono hF hlow (hz t ht') hx
    rw [hcrit, sub_zero, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1] at hm
    have h2 : fderiv ℝ F (x + t • (y - x)) (t • (y - x)) = t * fderiv ℝ F (x + t • (y - x)) (y - x) := by
      simp
    rw [h2] at hm
    have h3 : t * (c * ‖y - x‖ ^ 2 * t) ≤ t * fderiv ℝ F (x + t • (y - x)) (y - x) := by
      nlinarith
    have := le_of_mul_le_mul_left h3 ht.1
    linarith
  have h01 := hmono ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, mul_zero, one_pow, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h01
  have e : x + (y - x) = y := by abel
  rw [e] at h01
  linarith

/-- **Unique critical point of a uniformly convex function on a ball.**  If `F` is `C²` near every point of the
closed ball about `x₀` of radius `r`, its Hessian is bounded below by `c > 0` there, and `‖DF(x₀)‖ ≤ ε ≤ c r / 2`,
then `F` has exactly one critical point `x` in the ball; it is the strict minimizer of `F` on the ball and
`‖x - x₀‖ ≤ ε / c`. -/
theorem exists_unique_critical_ball (hF : ∀ x ∈ closedBall x0 r, ContDiffAt ℝ 2 F x) (hc : 0 < c)
    (hr : 0 ≤ r)
    (hlow : ∀ x ∈ closedBall x0 r, ∀ v : E, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v) {ε : ℝ}
    (hres : ‖fderiv ℝ F x0‖ ≤ ε) (hε : ε ≤ c * r / 2) :
    ∃ x ∈ closedBall x0 r, fderiv ℝ F x = 0 ∧
      (∀ y ∈ closedBall x0 r, fderiv ℝ F y = 0 → y = x) ∧ ‖x - x0‖ ≤ ε / c ∧
      ∀ y ∈ closedBall x0 r, y ≠ x → F x < F y := by
  -- a uniform bound on the Hessian by compactness
  have hcont : ContinuousOn (fun x => fderiv ℝ (fderiv ℝ F) x) (closedBall x0 r) := fun x hx =>
    (((hF x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
      |>.continuousWithinAt
  have hcontn : ContinuousOn (fun x => ‖fderiv ℝ (fderiv ℝ F) x‖) (closedBall x0 r) :=
    fun x hx => ((((hF x hx).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
      (by norm_num)).continuousAt.norm).continuousWithinAt
  obtain ⟨Λ0, hΛ0'⟩ := (isCompact_closedBall x0 r).exists_bound_of_continuousOn hcontn
  have hΛ0 : ∀ x ∈ closedBall x0 r, ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ Λ0 := fun x hx => by
    have := hΛ0' x hx
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  set Λ := max Λ0 c with hΛ
  have hcΛ : c ≤ Λ := le_max_right _ _
  have hdiff : ∀ x ∈ closedBall x0 r, DifferentiableAt ℝ (fderiv ℝ F) x := fun x hx =>
    ((hF x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hlip : ∀ x ∈ closedBall x0 r, ∀ y ∈ closedBall x0 r,
      ‖gradient F x - gradient F y‖ ≤ Λ * ‖x - y‖ := by
    intro x hx y hy
    have h := (convex_closedBall x0 r).norm_image_sub_le_of_norm_fderiv_le hdiff
      (fun z hz => (hΛ0 z hz).trans (le_max_left Λ0 c)) hy hx
    have e : ‖gradient F x - gradient F y‖ = ‖fderiv ℝ F x - fderiv ℝ F y‖ := by
      unfold gradient
      rw [← map_sub]
      exact (InnerProductSpace.toDual ℝ E).symm.norm_map _
    rw [e, norm_sub_rev]
    simpa [norm_sub_rev] using h
  have hmono : ∀ x ∈ closedBall x0 r, ∀ y ∈ closedBall x0 r,
      c * ‖x - y‖ ^ 2 ≤ inner ℝ (gradient F x - gradient F y) (x - y) := by
    intro x hx y hy
    have h := dF_strongMono hF hlow hx hy
    have e : inner ℝ (gradient F x - gradient F y) (x - y) = (fderiv ℝ F x - fderiv ℝ F y) (x - y) := by
      unfold gradient
      rw [← map_sub, InnerProductSpace.toDual_symm_apply]
    rwa [e]
  have hres' : ‖gradient F x0‖ ≤ ε := by
    unfold gradient
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    exact hres
  obtain ⟨x, hx, hgx, huniq, hdist⟩ := exists_unique_zero_ball hc hcΛ hr hlip hmono hres' hε
  have hcrit : ∀ y, gradient F y = 0 ↔ fderiv ℝ F y = 0 := by
    intro y
    unfold gradient
    exact (InnerProductSpace.toDual ℝ E).symm.map_eq_zero_iff
  refine ⟨x, hx, (hcrit x).1 hgx, fun y hy hy0 => huniq y hy ((hcrit y).2 hy0), hdist, ?_⟩
  intro y hy hne
  have h := F_strictMin hF hlow hx hy ((hcrit x).1 hgx)
  have : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have : 0 < c / 2 * ‖y - x‖ ^ 2 := by positivity
  linarith

end Convex

end Balaban.LargeField
