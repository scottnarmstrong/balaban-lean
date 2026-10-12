/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroConvex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-sided Taylor bound at a critical point from two-sided Hessian bounds (Lemma III.8.2, the expansion (3.3))

If a `C²` function `F` has a critical point `x₀`, its Hessian lies in `[c, C]` (as a form, `c‖v‖² ≤ D²F(v,v) ≤ C‖v‖²`)
at every point of a set `S` that is star-shaped about `x₀`, then for `y ∈ S`:
`F(x₀) + (c/2)‖y - x₀‖² ≤ F(y) ≤ F(x₀) + (C/2)‖y - x₀‖²`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Set

namespace Balaban.LargeField

section Taylor

/-- One-dimensional Taylor lower bound: `φ'(0) = 0` and `φ'' ≥ m` on `[0,1]` give `φ(1) ≥ φ(0) + m/2`. -/
theorem oneD_lower {φ φ1 φ2 : ℝ → ℝ} {m : ℝ} (h1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (h2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s) (h0 : φ1 0 = 0)
    (hm : ∀ s ∈ Icc (0 : ℝ) 1, m ≤ φ2 s) : φ 0 + m / 2 ≤ φ 1 := by
  have hA : MonotoneOn (fun s => φ1 s - m * s) (Icc 0 1) := by
    have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => φ1 s - m * s) (φ2 t - m) t := fun t ht =>
      ((h2 t ht).fun_sub ((hasDerivAt_id t).const_mul m)).congr_deriv (by simp)
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rw [(hd t ht').deriv]
    linarith [hm t ht']
  have hB : MonotoneOn (fun s => φ s - m / 2 * s ^ 2) (Icc 0 1) := by
    have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => φ s - m / 2 * s ^ 2) (φ1 t - m * t) t :=
      fun t ht => by
        have := (h1 t ht).sub ((hasDerivAt_pow 2 t).const_mul (m / 2))
        refine this.congr_deriv ?_
        simp; ring
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rw [(hd t ht').deriv]
    have := hA ⟨le_rfl, zero_le_one⟩ ht' ht.1.le
    simp only [h0, mul_zero, sub_zero] at this
    linarith
  have := hB ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp at this
  linarith

/-- One-dimensional Taylor upper bound. -/
theorem oneD_upper {φ φ1 φ2 : ℝ → ℝ} {M : ℝ} (h1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ1 s) s)
    (h2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s) (h0 : φ1 0 = 0)
    (hM : ∀ s ∈ Icc (0 : ℝ) 1, φ2 s ≤ M) : φ 1 ≤ φ 0 + M / 2 := by
  have := oneD_lower (φ := fun s => -φ s) (φ1 := fun s => -φ1 s) (φ2 := fun s => -φ2 s) (m := -M)
    (fun s hs => (h1 s hs).neg) (fun s hs => (h2 s hs).neg) (by simp [h0]) (fun s hs => by linarith [hM s hs])
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : E → ℝ} {x0 : E} {c C : ℝ}

/-- **Two-sided Taylor bound** on a set star-shaped about the critical point. -/
theorem taylor_two_sided {S : Set E} (hS : ∀ y ∈ S, ∀ s ∈ Icc (0 : ℝ) 1, x0 + s • (y - x0) ∈ S)
    (hF : ∀ x ∈ S, ContDiffAt ℝ 2 F x) (hcrit : fderiv ℝ F x0 = 0)
    (hlow : ∀ x ∈ S, ∀ v : E, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) x v v)
    (hup : ∀ x ∈ S, ∀ v : E, fderiv ℝ (fderiv ℝ F) x v v ≤ C * ‖v‖ ^ 2) {y : E} (hy : y ∈ S) :
    F x0 + c / 2 * ‖y - x0‖ ^ 2 ≤ F y ∧ F y ≤ F x0 + C / 2 * ‖y - x0‖ ^ 2 := by
  set v := y - x0 with hv
  have hl : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x0 + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x0
  have hx : ∀ s ∈ Icc (0 : ℝ) 1, x0 + s • v ∈ S := fun s hs => hS y hy s hs
  have h1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => F (x0 + s • v))
      (fderiv ℝ F (x0 + s • v) v) s := fun s hs =>
    (((hF _ (hx s hs)).differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt s (hl s)
  have h2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => fderiv ℝ F (x0 + s • v) v)
      (fderiv ℝ (fderiv ℝ F) (x0 + s • v) v v) s := fun s hs => by
    have h2' : ContDiffAt ℝ 1 (fderiv ℝ F) (x0 + s • v) := (hF _ (hx s hs)).fderiv_right (m := 1) (by norm_num)
    have hd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (x0 + s • v)) (x0 + s • v) :=
      (h2'.differentiableAt (by norm_num)).hasFDerivAt
    have hc := hd.comp_hasDerivAt s (hl s)
    have := hc.clm_apply (hasDerivAt_const s v)
    simpa using this
  have h0 : fderiv ℝ F (x0 + (0 : ℝ) • v) v = 0 := by simp [hcrit]
  have hnorm : ∀ s ∈ Icc (0 : ℝ) 1, True := fun _ _ => trivial
  constructor
  · have := oneD_lower (m := c * ‖v‖ ^ 2) h1 h2 h0 (fun s hs => hlow _ (hx s hs) v)
    simp only [zero_smul, add_zero, one_smul] at this
    have e : x0 + v = y := by rw [hv]; abel
    rw [e] at this
    linarith
  · have := oneD_upper (M := C * ‖v‖ ^ 2) h1 h2 h0 (fun s hs => hup _ (hx s hs) v)
    simp only [zero_smul, add_zero, one_smul] at this
    have e : x0 + v = y := by rw [hv]; abel
    rw [e] at this
    linarith

end Taylor

end Balaban.LargeField
