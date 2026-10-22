/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteLogDet
public import Balaban.Green.FinalLogDetLocal

/-!
# The determinant of `1 + D` as the exponential of a trace series

For a complex matrix `D` whose row sums are at most `q < 1`, the series
`∑_{n ≥ 1} (-1)^{n+1} tr(D^n)/n` converges and
`det (1 + D) = exp (∑_{n ≥ 1} (-1)^{n+1} tr(D^n)/n)`
(`det_one_add_eq_exp_tsum_trace`). This is the landed
`Balaban.Green.det_one_sub_eq_exp_tsum_trace` applied to `K = -D`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`det (1 + D) = exp (∑_{n ≥ 1} (-1)^{n+1} tr(D^n)/n)`** when the row sums of `D` are at
most `q < 1`. -/
theorem det_one_add_eq_exp_tsum_trace (D : Matrix ι ι ℂ) {q : ℝ} (hq1 : q < 1)
    (hD : ∀ x, ∑ y, ‖D x y‖ ≤ q) :
    Summable (fun n : ℕ => (-1) ^ n * (D ^ (n + 1)).trace / ((n : ℂ) + 1)) ∧
    (1 + D).det = Complex.exp (∑' n : ℕ, (-1) ^ n * (D ^ (n + 1)).trace / ((n : ℂ) + 1)) := by
  obtain ⟨hs, he⟩ := det_one_sub_eq_exp_tsum_trace (-D) hq1 (by simpa using hD)
  have key : ∀ n : ℕ, ((-D) ^ (n + 1)).trace / ((n : ℂ) + 1)
      = -((-1) ^ n * (D ^ (n + 1)).trace / ((n : ℂ) + 1)) := by
    intro n
    rw [show (-D) ^ (n + 1) = ((-1 : ℂ) ^ (n + 1)) • D ^ (n + 1) by
      rw [← neg_one_smul ℂ D, smul_pow], Matrix.trace_smul]
    have : (-1 : ℂ) ^ (n + 1) = -(-1) ^ n := by rw [pow_succ]; ring
    rw [this]; simp only [smul_eq_mul]; ring
  simp only [key] at hs he
  refine ⟨hs.of_neg, ?_⟩
  rw [sub_neg_eq_add] at he
  rw [tsum_neg, neg_neg] at he
  exact he

end Balaban.LargeField.Base
