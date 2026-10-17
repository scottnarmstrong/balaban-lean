/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomDefect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exponential payment for a large polymer

When the scaled diameter crosses the tube comparison threshold, one power of exponential
decay pays for the possible difference of the class term and its tube extension.
-/

@[expose] public section

namespace Balaban.SmallField

/-- The numerical large-polymer estimate behind the tube discrepancy bound. Here `ρ` is
the reciprocal of the comparison threshold, including its fixed geometric constants. -/
theorem discrepancy_tail_le {κ t ρ M : ℝ} (ht : 0 ≤ t) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hlarge : 1 ≤ ρ * (1 + t)) :
    2 * M * Real.exp (-κ * t) ≤
      12 * Real.exp 1 * M * ρ ^ 3 * Real.exp (-(κ - 1) * t) := by
  have hpow : (1 + t) ^ 3 ≤ 6 * Real.exp (1 + t) := by
    have h := Real.pow_div_factorial_le_exp (1 + t) (by linarith) 3
    norm_num at h
    nlinarith
  have hpow2 : 1 ≤ ρ ^ 3 * (1 + t) ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by ring
      _ ≤ (ρ * (1 + t)) ^ 3 := pow_le_pow_left₀ (by positivity) hlarge 3
      _ = ρ ^ 3 * (1 + t) ^ 3 := mul_pow ..
  have hexp : Real.exp (-κ * t) = Real.exp (-(κ - 1) * t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    2 * M * Real.exp (-κ * t)
        = 2 * M * Real.exp (-(κ - 1) * t) * Real.exp (-t) := by rw [hexp]; ring
    _ ≤ 2 * M * Real.exp (-(κ - 1) * t) *
          (ρ ^ 3 * (1 + t) ^ 3 * Real.exp (-t)) := by
      have h := mul_le_mul_of_nonneg_right hpow2 (Real.exp_pos (-t)).le
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * M * Real.exp (-(κ - 1) * t)))
    _ ≤ 2 * M * Real.exp (-(κ - 1) * t) *
          (ρ ^ 3 * (6 * Real.exp (1 + t)) * Real.exp (-t)) := by
      gcongr
    _ = 12 * Real.exp 1 * M * ρ ^ 3 * Real.exp (-(κ - 1) * t) := by
      have he : Real.exp (1 + t) * Real.exp (-t) = Real.exp 1 := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 12 * M * ρ ^ 3 * Real.exp (-(κ - 1) * t) *
              (Real.exp (1 + t) * Real.exp (-t)) := by ring
        _ = _ := by rw [he]; ring

end Balaban.SmallField
