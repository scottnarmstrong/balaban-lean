/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The block-index condition of the collar chain at general `d` and `L`

The condition `(5 L + 13) c₁ + r₀ L ≤ (L - 2) L^{m₀+1}` of `bgFlSetting_castLocalB`, with
`c₁ = L⁴`, for the collars `r₀ ≤ R`.

* `index_condition_collar_of_le`: monotone in `r₀`; the condition at `R` gives it at every
  `r₀ ≤ R`.
* `index_condition_collar_G`: the source collar `r₀ ≤ 4 d L³ + 4 d L` (it contains
  `4 d L³ + L`) and the cover index `m₀` with `5 L + 8 d + 13 ≤ L^j`, `j + 3 ≤ m₀`.  At
  `d = L = 3`: `52 ≤ 3⁴`, `m₀ ≥ 7`; the numerals `324 = 4 d L³`, `327 = 4 d L³ + L`, `1431`
  are the instances of `4 d L³`, `4 d L³ + L` and of `R` with `(5·3+13)·81 + 3 R = 3⁸`.
-/

@[expose] public section

namespace Balaban.Inhabited

/-- The block-index condition for `r₀ ≤ R` from the condition at `R`. -/
theorem index_condition_collar_of_le {L m₀ : ℕ} {r₀ R : ℝ} (hr : r₀ ≤ R)
    (h : (((5 * L + 13) * L ^ 4 : ℕ) : ℝ) + R * (L : ℝ) ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    (((5 * L + 13) * L ^ 4 : ℕ) : ℝ) + r₀ * (L : ℝ) ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1) := by
  have : r₀ * (L : ℝ) ≤ R * (L : ℝ) := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)
  linarith

/-- **The block-index condition for the source collar** `r₀ ≤ 4 d L³ + 4 d L` and cover index
`m₀ ≥ j + 3` with `5 L + 8 d + 13 ≤ L^j`. -/
theorem index_condition_collar_G {d L m₀ j : ℕ} (hL : 3 ≤ L) {r₀ : ℝ}
    (hr : r₀ ≤ 4 * (d : ℝ) * (L : ℝ) ^ 3 + 4 * d * L) (hj : 5 * L + 8 * d + 13 ≤ L ^ j)
    (hm : j + 3 ≤ m₀) :
    (((5 * L + 13) * L ^ 4 : ℕ) : ℝ) + r₀ * (L : ℝ) ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1) := by
  have hL1 : (1 : ℝ) ≤ ((L - 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ L - 2)
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hjR : ((5 * L + 8 * d + 13 : ℕ) : ℝ) ≤ (L : ℝ) ^ j := by exact_mod_cast hj
  have hpow : (L : ℝ) ^ (j + 4) ≤ (L : ℝ) ^ (m₀ + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hL4 : (L : ℝ) ^ 4 = (L : ℝ) ^ 3 * L := by ring
  have hLL : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hr' : r₀ * (L : ℝ) ≤ 4 * d * (L : ℝ) ^ 4 + 4 * d * (L : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    nlinarith
  have hsum : (((5 * L + 13) * L ^ 4 : ℕ) : ℝ) + r₀ * (L : ℝ) ≤
      ((5 * L + 8 * d + 13 : ℕ) : ℝ) * (L : ℝ) ^ 4 := by
    push_cast
    have : 4 * (d : ℝ) * (L : ℝ) ^ 2 ≤ 4 * d * (L : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hLL (by positivity)
    nlinarith
  have h5 : ((5 * L + 8 * d + 13 : ℕ) : ℝ) * (L : ℝ) ^ 4 ≤ (L : ℝ) ^ (j + 4) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right hjR (by positivity)
  have hP : (0 : ℝ) ≤ (L : ℝ) ^ (m₀ + 1) := by positivity
  nlinarith

end Balaban.Inhabited
