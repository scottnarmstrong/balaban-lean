/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Composition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composition weights are admissible

For `L ≥ 3` and `a₁ ∈ [9/16, 2]` the weights `compWeight L a₁ r = a₁ (1 - L⁻²) / (1 - L⁻²ʳ)` lie
in `[1/2, 2]` for every `r ≥ 1`, i.e. `IsAdmissibleWeights k (compWeight L a₁)` for every `k`.
The upper bound is `a_r ≤ a₁` (the denominator is at least `1 - L⁻²`), the lower bound is
`a_r ≥ a₁ (1 - L⁻²) ≥ (9/16)(8/9) = 1/2`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale

theorem compWeight_mem_Icc {L : ℕ} (hL : 3 ≤ L) {a₁ : ℝ} (h1 : 9 / 16 ≤ a₁) (h2 : a₁ ≤ 2)
    {r : ℕ} (hr : 1 ≤ r) : compWeight L a₁ r ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  set u : ℝ := (((L : ℝ) ^ 2)⁻¹) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 / 9 := by
    rw [hu, inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hL2
  have hLr : (L : ℝ) ^ 2 ≤ ((L : ℝ) ^ r) ^ 2 := by
    have : (L : ℝ) ≤ (L : ℝ) ^ r := by
      calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (L : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr
    nlinarith
  set v : ℝ := (((((L : ℝ) ^ r) ^ 2)⁻¹)) with hv
  have hv0 : 0 < v := by positivity
  have hvu : v ≤ u := by
    rw [hv, hu]
    exact inv_anti₀ (by positivity) hLr
  have hden : 0 < 1 - v := by linarith
  have hnum : 0 < a₁ * (1 - u) := by
    apply mul_pos <;> linarith
  unfold compWeight
  rw [← hu, ← hv]
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hden]
    nlinarith

/-- The weights `compWeight L a₁` are admissible for `L ≥ 3`, `a₁ ∈ [9/16, 2]`. -/
theorem isAdmissibleWeights_compWeight {L : ℕ} (hL : 3 ≤ L) {a₁ : ℝ} (h1 : 9 / 16 ≤ a₁)
    (h2 : a₁ ≤ 2) (k : ℕ) : IsAdmissibleWeights k (compWeight L a₁) :=
  fun _ hj _ => compWeight_mem_Icc hL h1 h2 hj

end Balaban.Background
