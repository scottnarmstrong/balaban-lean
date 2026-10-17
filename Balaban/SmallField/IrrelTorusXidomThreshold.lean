/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSmallSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The small versus large polymer threshold
-/

@[expose] public section

namespace Balaban.SmallField

/-- Below the large-polymer threshold, the path length fits inside the chart radius. -/
theorem path_fits_of_not_large {q A t v ρ r : ℝ}
    (hA : 0 ≤ A) (hv : 0 ≤ v) (hρ : 0 < ρ)
    (hbase : q + A * v / ρ ≤ r)
    (hsmall : ¬ 1 ≤ ρ * (1 + t)) :
    q + A * (1 + t) * v ≤ r := by
  have hpath : A * (1 + t) * v ≤ A * v / ρ := by
    apply (le_div_iff₀ hρ).2
    have hAv : 0 ≤ A * v := mul_nonneg hA hv
    nlinarith [mul_nonneg hAv (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hsmall)))]
  linarith

/-- The cubic large-polymer payment is bounded by the anisotropic irrelevance factor. -/
theorem cubic_threshold_le_aniso {C σ u α : ℝ}
    (hC : 0 ≤ C) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hα : 0 ≤ α) (hα1 : α < 1) :
    (C * σ * u) ^ 3 ≤ C ^ 3 * σ ^ (3 - α) * u ^ 2 := by
  by_cases hσ : σ = 0
  · subst σ
    have hp : (0 : ℝ) ^ (3 - α) = 0 := Real.zero_rpow (by linarith : 3 - α ≠ 0)
    simp [hp]
  have hσpow : σ ^ 3 ≤ σ ^ (3 - α) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne hσ0 (Ne.symm hσ))
      hσ1 (by linarith : 3 - α ≤ 3)
    rwa [← Real.rpow_natCast]
  have hu3 : u ^ 3 ≤ u ^ 2 := by
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]
  calc
    (C * σ * u) ^ 3 = C ^ 3 * σ ^ 3 * u ^ 3 := by ring
    _ ≤ C ^ 3 * σ ^ (3 - α) * u ^ 3 := by gcongr
    _ ≤ C ^ 3 * σ ^ (3 - α) * u ^ 2 := by gcongr

end Balaban.SmallField
