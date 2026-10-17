/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical scale comparison for the anisotropic datum
-/

@[expose] public section

namespace Balaban.SmallField

/-- With `τ = c s`, `ζ = H e` and `σ = 16 c H s`, the four numerical bounds required
by the anisotropic data constructor follow from `e ≤ ε`. -/
theorem source_to_aniso_numeric {c H s e ε : ℝ}
    (hc : 1 ≤ c) (hH : 1 ≤ H) (hs : 0 ≤ s) (he : 0 ≤ e) (hee : e ≤ ε) :
    2 * (c * s) ^ 2 * (H * e) ≤ (16 * c * H * s) ^ 2 * ε ∧
    2 * (c * s) * (H * e) ≤ (16 * c * H * s) * ε ∧
    10 * (c * s) ^ 2 * (H * e) ≤ (16 * c * H * s) ^ 2 * ε ∧
    98 * (c * s) ^ 2 * (H * e) ^ 2 ≤ (16 * c * H * s) ^ 2 * ε ^ 2 := by
  have hH2 : H ≤ H ^ 2 := by nlinarith [sq_nonneg (H - 1)]
  have hε : 0 ≤ ε := he.trans hee
  have he2 : e ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ he hee 2
  have hcoef2 : 2 * c ^ 2 * H ≤ (16 * c * H) ^ 2 := by
    have hh : 2 * H ≤ 256 * H ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
    nlinarith
  have hcoef10 : 10 * c ^ 2 * H ≤ (16 * c * H) ^ 2 := by
    have hh : 10 * H ≤ 256 * H ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
    nlinarith
  have hcoef98 : 98 * c ^ 2 * H ^ 2 ≤ (16 * c * H) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg H)]
  have hcoefAdj : 2 * c * H ≤ 16 * c * H := by
    nlinarith [mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hH)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = (2 * c ^ 2 * H) * s ^ 2 * e := by ring
      _ ≤ (2 * c ^ 2 * H) * s ^ 2 * ε := by gcongr
      _ ≤ (16 * c * H) ^ 2 * s ^ 2 * ε := by gcongr
      _ = _ := by ring
  · calc
      _ = (2 * c * H) * s * e := by ring
      _ ≤ (2 * c * H) * s * ε := by gcongr
      _ ≤ (16 * c * H) * s * ε := by gcongr
      _ = _ := by ring
  · calc
      _ = (10 * c ^ 2 * H) * s ^ 2 * e := by ring
      _ ≤ (10 * c ^ 2 * H) * s ^ 2 * ε := by gcongr
      _ ≤ (16 * c * H) ^ 2 * s ^ 2 * ε := by gcongr
      _ = _ := by ring
  · calc
      _ = (98 * c ^ 2 * H ^ 2) * s ^ 2 * e ^ 2 := by ring
      _ ≤ (98 * c ^ 2 * H ^ 2) * s ^ 2 * ε ^ 2 := by gcongr
      _ ≤ (16 * c * H) ^ 2 * s ^ 2 * ε ^ 2 := by gcongr
      _ = _ := by ring

end Balaban.SmallField
