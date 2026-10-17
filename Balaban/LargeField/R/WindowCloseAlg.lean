/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The arithmetic of the composed window bound (blocker 4, W964)

`window_pt_combine`: the pointwise bound `hbG` of `window_hid_core_action` from the five facts proved separately:
the exact node integral `cN e^{-g}`, the sum identity `𝒜 ≥ A_D - C_kk` of the main actions, the monotonicity
`A_{D''} ≤ A_D` of the restricted action, the denominator `∫ρ`, and the quotient bound
`e^{-g - (A_{D''} - C_kk)} cN / cI / ∫ρ ≤ B_q`.  The result is `c₀/∫ρ · e^{-𝒜} · cN e^{-g} ≤ cI B_q`.
-/

@[expose] public section

namespace Balaban.LargeField

open ENNReal

/-- **The arithmetic of `hbG`.** -/
theorem window_pt_combine {c0 rd cN cI Bq g A AD AD'' Ckk : ℝ} (hc0 : 0 ≤ c0) (hc01 : c0 ≤ 1) (hrd : 0 < rd)
    (hcN : 0 < cN) (hcI : 0 < cI)
    (hsum : AD - Ckk ≤ A) (hmono : AD'' ≤ AD)
    (hquot : Real.exp (-g - (AD'' - Ckk)) * cN / cI / rd ≤ Bq) :
    c0 / rd * Real.exp (-A) * (cN * Real.exp (-g)) ≤ cI * Bq := by
  have h1 : Real.exp (-A) ≤ Real.exp (-AD'' + Ckk) := Real.exp_le_exp.2 (by linarith)
  have hBq : 0 ≤ Bq := le_trans (by positivity) hquot
  have h2 : Real.exp (-g - (AD'' - Ckk)) * cN / cI / rd * (cI * rd) = Real.exp (-AD'' + Ckk) * (cN * Real.exp (-g)) := by
    have e : Real.exp (-g - (AD'' - Ckk)) = Real.exp (-AD'' + Ckk) * Real.exp (-g) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    field_simp
  have h3 : Real.exp (-AD'' + Ckk) * (cN * Real.exp (-g)) ≤ cI * rd * Bq := by
    have := mul_le_mul_of_nonneg_right hquot (le_of_lt (mul_pos hcI hrd))
    rw [h2] at this
    linarith
  have h4 : c0 / rd * Real.exp (-A) * (cN * Real.exp (-g)) ≤ c0 / rd * (Real.exp (-AD'' + Ckk) * (cN * Real.exp (-g))) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
  calc c0 / rd * Real.exp (-A) * (cN * Real.exp (-g))
      ≤ c0 / rd * (Real.exp (-AD'' + Ckk) * (cN * Real.exp (-g))) := h4
    _ ≤ c0 / rd * (cI * rd * Bq) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = c0 * (cI * Bq) := by field_simp
    _ ≤ 1 * (cI * Bq) := mul_le_mul_of_nonneg_right hc01 (by positivity)
    _ = cI * Bq := one_mul _

/-- **The same in `ℝ≥0∞`**: the weight of `hbG`. -/
theorem window_pt_combine_ennreal {c0 rd cN cI Bq g A AD AD'' Ckk : ℝ} (hc0 : 0 ≤ c0) (hc01 : c0 ≤ 1)
    (hrd : 0 < rd) (hcN : 0 < cN) (hcI : 0 < cI) (hsum : AD - Ckk ≤ A) (hmono : AD'' ≤ AD)
    (hquot : Real.exp (-g - (AD'' - Ckk)) * cN / cI / rd ≤ Bq) :
    ENNReal.ofReal (c0 / rd) * ENNReal.ofReal (Real.exp (-A)) * ENNReal.ofReal (cN * Real.exp (-g)) ≤
      ENNReal.ofReal (cI * Bq) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (window_pt_combine hc0 hc01 hrd hcN hcI hsum hmono hquot)

/-- **`hbG` assembled from its parts**: the integral `Iint` of the Gaussian chain equals `cN e^{-g}`, `Qtot = cI B_q`, and the
denominator `rd` equals the integral `I`. -/
theorem window_pt_combine_final {c0 rd I cN cI Bq g A AD AD'' Ckk : ℝ} {Iint Qtot : ℝ≥0∞} (hc0 : 0 ≤ c0)
    (hc01 : c0 ≤ 1) (hrd : 0 < rd) (hrdI : rd = I) (hcN : 0 < cN) (hcI : 0 < cI) (hsum : AD - Ckk ≤ A)
    (hmono : AD'' ≤ AD) (hquot : Real.exp (-g - (AD'' - Ckk)) * cN / cI / I ≤ Bq)
    (hint : Iint = ENNReal.ofReal (cN * Real.exp (-g))) (hQ : Qtot = ENNReal.ofReal (cI * Bq)) :
    ENNReal.ofReal (c0 / rd) * ENNReal.ofReal (Real.exp (-A)) * Iint ≤ Qtot := by
  subst hint hQ hrdI
  exact window_pt_combine_ennreal hc0 hc01 hrd hcN hcI hsum hmono hquot

/-- A positive real integral gives a positive integral in `ℝ≥0∞`. -/
theorem window_pos_of_eq {Iint : ℝ≥0∞} {x : ℝ} (h : Iint = ENNReal.ofReal x) (hx : 0 < x) : 0 < Iint := by
  rw [h]; exact ENNReal.ofReal_pos.mpr hx

end Balaban.LargeField
