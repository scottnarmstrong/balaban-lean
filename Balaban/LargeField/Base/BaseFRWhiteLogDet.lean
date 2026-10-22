/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteChange

/-!
# The determinant of the finite-range whitening

From `W A W = 1 + D_R` (`whiteW_mul_mul_whiteW`): `(det W)² det A = det (1 + D_R)`
(`det_whiteW_sq_mul_det`), hence for `‖D_R‖ < 1` and invertible `A`
`log |det W| = ½ log |det (1 + D_R)| - ½ log |det A|` (`log_abs_det_whiteW`). The series
`log det (1 + D) = ∑_{n ≥ 1} (-1)^{n+1} tr(D^n)/n` for `‖D‖ < 1` is not in this file.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Balaban.LargeField.FRWhite
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

section LogDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`(det W)² det A = det (1 + D_R)`.** -/
theorem det_whiteW_sq_mul_det {γ J : ℝ} (hγ : 0 < γ) (hJ : 0 < J) (A : Matrix ι ι ℂ) (R : ℕ) :
    (whiteW γ J A R).det ^ 2 * A.det = (1 + whiteDefect (whiteK γ J A) R).det := by
  rw [← whiteW_mul_mul_whiteW hγ hJ A R, Matrix.det_mul, Matrix.det_mul]
  ring

/-- **`log |det W| = ½ log |det (1 + D_R)| - ½ log |det A|`** for an invertible `A` and a defect of
norm below `1`. -/
theorem log_abs_det_whiteW [Nonempty ι] {γ J : ℝ} (hγ : 0 < γ) (hJ : 0 < J) {A : Matrix ι ι ℂ}
    (hA : IsUnit A) (R : ℕ) (hD : ‖whiteDefect (whiteK γ J A) R‖ < 1) :
    Real.log ‖(whiteW γ J A R).det‖ =
      (1 / 2) * Real.log ‖(1 + whiteDefect (whiteK γ J A) R).det‖ -
        (1 / 2) * Real.log ‖A.det‖ := by
  have hW : (whiteW γ J A R).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 (whiteW_isUnit hγ hJ A R hD)).ne_zero
  have hAd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hA).ne_zero
  have h := congrArg norm (det_whiteW_sq_mul_det hγ hJ A R)
  rw [norm_mul, norm_pow] at h
  have hn1 : 0 < ‖(whiteW γ J A R).det‖ := norm_pos_iff.2 hW
  have hn2 : 0 < ‖A.det‖ := norm_pos_iff.2 hAd
  have := congrArg Real.log h
  rw [Real.log_mul (pow_pos hn1 2).ne' hn2.ne', Real.log_pow] at this
  push_cast at this
  linarith

end LogDet

end Balaban.LargeField.FRWhite
