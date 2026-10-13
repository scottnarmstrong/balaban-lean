/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutInterpolation

/-!
# Real and complex Gaussian inverse square roots

The real square root used for the chart change of variables agrees, after
complexification, with the principal Stieltjes square root used by the cut
component covariance in P4 (2.49)–(2.54).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.Green Balaban.Localization Matrix
open scoped ComplexOrder MatrixOrder

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- For a real positive definite matrix, W714's real inverse square root is
W711's principal complex inverse square root after complexification. -/
theorem pdSqrtInv_map_eq_sqrtMat (K : Matrix κ κ ℝ) (hK : K.PosDef) :
    (pdSqrtInv K).map (algebraMap ℝ ℂ) =
      sqrtMat (K.map (algebraMap ℝ ℂ)) := by
  let A := K.map (algebraMap ℝ ℂ)
  let R := (pdSqrtInv K).map (algebraMap ℝ ℂ)
  have hA : A.PosDef := posDef_map_ofReal hK
  have hR : R.PosDef := posDef_map_ofReal (pdSqrtInv_posDef hK)
  have hRR : R * R = A⁻¹ := by
    change (pdSqrtInv K).map (algebraMap ℝ ℂ) *
      (pdSqrtInv K).map (algebraMap ℝ ℂ) =
      (K.map (algebraMap ℝ ℂ))⁻¹
    rw [← Matrix.map_mul, pdSqrtInv_mul_self hK]
    exact (map_inv_ofReal ((Matrix.isUnit_iff_isUnit_det K).1 hK.isUnit)).symm
  have hS : (sqrtMat A).PosDef := by
    have heq : sqrtMat A = invSqrtMat hA := resolvent_sqrt_eq hA
    rw [heq]
    exact invSqrtMat_posDef hA
  have hSS : sqrtMat A * sqrtMat A = A⁻¹ :=
    sqrtMat_mul_self (resOK_of_posDef hA)
  have hRroot : R = CFC.sqrt A⁻¹ :=
    (CFC.sqrt_unique (a := A⁻¹) (b := R) hRR
      (Matrix.nonneg_iff_posSemidef.mpr hR.posSemidef)).symm
  have hSroot : sqrtMat A = CFC.sqrt A⁻¹ :=
    (CFC.sqrt_unique (a := A⁻¹) (b := sqrtMat A) hSS
      (Matrix.nonneg_iff_posSemidef.mpr hS.posSemidef)).symm
  exact hRroot.trans hSroot.symm

end Balaban.LargeField
