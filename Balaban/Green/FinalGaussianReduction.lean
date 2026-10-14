/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.GaussianChangeGeneral

/-!
# The Gaussian reduction at the physical point (W787, FINALPHYS2 leaf E3)

For a real symmetric positive definite matrix `K` on a finite index type and a finite-dimensional
real inner product space `W`, the normalized integral
`Z[F] / Z[1] = ∫ F(v) exp(-½ Q_K(v)) dv / ∫ exp(-½ Q_K(v)) dv`
equals `∫ F(C ψ) dγ(ψ)` with `C = pdSqrtInv K = K^{-1/2}` and `γ` the standard Gaussian.  The change
of variables is made once, at the physical point; no family of square roots is needed.  This is the
ratio form of the landed `lintegral_pd_gaussian_change`.
-/

@[expose] public section

open Matrix MeasureTheory Balaban.LargeField

namespace Balaban.Green

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

/-- The partition function `Z[1] = ∫ exp(-½ Q_K(v)) dv` is the Gaussian norm. -/
theorem lintegral_pd_gaussian_partition {K : Matrix ι ι ℝ} (hK : K.PosDef) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)) ∂(pdVol ι W) =
      ENNReal.ofReal (pdGaussNorm ι W K) := by
  have h := lintegral_pd_gaussian_change (W := W) hK (fun _ => (1 : ENNReal))
  simp only [one_mul, lintegral_const] at h
  rw [pdGaussian_univ] at h
  simpa using h

/-- **The Gaussian reduction** `Z[F] / Z[1] = ∫ F(K^{-1/2} ψ) dγ(ψ)`. -/
theorem lintegral_pd_gaussian_ratio {K : Matrix ι ι ℝ} (hK : K.PosDef)
    (F : (ι → W) → ENNReal) :
    (∫⁻ v, F v * ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)) ∂(pdVol ι W)) /
        (∫⁻ v, ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)) ∂(pdVol ι W)) =
      ∫⁻ ψ, F (matAct (pdSqrtInv K) ψ) ∂(pdGaussian ι W) := by
  rw [lintegral_pd_gaussian_partition hK, lintegral_pd_gaussian_change hK F]
  rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel
    (by simpa using pdGaussNorm_pos (W := W) hK) ENNReal.ofReal_ne_top, one_mul]

end Balaban.Green
