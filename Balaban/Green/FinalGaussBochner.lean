/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.GaussianChangeGeneral

/-!
# The Gaussian change of variables for complex integrands

`lintegral_pd_gaussian_change` (`Green/GaussianChangeGeneral.lean`) is an identity of lower
integrals for nonnegative functions. This file turns it into an identity of measures,
`pd_withDensity_eq_map`: the measure `exp(-½ Q_K(v)) dv` is `Z_K` times the image of the standard
Gaussian under `ψ ↦ K^{-1/2} ψ`, and then into the Bochner form for every measurable complex
integrand `F`,

`∫ F(v) exp(-½ Q_K(v)) dv = Z_K ∫ F(K^{-1/2} ψ) dγ(ψ)`

(`integral_pd_gaussian_change`), with no integrability hypothesis (both sides vanish together).
-/

@[expose] public section

open Matrix MeasureTheory Balaban.LargeField

namespace Balaban.Green

variable {ι W : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]

omit [DecidableEq ι] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
/-- `matAct S` is continuous on fields with values in a normed space. -/
theorem continuous_matAct (S : Matrix ι ι ℝ) : Continuous (matAct (W := W) S) := by
  unfold matAct
  fun_prop

/-- **The measure `exp(-½ Q_K(v)) dv` is `Z_K` times the image of the standard Gaussian under
`ψ ↦ K^{-1/2} ψ`.** -/
theorem pd_withDensity_eq_map {K : Matrix ι ι ℝ} (hK : K.PosDef) :
    (pdVol ι W).withDensity (fun v => ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v))) =
      ENNReal.ofReal (pdGaussNorm ι W K) •
        (pdGaussian ι W).map (matAct (pdSqrtInv K)) := by
  ext A hA
  have hm : Measurable (matAct (W := W) (pdSqrtInv K)) := (continuous_matAct _).measurable
  rw [withDensity_apply _ hA, Measure.smul_apply, Measure.map_apply hm hA, smul_eq_mul]
  have h := lintegral_pd_gaussian_change (W := W) hK (A.indicator fun _ => (1 : ENNReal))
  have e1 : ∫⁻ v in A, ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)) ∂(pdVol ι W) =
      ∫⁻ v, A.indicator (fun _ => (1 : ENNReal)) v *
        ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)) ∂(pdVol ι W) := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A <;> simp [Set.indicator, hv]
  have e2 : ∫⁻ ψ, A.indicator (fun _ => (1 : ENNReal)) (matAct (pdSqrtInv K) ψ) ∂(pdGaussian ι W) =
      (pdGaussian ι W) (matAct (pdSqrtInv K) ⁻¹' A) := by
    have : (fun ψ => A.indicator (fun _ => (1 : ENNReal)) (matAct (pdSqrtInv K) ψ)) =
        (matAct (pdSqrtInv K) ⁻¹' A).indicator (fun _ => (1 : ENNReal)) := by
      funext ψ; by_cases hv : matAct (pdSqrtInv K) ψ ∈ A <;> simp [Set.indicator, hv]
    rw [this, lintegral_indicator_const (hm hA), one_mul]
  rw [e1, h, e2]

/-- **The Gaussian change of variables for complex integrands**, no integrability hypothesis:
for every measurable `F : (ι → W) → ℂ`,
`∫ F(v) exp(-½ Q_K(v)) dv = Z_K ∫ F(K^{-1/2} ψ) dγ(ψ)`. -/
theorem integral_pd_gaussian_change {K : Matrix ι ι ℝ} (hK : K.PosDef) {F : (ι → W) → ℂ}
    (hF : Measurable F) :
    ∫ v, ((Real.exp (-(1 / 2) * pdQuad K v) : ℝ) : ℂ) * F v ∂(pdVol ι W) =
      (pdGaussNorm ι W K : ℂ) * ∫ ψ, F (matAct (pdSqrtInv K) ψ) ∂(pdGaussian ι W) := by
  have hm : Measurable (matAct (W := W) (pdSqrtInv K)) := (continuous_matAct _).measurable
  have hq : Measurable fun v : ι → W => Real.exp (-(1 / 2) * pdQuad K v) := by
    refine Real.measurable_exp.comp ?_
    refine Measurable.const_mul ?_ _
    unfold pdQuad pdBil
    fun_prop
  have h1 : ∫ v, ((Real.exp (-(1 / 2) * pdQuad K v) : ℝ) : ℂ) * F v ∂(pdVol ι W) =
      ∫ v, F v ∂((pdVol ι W).withDensity
        (fun v => ENNReal.ofReal (Real.exp (-(1 / 2) * pdQuad K v)))) := by
    rw [integral_withDensity_eq_integral_toReal_smul (hq.ennreal_ofReal)]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
    · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [h1, pd_withDensity_eq_map hK, integral_smul_measure, integral_map hm.aemeasurable
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal (pdGaussNorm_pos hK).le, Complex.real_smul]

end Balaban.Green
