/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteSymm
public import Balaban.LargeField.Base.BaseChartGaussianNormalization

/-!
# The whitened change of variables in the chart Gaussian integral (route FR-1)

For an approximate square root `W` of the chart Gaussian form,
`⟨Wφ, gaussForm(Wφ)⟩ = |φ|² + q_D(φ)`, the tangent Gaussian integral becomes (LF-BASE-KF0 (A.3),
Lemma II.7.4 (b) with the finite-range square root of `BaseFRWhite.lean`)

`∫ e^{-½⟨v, Hv⟩} f(v) dv = (2π)^{-|ι|/2} |det W| ∫ e^{-½(|φ|² + q_D(φ))} f(P(Wφ)) dφ`,

over the tangent space `v` and Lebesgue measure on `ℝ^{N|ι|}`; `whiteW_isUnit` gives the
invertibility of `W` from `W A W = 1 + D_R`, `‖D_R‖ < 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Balaban.LargeField Balaban.LargeField.Base SphereChart Matrix Balaban.Green
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

/-- Lebesgue change of variables by a linear equivalence (Bochner form). -/
theorem integral_comp_linearEquiv_abs_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) (g : E → F) :
    ∫ φ, g (T φ) ∂μ = |LinearMap.det (T : E →ₗ[ℝ] E)|⁻¹ • ∫ u, g u ∂μ := by
  have hdet : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hemb : MeasurableEmbedding T := (T.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  rw [← hemb.integral_map, show (T : E → E) = (T : E →ₗ[ℝ] E) from rfl, hmap, integral_smul_measure]
  rw [abs_inv, ENNReal.toReal_ofReal (by positivity)]


/-- Lebesgue-integrability is preserved by composition with a linear equivalence. -/
theorem integrable_comp_linearEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F]
    (μ : Measure E) [μ.IsAddHaarMeasure] (T : E ≃ₗ[ℝ] E) {g : E → F} (hg : Integrable g μ) :
    Integrable (fun φ => g (T φ)) μ := by
  have hdet : LinearMap.det (T : E →ₗ[ℝ] E) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hemb : MeasurableEmbedding T := (T.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have h : Integrable g (Measure.map T μ) := by
    rw [show (T : E → E) = (T : E →ₗ[ℝ] E) from rfl, hmap]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact (hemb.integrable_map_iff).1 h


section Whitened

open Balaban.LargeField.Base

/-- A positive definite chart form has an exact square root `R` with
`⟨Rψ, gaussForm(Rψ)⟩ = ⟨ψ, ψ⟩`. -/
theorem exists_sqrt_equiv_cinner {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (e : Config ι N) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hK : (LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm e H)).PosDef) :
    ∃ R : Config ι N ≃ₗ[ℝ] Config ι N,
      ∀ ψ, cinner (R ψ) (gaussForm e H (R ψ)) = cinner ψ ψ := by
  obtain ⟨R, hRR, hRs, -⟩ := gaussForm_sqrt_equiv_of_posDef e H hK
  refine ⟨R, fun ψ => ?_⟩
  have h1 : gaussForm e H (R ψ) = R.symm ψ := by
    have h2 := hRR (R.symm ψ)
    rwa [LinearEquiv.apply_symm_apply] at h2
  rw [h1, hRs, LinearEquiv.apply_symm_apply]

theorem measurable_stdGaussian_density (ι : Type*) [Fintype ι] (N : ℕ) :
    Measurable fun ψ : Config ι N => ENNReal.ofReal
      ((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
        Real.exp (-(1 / 2) * cinner ψ ψ)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  unfold cinner
  fun_prop

/-- The integral against the standard Gaussian is the Lebesgue integral against its density. -/
theorem integral_stdGaussian_eq {ι : Type*} [Fintype ι] {N : ℕ} (g : Config ι N → ℂ) :
    ∫ ψ, g ψ ∂(stdGaussian ι N) =
      ∫ ψ, (((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
        Real.exp (-(1 / 2) * cinner ψ ψ) : ℝ) : ℂ) * g ψ := by
  unfold stdGaussian
  rw [integral_withDensity_eq_integral_toReal_smul₀ (measurable_stdGaussian_density ι N).aemeasurable
    (Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  simp only [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- Integrability against the standard Gaussian is Lebesgue integrability against its density. -/
theorem integrable_stdGaussian_iff {ι : Type*} [Fintype ι] {N : ℕ} (g : Config ι N → ℂ) :
    Integrable g (stdGaussian ι N) ↔
      Integrable (fun ψ => (((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
        Real.exp (-(1 / 2) * cinner ψ ψ) : ℝ) : ℂ) * g ψ) := by
  unfold stdGaussian
  rw [integrable_withDensity_iff_integrable_smul' (measurable_stdGaussian_density ι N)
    (Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Filter.Eventually.of_forall fun ψ => ?_)
  simp only [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- **The whitened change of variables** (LF-BASE-KF0 (A.3), Lemma II.7.4 (b)) with an approximate
square root: for a linear equivalence `W` of `ℝ^{N|ι|}` with
`⟨Wφ, gaussForm(Wφ)⟩ = |φ|² + q_D(φ)`,
`∫ e^{-½⟨v, Hv⟩} f(v) dv = (2π)^{-|ι|/2} |det W| ∫ e^{-½(|φ|² + q_D(φ))} f(P(Wφ)) dφ`
(`v` over the tangent space, `P` the tangent projection, Lebesgue `dφ` on `ℝ^{N|ι|}`). -/
theorem integral_tangent_gaussian_whitened {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (e : Config ι N) (he : ∀ x, ‖e x‖ = 1) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hK : (LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm e H)).PosDef)
    (W : Config ι N ≃ₗ[ℝ] Config ι N) (qD : Config ι N → ℝ)
    (hW : ∀ φ, cinner (W φ) (gaussForm e H (W φ)) = cinner φ φ + qD φ)
    (f : ((x : ι) → perp (e x)) → ℂ) (hf : Measurable f) :
    ∫ v : (x : ι) → perp (e x),
      (((Real.exp (-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))))) : ℝ) : ℂ) * f v
      ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) =
      (((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * |LinearMap.det (W : Config ι N →ₗ[ℝ] Config ι N)| : ℝ) : ℂ) *
        ∫ φ : Config ι N, (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
          f (tangentProj e he (W φ)) := by
  classical
  obtain ⟨R, hR⟩ := exists_sqrt_equiv_cinner e H hK
  rw [integral_tangent_gaussian_complex e he H R hR f hf]
  set T : Config ι N ≃ₗ[ℝ] Config ι N := W.trans R.symm with hT
  have hRT : ∀ φ, R (T φ) = W φ := fun φ => by simp [hT]
  have hdet : LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N) *
      LinearMap.det (T : Config ι N →ₗ[ℝ] Config ι N) =
      LinearMap.det (W : Config ι N →ₗ[ℝ] Config ι N) := by
    rw [← LinearMap.det_comp]
    congr 1
    exact LinearMap.ext fun φ => hRT φ
  have hmf : Measurable fun ψ : Config ι N => f (tangentProj e he (R ψ)) :=
    hf.comp ((measurable_tangentProj e he).comp
      (LinearMap.continuous_of_finiteDimensional (R : Config ι N →ₗ[ℝ] Config ι N)).measurable)
  rw [integral_stdGaussian_eq]
  set c : ℝ := (2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) with hc
  have hcv := integral_comp_linearEquiv_abs_det (volume : Measure (Config ι N)) T
    (fun ψ => (((c * Real.exp (-(1 / 2) * cinner ψ ψ) : ℝ) : ℂ)) * f (tangentProj e he (R ψ)))
  have hdT : 0 < |LinearMap.det (T : Config ι N →ₗ[ℝ] Config ι N)| := by
    rw [abs_pos, ← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hinner : ∀ φ, (((c * Real.exp (-(1 / 2) * cinner (T φ) (T φ)) : ℝ) : ℂ)) *
        f (tangentProj e he (R (T φ))) =
      (c : ℂ) * ((((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
        f (tangentProj e he (W φ))) := by
    intro φ
    have h1 : cinner (T φ) (T φ) = cinner φ φ + qD φ := by
      rw [← hR (T φ), hRT, hW]
    rw [h1, hRT]
    push_cast
    ring
  simp only [hinner] at hcv
  rw [integral_const_mul] at hcv
  have hexp : ∫ ψ, (((c * Real.exp (-(1 / 2) * cinner ψ ψ) : ℝ) : ℂ)) *
      f (tangentProj e he (R ψ)) =
      |LinearMap.det (T : Config ι N →ₗ[ℝ] Config ι N)| •
        ((c : ℂ) * ∫ φ, (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
          f (tangentProj e he (W φ))) := by
    rw [hcv, smul_smul, mul_inv_cancel₀ hdT.ne', one_smul]
  rw [hexp, Complex.real_smul]
  have hp : 0 < 2 * Real.pi := by positivity
  have hrp : (2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card ι / 2) * c =
      (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) := by
    rw [hc, ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  have habs : |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)| *
      |LinearMap.det (T : Config ι N →ₗ[ℝ] Config ι N)| =
      |LinearMap.det (W : Config ι N →ₗ[ℝ] Config ι N)| := by rw [← abs_mul, hdet]
  have key : ((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card ι / 2) *
      |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)| : ℝ) *
      (|LinearMap.det (T : Config ι N →ₗ[ℝ] Config ι N)| * c) =
      (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) *
        |LinearMap.det (W : Config ι N →ₗ[ℝ] Config ι N)| := by
    rw [← habs, ← hrp]; ring
  have key' := congrArg (fun r : ℝ => (r : ℂ)) key
  simp only [Complex.ofReal_mul] at key'
  generalize (∫ φ : Config ι N, (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
    f (tangentProj e he (W φ))) = I
  push_cast at key' ⊢
  linear_combination I * key'

/-- **Integrability for the whitened change of variables**: if the tangent Gaussian integrand
`e^{-½⟨v, Hv⟩} f(v)` is integrable on the tangent space, then the whitened integrand
`e^{-½(|φ|² + q_D(φ))} f(P(Wφ))` is Lebesgue integrable on `ℝ^{N|ι|}` (the measure form of
`integral_tangent_gaussian_whitened`). -/
theorem integrable_tangent_gaussian_whitened {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (e : Config ι N) (he : ∀ x, ‖e x‖ = 1) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hK : (LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm e H)).PosDef)
    (W : Config ι N ≃ₗ[ℝ] Config ι N) (qD : Config ι N → ℝ)
    (hW : ∀ φ, cinner (W φ) (gaussForm e H (W φ)) = cinner φ φ + qD φ)
    (f : ((x : ι) → perp (e x)) → ℂ) (hf : Measurable f)
    (hint : Integrable (fun v : (x : ι) → perp (e x) =>
      (((Real.exp (-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))))) : ℝ) : ℂ) * f v)
      (Measure.pi fun x => (volume : Measure (perp (e x))))) :
    Integrable (fun φ : Config ι N =>
      (((Real.exp (-(1 / 2) * (cinner φ φ + qD φ))) : ℝ) : ℂ) *
        f (tangentProj e he (W φ))) := by
  classical
  obtain ⟨R, hR⟩ := exists_sqrt_equiv_cinner e H hK
  set T : Config ι N ≃ₗ[ℝ] Config ι N := W.trans R.symm with hT
  have hRT : ∀ φ, R (T φ) = W φ := fun φ => by simp [hT]
  let μ : Measure ((x : ι) → perp (e x)) := Measure.pi fun x => volume
  let q : ((x : ι) → perp (e x)) → ℝ := fun v =>
    Real.exp (-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
      (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))))
  let t : Config ι N → ((x : ι) → perp (e x)) := fun ψ => tangentProj e he (R ψ)
  let C : ℝ := (2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card ι / 2) *
    |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)|
  have hdetR : LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hCpos : 0 < C := by
    have : 0 < |LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N)| := abs_pos.2 hdetR
    positivity
  have hq : Measurable q := by
    have hc : Continuous H := LinearMap.continuous_of_finiteDimensional H
    have hv : Measurable fun v : (x : ι) → perp (e x) =>
        (fun x => (v x : EuclideanSpace ℝ (Fin N)) : Config ι N) :=
      measurable_pi_iff.2 fun x => measurable_subtype_coe.comp (measurable_pi_apply x)
    dsimp [q, cinner]
    fun_prop
  have ht : Measurable t :=
    (measurable_tangentProj e he).comp
      (LinearMap.continuous_of_finiteDimensional
        (R : Config ι N →ₗ[ℝ] Config ι N)).measurable
  have hmeas : μ.withDensity (fun v => ENNReal.ofReal (q v)) =
      ENNReal.ofReal C • Measure.map t (stdGaussian ι N) :=
    withDensity_tangent_gaussian_eq e he H R hR
  have h1 : Integrable f (μ.withDensity (fun v => ENNReal.ofReal (q v))) := by
    have hmd : Measurable (fun v => ENNReal.ofReal (q v)) := ENNReal.measurable_ofReal.comp hq
    rw [integrable_withDensity_iff_integrable_smul' hmd
      (Filter.Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
    refine hint.congr (Filter.Eventually.of_forall fun v => ?_)
    simp only [Complex.real_smul]
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [hmeas, integrable_smul_measure (by simpa using hCpos) ENNReal.ofReal_ne_top] at h1
  have h2 : Integrable (fun ψ => f (t ψ)) (stdGaussian ι N) :=
    (integrable_map_measure hf.aestronglyMeasurable ht.aemeasurable).1 h1
  have h3 := (integrable_stdGaussian_iff _).1 h2
  have h4 := integrable_comp_linearEquiv (volume : Measure (Config ι N)) T h3
  set c : ℝ := (2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) with hc
  have hc0 : (c : ℂ) ≠ 0 := by
    rw [hc]; exact_mod_cast (by positivity : (2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) ≠ 0)
  refine (h4.const_mul ((c : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun φ => ?_)
  have h5 : cinner (T φ) (T φ) = cinner φ φ + qD φ := by
    rw [← hR (T φ), hRT, hW]
  show (c : ℂ)⁻¹ * ((((c * Real.exp (-(1 / 2) * cinner (T φ) (T φ)) : ℝ)) : ℂ) *
      f (tangentProj e he (R (T φ)))) = _
  rw [h5, hRT]
  push_cast
  field_simp

end Whitened


section Unit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`W` is invertible** when the defect is below `1`: `det (W A W) = (det W)² det A` and
`W A W = 1 + D_R` is a unit. -/
theorem whiteW_isUnit {γ J : ℝ} (hγ : 0 < γ) (hJ : 0 < J) (A : Matrix ι ι ℂ) (R : ℕ)
    [Nonempty ι] (hD : ‖whiteDefect (whiteK γ J A) R‖ < 1) : IsUnit (whiteW γ J A R) := by
  have h := whiteW_mul_mul_whiteW hγ hJ A R
  have hu : IsUnit (1 + whiteDefect (whiteK γ J A) R) := by
    have := IsUnit.one_sub_of_norm_lt_one (x := -whiteDefect (whiteK γ J A) R) (by rwa [norm_neg])
    simpa [sub_neg_eq_add] using this
  rw [← h] at hu
  rw [Matrix.isUnit_iff_isUnit_det] at hu ⊢
  rw [Matrix.det_mul, Matrix.det_mul] at hu
  exact (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))

end Unit

end Balaban.LargeField.FRWhite
