/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartComponentNormalization
public import Balaban.LargeField.Base.BaseChartQuadraticPhysical

/-!
# The chart Gaussian integral over an abstract set of sites

Let `ι` be a finite set of sites carrying unit spins, `e` a unit background field, and
`Bf : (ι → S^{N-1}) → ℝ` an action with the exact chord expansion
`Bf ψ - Bf e = ½ ⟨ψ - e, H (ψ - e)⟩` for a symmetric `H` whose Gaussian form is positive
definite.  For a cutoff `χ` supported in the hemispheres around `e`, a regime-A mass coefficient
`m`, a complex source `g` and a constant `K0`, the integral against the product sphere measure
of `χ K0 exp(-β Bf ψ - m ∑ ‖ψ_x - h‖² + ⟨g, ψ⟩)` is the Gaussian prefactor times the standard
Gaussian integral of the remainder `chartGaussRem` (`chartGaussian_core`).

Nothing in this statement refers to the torus, to generating sets or to the record: the geometric
inputs (the chord expansion, the hemisphere support, positivity) are hypotheses.  The first-step
sectors are instances of it.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

attribute [local fun_prop] measurable_chartMapPi

/-- **The sphere integrand of the chart Gaussian core**:
`χ K0 exp(-β Bf ψ - m ∑ ‖ψ_x - h‖² + ⟨g, ψ⟩)`. -/
def chartGaussDensity (β m : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : ι → Fin N → ℂ)
    (K0 : ℂ) (χ : (ι → Sph) → ℝ) (Bf : (ι → Sph) → ℝ) (ψ : ι → Sph) : ℂ :=
  (χ ψ : ℂ) * K0 * Complex.exp (-((β * Bf ψ : ℝ) : ℂ) -
    ((m * ∑ x, ‖(ψ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
    ∑ x, ∑ i : Fin N, g x i * ((((ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ)) : ℂ))

/-- **The remainder of the chart Gaussian core**, as a function of the tangent coordinates `v`:
the Jacobian, the cutoff, the constant and the exponential of the background value, the source,
and the non-quadratic part of the chart exponent. -/
def chartGaussRem (β m : ℝ) (e : Config ι N) (he : ∀ x, ‖e x‖ = 1)
    (H : Config ι N →ₗ[ℝ] Config ι N) (h : EuclideanSpace ℝ (Fin N)) (g : ι → Fin N → ℂ)
    (K0 : ℂ) (χ : (ι → Sph) → ℝ) (Bec : ℝ) (v : (x : ι) → perp (e x)) : ℂ :=
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Config ι N := fun x => (v x : EuclideanSpace ℝ (Fin N))
  let z := chartShift β e w
  let M := m * ∑ x, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
  ((chartJac β w : ℝ) : ℂ) * ((χ φ : ℂ) * K0 *
    Complex.exp (-((β * Bec : ℝ) : ℂ) +
      (∑ x, ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) +
      (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * (∑ x, ∑ i : Fin N, g x i * (((w x + z x) i : ℝ) : ℂ)) -
      ((cinner w (H z) + (1 / 2) * cinner z (H z) + M : ℝ) : ℂ)))

omit [DecidableEq ι] in
theorem measurable_chartGaussRem {β m : ℝ} (e : Config ι N) (he : ∀ x, ‖e x‖ = 1)
    (H : Config ι N →ₗ[ℝ] Config ι N) (h : EuclideanSpace ℝ (Fin N)) (g : ι → Fin N → ℂ)
    (K0 : ℂ) (χ : (ι → Sph) → ℝ) (hχ : Measurable χ) (Bec : ℝ) :
    Measurable (chartGaussRem β m e he H h g K0 χ Bec) := by
  let V := (x : ι) → perp (e x)
  let W : V → Config ι N := fun v x => (v x : EuclideanSpace ℝ (Fin N))
  let Φ : V → (ι → Sph) := fun v => chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let Z : V → Config ι N := fun v => chartShift β e (W v)
  let Mass : V → ℝ := fun v =>
    m * ∑ x, ‖(Φ v x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2
  let Source : V → ℂ := fun v => ∑ x, ∑ i : Fin N, g x i * (((W v x + Z v x) i : ℝ) : ℂ)
  let Cross : V → ℝ := fun v => cinner (W v) (H (Z v))
  let Zquad : V → ℝ := fun v => cinner (Z v) (H (Z v))
  have hH : Measurable H := (LinearMap.continuous_of_finiteDimensional H).measurable
  have hW : Measurable W := by
    refine measurable_pi_iff.mpr fun x => ?_
    fun_prop
  have hΦ : Measurable Φ := by fun_prop
  have hZ : Measurable Z := (measurable_chartShift β e).comp hW
  have hMass : Measurable Mass := by
    dsimp only [Mass]
    fun_prop
  have hSource : Measurable Source := by
    dsimp only [Source]
    fun_prop
  have hCross : Measurable Cross := by
    dsimp only [Cross, cinner]
    fun_prop
  have hZquad : Measurable Zquad := by
    dsimp only [Zquad, cinner]
    fun_prop
  change Measurable (fun v : V =>
    ((chartJac β (W v) : ℝ) : ℂ) *
      ((χ (Φ v) : ℂ) * K0 * Complex.exp (
        -((β * Bec : ℝ) : ℂ) + (∑ x, ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) +
        (((Real.sqrt β)⁻¹ : ℝ) : ℂ) * Source v -
        ((Cross v + (1 / 2) * Zquad v + Mass v : ℝ) : ℂ))))
  refine (Complex.measurable_ofReal.comp ((measurable_chartJac β).comp hW)).mul ?_
  refine ((Complex.measurable_ofReal.comp (hχ.comp hΦ)).mul measurable_const).mul ?_
  apply Complex.measurable_exp.comp
  fun_prop

omit [DecidableEq ι] in
/-- **The pointwise chart identity**: at a tangent vector `v` inside the balls the rescaled
chart integrand is the Gaussian weight times the remainder. -/
theorem chartGauss_pointwise {β : ℝ} (hβ : 0 < β) (m : ℝ) (e : Config ι N)
    (he : ∀ x, ‖e x‖ = 1) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v) (h : EuclideanSpace ℝ (Fin N))
    (g : ι → Fin N → ℂ) (K0 : ℂ) (χ : (ι → Sph) → ℝ) (Bf : (ι → Sph) → ℝ)
    (ec : ι → Sph)
    (hchord : ∀ ψ : ι → Sph, Bf ψ - Bf ec = (1 / 2) *
      cinner (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - e x)
        (H (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - e x)))
    (v : (x : ι) → perp (e x)) :
    (∏ x, ((chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x) : ℝ) : ℂ)) *
        chartGaussDensity β m h g K0 χ Bf (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) =
      Complex.exp (((-(1 / 2) * cinner (fun x => (v x : EuclideanSpace ℝ (Fin N)))
        (H (fun x => (v x : EuclideanSpace ℝ (Fin N)))) : ℝ)) : ℂ) *
        chartGaussRem β m e he H h g K0 χ (Bf ec) v := by
  unfold chartGaussDensity chartGaussRem
  dsimp only
  set w : Config ι N := fun x => (v x : EuclideanSpace ℝ (Fin N)) with hw
  set φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v) with hφ
  have hJ : (∏ x, ((chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x) : ℝ) : ℂ)) =
      ((chartJac β w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, chartWeight_prod_inv_sqrt_eq_chartJac e hβ v]
  rw [hJ]
  by_cases hv : ∀ x, ‖v x‖ < Real.sqrt β
  · have hpt : (fun x => (φ x : EuclideanSpace ℝ (Fin N))) = chartPoint β e w :=
      chartMapPi_inv_sqrt_eq_chartPoint e he hβ v hv
    have hchd := hchord φ
    have hu : (fun x => (φ x : EuclideanSpace ℝ (Fin N)) - e x) = chartPoint β e w - e := by
      funext x
      have := congrFun hpt x
      simp only [Pi.sub_apply]
      rw [this]
    have hsp := sphereExponent_chartPoint hβ e H hsymm w
    have hsrc := source_chartPoint_complex (β := β) e w g
    have hφx : ∀ x, (φ x : EuclideanSpace ℝ (Fin N)) = chartPoint β e w x :=
      fun x => congrFun hpt x
    have hsrc' : ∑ x, ∑ i : Fin N, g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) =
        (∑ x, ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) +
          (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
            (∑ x, ∑ i : Fin N, g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)) := by
      simpa only [hφx] using hsrc
    have hB : β * Bf φ = β * Bf ec + β * ((1 / 2) * cinner (chartPoint β e w - e)
        (H (chartPoint β e w - e))) := by
      rw [← hu]; linear_combination β * hchd
    unfold sphereExponent chartExponent at hsp
    have hBr : β * Bf φ = β * Bf ec + (cinner w (H (chartShift β e w)) +
        (1 / 2) * cinner (chartShift β e w) (H (chartShift β e w)) +
        (1 / 2) * cinner w (H w)) := by
      rw [hB]; linarith
    have hexp : -((β * Bf φ : ℝ) : ℂ) - ((m * ∑ x, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 :
          ℝ) : ℂ) + ∑ x, ∑ i : Fin N, g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) =
        (((-(1 / 2) * cinner w (H w) : ℝ)) : ℂ) +
          (-((β * Bf ec : ℝ) : ℂ) +
            (∑ x, ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) +
            (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              (∑ x, ∑ i : Fin N, g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)) -
            ((cinner w (H (chartShift β e w)) + (1 / 2) * cinner (chartShift β e w)
              (H (chartShift β e w)) +
              m * ∑ x, ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ)) := by
      rw [hsrc', hBr]
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    ring
  · obtain ⟨x, hx⟩ := not_forall.mp hv
    have hj : chartJac β w = 0 := chartJac_eq_zero (w := w) (x₀ := x) hx
    rw [hj]
    simp

/-- **The chart Gaussian core.**  The integral of `χ K0 exp(-β Bf - m ∑ ‖ψ_x - h‖² + ⟨g, ψ⟩)`
against the product sphere measure, for an action with the exact chord expansion about the unit
background `e`, a cutoff supported in the hemispheres around `e`, and a positive definite Gaussian
form, is the Gaussian prefactor times the standard Gaussian integral of the remainder. -/
theorem chartGaussian_core {β : ℝ} (hβ : 0 < β) (m : ℝ) (e : Config ι N)
    (he : ∀ x, ‖e x‖ = 1) (H : Config ι N →ₗ[ℝ] Config ι N)
    (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v)
    (hK : (LinearMap.toMatrix
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (Pi.basis (fun _ : ι => (EuclideanSpace.basisFun (Fin N) ℝ).toBasis))
      (gaussForm e H)).PosDef)
    (h : EuclideanSpace ℝ (Fin N)) (g : ι → Fin N → ℂ) (K0 : ℂ)
    (χ : (ι → Sph) → ℝ) (hχ : Measurable χ) (hχ1 : ∀ ψ, |χ ψ| ≤ 1)
    (hχs : ∀ ψ : ι → Sph,
      (∃ x, ¬ 0 < inner ℝ (e x) (ψ x : EuclideanSpace ℝ (Fin N))) → χ ψ = 0)
    (Bf : (ι → Sph) → ℝ) (hBf : Continuous Bf) (ec : ι → Sph)
    (hchord : ∀ ψ : ι → Sph, Bf ψ - Bf ec = (1 / 2) *
      cinner (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - e x)
        (H (fun x => (ψ x : EuclideanSpace ℝ (Fin N)) - e x))) :
    ∃ R : Config ι N ≃ₗ[ℝ] Config ι N,
      (∀ w, gaussForm e H (R (R w)) = w) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config ι N →ₗ[ℝ] Config ι N) =
        Real.sqrt (LinearMap.det (gaussForm e H))⁻¹ ∧
      ∫ ψ, chartGaussDensity β m h g K0 χ Bf ψ
          ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
        ((Real.sqrt β)⁻¹ ^ (Fintype.card ι * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card ι / 2) *
            Real.sqrt (LinearMap.det (gaussForm e H))⁻¹ : ℝ) : ℂ) *
            ∫ ψ, chartGaussRem β m e he H h g K0 χ (Bf ec)
              (tangentProj e he (R ψ)) ∂(stdGaussian ι N)) := by
  have hRem := measurable_chartGaussRem (β := β) (m := m) e he H h g K0 χ hχ (Bf ec)
  obtain ⟨R, hRR, hRs, hdet, hnorm⟩ :=
    integral_tangent_gaussian_of_posDef e he H hK
      (chartGaussRem β m e he H h g K0 χ (Bf ec)) hRem
  refine ⟨R, hRR, hRs, hdet, ?_⟩
  -- the density is measurable and bounded
  let Gc : (ι → Sph) → ℂ := fun ψ => K0 * Complex.exp (-((β * Bf ψ : ℝ) : ℂ) -
    ((m * ∑ x, ‖(ψ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
    ∑ x, ∑ i : Fin N, g x i * ((((ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ)) : ℂ))
  have hGc : Continuous Gc := by
    dsimp only [Gc]
    refine continuous_const.mul (Complex.continuous_exp.comp ?_)
    have := hBf
    fun_prop
  have hdens : ∀ ψ, chartGaussDensity β m h g K0 χ Bf ψ = (χ ψ : ℂ) * Gc ψ := by
    intro ψ; simp only [chartGaussDensity, Gc]; ring
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hGc.continuousOn
  have hmeas : Measurable (chartGaussDensity β m h g K0 χ Bf) := by
    have : chartGaussDensity β m h g K0 χ Bf = fun ψ => (χ ψ : ℂ) * Gc ψ := funext hdens
    rw [this]
    exact (Complex.measurable_ofReal.comp hχ).mul hGc.measurable
  have hint : Integrable (chartGaussDensity β m h g K0 χ Bf)
      (Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
    refine Integrable.of_bound (C := C) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ψ => ?_)
    rw [hdens, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |χ ψ| * ‖Gc ψ‖ ≤ 1 * C :=
          mul_le_mul (hχ1 ψ) (hC ψ (Set.mem_univ ψ)) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hsupp : ∀ ψ : ι → Sph,
      (∃ x, ¬ 0 < inner ℝ (e x) (ψ x : EuclideanSpace ℝ (Fin N))) →
        chartGaussDensity β m h g K0 χ Bf ψ = 0 := by
    intro ψ hψ
    rw [hdens, hχs ψ hψ]
    simp
  rw [integral_sphere_pi_hemisphere_complex e he _ hmeas hint hsupp,
    integral_pi_perp_inv_sqrt_smul e he hβ]
  congr 1
  rw [← hnorm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [chartGauss_pointwise hβ m e he H hsymm h g K0 χ Bf ec hchord v, Complex.ofReal_exp]

end

end Balaban.LargeField
