/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.HemispherePi
public import Balaban.LargeField.Base.BasePhysicalDensity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-!
# The hemisphere chart identity for complex integrands, and the first renormalization step

* `integral_sphere_pi_hemisphere_complex`: for a complex integrable `F` on the spin configurations
  that vanishes unless every spin lies in the open hemisphere around the unit vector `e_x`,
  `∫ F dσ^ι = ∫ ∏_x (1 - |ξ_x|²)^{-1/2} 1[|ξ_x|<1] · F(Φ_e(ξ)) dξ`, with the unnormalized product of
  surface measures on the left and Lebesgue measure on `∏ e_x^⊥` on the right.
* `base_goodIntegral_eq_chartIntegral`: the instance for the block-averaged density of the first
  step with the cutoff `χ` supported in the hemispheres.
* `basePhysicalDensity_chart_split`: the frozen partition function as the integral over the coarse
  variables of the bad part plus the chart part.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Balaban.LargeField

open SphereChart

noncomputable section

section General

variable {ι : Type*} [Fintype ι] {N : ℕ}

local notation "Sph" => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

private lemma chart_lintegral_eq (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (f : (ι → Sph) → ℝ≥0∞) (hf : Measurable f)
    (hsupp : ∀ φ, (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → f φ = 0) :
    ∫⁻ φ, f φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫⁻ φ, f φ ∂(Measure.map (chartMapPi e he)
        ((Measure.pi fun x => (volume : Measure (perp (e x)))).withDensity
          (fun ξ => ∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))))) := by
  rw [lintegral_sphere_pi_hemisphere e he f hf hsupp, lintegral_map hf (measurable_chartMapPi e he),
    lintegral_withDensity_eq_lintegral_mul₀]
  · rfl
  · exact (Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_chartWeight (e x)).comp (measurable_pi_apply x))).aemeasurable
  · exact (hf.comp (measurable_chartMapPi e he)).aemeasurable

private lemma chart_integral_real (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (f : (ι → Sph) → ℝ) (hf : Measurable f)
    (hint : Integrable f (Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere))
    (hsupp : ∀ φ, (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → f φ = 0) :
    ∫ φ, f φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫ φ, f φ ∂(Measure.map (chartMapPi e he)
        ((Measure.pi fun x => (volume : Measure (perp (e x)))).withDensity
          (fun ξ => ∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))))) := by
  have hn : ∫⁻ φ, ‖f φ‖ₑ ∂(Measure.map (chartMapPi e he)
        ((Measure.pi fun x => (volume : Measure (perp (e x)))).withDensity
          (fun ξ => ∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))))) < ∞ := by
    rw [← chart_lintegral_eq e he _ hf.enorm (fun φ h => by simp [hsupp φ h])]
    exact hint.2
  have hint' : Integrable f (Measure.map (chartMapPi e he)
        ((Measure.pi fun x => (volume : Measure (perp (e x)))).withDensity
          (fun ξ => ∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))))) :=
    ⟨hf.aestronglyMeasurable, hn⟩
  have h1 := chart_lintegral_eq e he (fun φ => ENNReal.ofReal (f φ))
    (ENNReal.measurable_ofReal.comp hf) (fun φ h => by simp [hsupp φ h])
  have h2 := chart_lintegral_eq e he (fun φ => ENNReal.ofReal (-f φ))
    (ENNReal.measurable_ofReal.comp hf.neg) (fun φ h => by simp [hsupp φ h])
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint', h1, h2]

/-- **The chart identity for complex integrands.**  For a complex integrable `F` on the spin
configurations (product of the surface measures on the spheres) vanishing unless every spin lies in
the open hemisphere `⟨e_x, φ_x⟩ > 0`, the integral equals the integral over the tangent coordinates
`ξ_x ∈ e_x^⊥` with the weights `(1 - |ξ_x|²)^{-1/2} 1[|ξ_x| < 1]`.  There is no normalization
constant. -/
theorem integral_sphere_pi_hemisphere_complex (e : ι → EuclideanSpace ℝ (Fin N))
    (he : ∀ x, ‖e x‖ = 1) (F : (ι → Sph) → ℂ) (hF : Measurable F)
    (hint : Integrable F (Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere))
    (hsupp : ∀ φ, (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → F φ = 0) :
    ∫ φ, F φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫ ξ : (x : ι) → perp (e x),
        (∏ x, ((chartWeight (e x) (ξ x) : ℝ) : ℂ)) * F (chartMapPi e he ξ)
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  have hre := chart_integral_real e he (fun φ => (F φ).re) (Complex.measurable_re.comp hF)
    (hint.re) (fun φ h => by simp [hsupp φ h])
  have him := chart_integral_real e he (fun φ => (F φ).im) (Complex.measurable_im.comp hF)
    (hint.im) (fun φ h => by simp [hsupp φ h])
  set m := Measure.map (chartMapPi e he)
        ((Measure.pi fun x => (volume : Measure (perp (e x)))).withDensity
          (fun ξ => ∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x)))) with hm
  have hmint : Integrable F m := by
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    have := hint.2
    unfold HasFiniteIntegral at this ⊢
    rw [hm, ← chart_lintegral_eq e he _ hF.enorm (fun φ h => by simp [hsupp φ h])]
    exact this
  have hC : ∫ φ, F φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
      = ∫ φ, F φ ∂m := by
    apply Complex.ext
    · have := integral_re hint; have := integral_re hmint; simp_all
    · have := integral_im hint; have := integral_im hmint; simp_all
  rw [hC, hm, integral_map (measurable_chartMapPi e he).aemeasurable hF.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Complex.real_smul]
    congr 2
    rw [ENNReal.toReal_prod]
    simp [Complex.ofReal_prod, ENNReal.toReal_ofReal (chartWeight_nonneg _ _)]
  · exact (Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_chartWeight (e x)).comp (measurable_pi_apply x))).aemeasurable
  · exact Filter.Eventually.of_forall fun ξ =>
      (ENNReal.prod_lt_top fun x _ => ENNReal.ofReal_lt_top)

/-- **The chart identity with a cutoff.**  `χ` is a measurable real cutoff vanishing unless every
spin lies in its hemisphere, and `F` is bounded and measurable. -/
theorem integral_sphere_pi_hemisphere_cutoff (e : ι → EuclideanSpace ℝ (Fin N))
    (he : ∀ x, ‖e x‖ = 1) (χ : (ι → Sph) → ℝ) (hχ : Measurable χ) (hχ1 : ∀ φ, |χ φ| ≤ 1)
    (hsupp : ∀ φ, (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → χ φ = 0)
    (F : (ι → Sph) → ℂ) (hF : Measurable F) (C : ℝ) (hC : ∀ φ, ‖F φ‖ ≤ C) :
    ∫ φ, (χ φ : ℂ) * F φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫ ξ : (x : ι) → perp (e x),
        (∏ x, ((chartWeight (e x) (ξ x) : ℝ) : ℂ)) * ((χ (chartMapPi e he ξ) : ℂ) * F (chartMapPi e he ξ))
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  refine integral_sphere_pi_hemisphere_complex e he (fun φ => (χ φ : ℂ) * F φ)
    (Complex.measurable_ofReal.comp hχ |>.mul hF) ?_ (fun φ h => by simp [hsupp φ h])
  refine Integrable.of_bound (C := C) ((Complex.measurable_ofReal.comp hχ |>.mul hF).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun φ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |χ φ| * ‖F φ‖ ≤ 1 * C := mul_le_mul (hχ1 φ) (hC φ) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

end General

section Base

variable {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]

/-- The spin integrand `χ(φ) K(θ, φ) exp(-β H(φ) + ⟨g, φ⟩)` integrated against the a priori
measure. -/
def baseGoodIntegral (d N L n : ℕ) [NeZero L] [NeZero n] (β a ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (χ : CfgT d N L n → ℝ) : ℂ :=
  ∫ φ, (χ φ : ℂ) * ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
    Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
      + ∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) ∂aprioriMeasure d N (L * n)

/-- The same integrand in the hemisphere chart around `e`, with the chart weights. -/
def baseChartIntegral (d N L n : ℕ) [NeZero L] [NeZero n] (β a ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (χ : CfgT d N L n → ℝ) (e : Torus d (L * n) → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) : ℂ :=
  ∫ ξ : (x : Torus d (L * n)) → perp (e x),
    (∏ x, ((chartWeight (e x) (ξ x) : ℝ) : ℂ)) *
      ((χ (chartMapPi e he ξ) : ℂ) * ((baseKernel d N L n β a θ (chartMapPi e he ξ) : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h (chartMapPi e he ξ) : ℝ) : ℂ)
          + ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((chartMapPi e he ξ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
    ∂(Measure.pi fun x => (volume : Measure (perp (e x))))

omit [NeZero N] in
private lemma baseKernel_le {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) :
    baseKernel d N L n β a θ φ ≤
      ∏ _y : Torus d n, ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) := by
  unfold baseKernel
  refine Finset.prod_le_prod₀ (fun y _ => gaussT_nonneg N _ (baseKernel_pos hβ ha).le _ _) (fun y _ => ?_)
  unfold gaussT
  have : 0 ≤ ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) :=
    Real.rpow_nonneg (div_nonneg (baseKernel_pos hβ ha).le (by positivity)) _
  have hexp : Real.exp (-((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / 2) * ‖θ y - baseQ d N L n φ y‖ ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have := sq_nonneg ‖θ y - baseQ d N L n φ y‖
    have h2 := (baseKernel_pos (d := d) (L := L) hβ ha).le
    nlinarith
  exact mul_le_of_le_one_right this hexp

/-- Measurability and a bound for the full spin integrand (kernel times Boltzmann factor). -/
private lemma kernel_boltz_bound {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Measurable (fun φ : CfgT d N L n => ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) ∧
    ∃ C : ℝ, ∀ φ, ‖((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))‖ ≤ C := by
  obtain ⟨hm, C, hC⟩ := spin_integrand_bound (L := L) (n := n) β ν h g
  have hk : Measurable fun φ : CfgT d N L n => baseKernel d N L n β a θ φ :=
    by
      have := (measurable_baseKernel (n := n) (L := L) (N := N) β a 1).comp
        (measurable_const (a := θ).prodMk measurable_id)
      simpa [Function.comp_def] using this
  refine ⟨(Complex.measurable_ofReal.comp hk).mul hm,
    (∏ _y : Torus d n, ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2)) * C,
    fun φ => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (baseKernel_nonneg hβ ha _ _)]
  exact mul_le_mul (baseKernel_le hβ ha θ φ) (hC φ) (norm_nonneg _)
    (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg
      (div_nonneg (baseKernel_pos hβ ha).le (by positivity)) _)

/-- **The good part of the first step in chart variables.**  With a fixed centre `e` of unit
vectors and a measurable cutoff `χ` (values in `[-1, 1]`, in practice `{0,1}`) vanishing unless every
spin lies in its open hemisphere, the spin integral of `χ K(θ, ·) exp(-βH + ⟨g, ·⟩)` against the a
priori measure is the integral of the same integrand over the chart variables, with the weights
`∏ (1 - |ξ_x|²)^{-1/2} 1[|ξ_x| < 1]`. -/
theorem baseGoodIntegral_eq_baseChartIntegral {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (χ : CfgT d N L n → ℝ) (hχ : Measurable χ)
    (hχ1 : ∀ φ, |χ φ| ≤ 1) (e : Torus d (L * n) → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (hsupp : ∀ φ, (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → χ φ = 0) :
    baseGoodIntegral d N L n β a ν h g θ χ = baseChartIntegral d N L n β a ν h g θ χ e he := by
  obtain ⟨hm, C, hC⟩ := kernel_boltz_bound (L := L) (n := n) hβ ha ν h g θ
  have := integral_sphere_pi_hemisphere_cutoff e he χ hχ hχ1 hsupp _ hm C hC
  unfold baseGoodIntegral baseChartIntegral aprioriMeasure
  simpa only [mul_assoc] using this

/-- **The first step, good/bad decomposition.**  For every family of measurable cutoffs `χ θ` and
centres `e θ` of unit vectors, with `χ θ` vanishing outside the open hemispheres around `e θ`,
the frozen partition function is the integral over the coarse variables of `z₁^D` times the bad
spin integral (factor `1 - χ`) plus the chart integral of the good part. -/
theorem partitionFunction_eq_integral_bad_add_chart {β a z₁ : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hz : 0 < z₁) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (χ : (Torus d n → EuclideanSpace ℝ (Fin N)) → CfgT d N L n → ℝ) (hχ : ∀ θ, Measurable (χ θ))
    (hχ1 : ∀ θ φ, |χ θ φ| ≤ 1)
    (e : (Torus d n → EuclideanSpace ℝ (Fin N)) → Torus d (L * n) → EuclideanSpace ℝ (Fin N))
    (he : ∀ θ x, ‖e θ x‖ = 1)
    (hsupp : ∀ θ φ, (∃ x, ¬ 0 < inner ℝ (e θ x) (φ x : EuclideanSpace ℝ (Fin N))) → χ θ φ = 0) :
    partitionFunction d N (L * n) β ν h g =
      ∫ ψ : Torus d n → EuclideanSpace ℝ (Fin N),
        ((z₁ ^ (N * Fintype.card (Torus d n)) : ℝ) : ℂ) *
          ((∫ φ, ((1 - χ (z₁ • ψ) φ : ℝ) : ℂ) * ((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) *
              Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
                + ∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
              ∂aprioriMeasure d N (L * n)) +
            baseChartIntegral d N L n β a ν h g (z₁ • ψ) (χ (z₁ • ψ)) (e (z₁ • ψ)) (he _))
        ∂(Measure.pi fun _ => volume) := by
  rw [basePhysicalDensity hβ ha hz h g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  simp only
  rw [← baseGoodIntegral_eq_baseChartIntegral hβ ha ν h g _ _ (hχ _) (hχ1 _) _ (he _) (hsupp _)]
  unfold baseRho1 baseGoodIntegral
  congr 1
  obtain ⟨hm, C, hC⟩ := kernel_boltz_bound (L := L) (n := n) hβ ha ν h g (z₁ • ψ)
  have hi : Integrable (fun φ : CfgT d N L n => ((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) (aprioriMeasure d N (L * n)) :=
    Integrable.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hχi : Integrable (fun φ : CfgT d N L n => (χ (z₁ • ψ) φ : ℂ) * (((baseKernel d N L n β a (z₁ • ψ) φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ)
        + ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))) (aprioriMeasure d N (L * n)) := by
    refine Integrable.of_bound (C := C) ((Complex.measurable_ofReal.comp (hχ _)).mul hm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun φ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ 1 * C := mul_le_mul (hχ1 _ _) (hC φ) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  rw [← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  · exact (hi.sub hχi).congr (Filter.Eventually.of_forall fun φ => by
      simp only [Complex.ofReal_sub, Complex.ofReal_one, Pi.sub_apply]; ring)
  · exact hχi.congr (Filter.Eventually.of_forall fun φ => by simp only [mul_assoc])

end Base

end

end Balaban.LargeField
