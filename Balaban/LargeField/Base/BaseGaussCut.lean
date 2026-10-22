/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.ChartIntegral
public import Balaban.LargeField.Base.BaseFRWhiteChange
public import Balaban.LargeField.Base.BaseFirstAllGoodWhite
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The standard Gaussian as a product measure, and the truncated product measure

The standard Gaussian `stdGaussian ι N` on `Config ι N` is the product over the sites of the
standard Gaussian `siteGaussian N` on `ℝ^N` (`stdGaussian_eq_pi`). The truncated product measure
`gaussCut p₁` is the product of the site Gaussians restricted to `|φ_x| < p₁` and normalized; the
mass of the truncation is `Z_cut = γ_N{|φ| < p₁}^{|ι|}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Balaban.LargeField

open Balaban.LargeField.Base

noncomputable section

/-- The density `(2π)^{-N/2} e^{-|x|²/2}` of the standard Gaussian on `ℝ^N`. -/
def siteDensity (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2)

/-- The standard Gaussian measure on `ℝ^N`. -/
def siteGaussian (N : ℕ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin N))).withDensity fun x =>
    ENNReal.ofReal (siteDensity N x)

theorem siteDensity_nonneg (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) : 0 ≤ siteDensity N x := by
  unfold siteDensity; positivity

theorem measurable_siteDensity (N : ℕ) : Measurable (siteDensity N) := by
  unfold siteDensity; fun_prop

theorem integrable_siteDensity (N : ℕ) : Integrable (siteDensity N) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin N)) (b := ((1 / 2 : ℝ) : ℂ)) (by simp) 0 0
  have h2 := h.norm
  unfold siteDensity
  refine Integrable.const_mul ?_ _
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem siteGaussian_apply (N : ℕ) {s : Set (EuclideanSpace ℝ (Fin N))} (hs : MeasurableSet s) :
    siteGaussian N s = ENNReal.ofReal (∫ x in s, siteDensity N x) := by
  unfold siteGaussian
  rw [withDensity_apply _ hs, ofReal_integral_eq_lintegral_ofReal
    (integrable_siteDensity N).restrict (Filter.Eventually.of_forall (siteDensity_nonneg N))]

instance (N : ℕ) : IsFiniteMeasure (siteGaussian N) :=
  ⟨by rw [siteGaussian_apply N MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩

theorem stdGaussian_density_eq_prod (ι : Type*) [Fintype ι] (N : ℕ) (ψ : Config ι N) :
    (2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) * Real.exp (-(1 / 2) * cinner ψ ψ) =
      ∏ i, siteDensity N (ψ i) := by
  unfold siteDensity
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  · congr 1
    unfold cinner
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [real_inner_self_eq_norm_sq]

theorem stdGaussian_pi_box (ι : Type*) [Fintype ι] (N : ℕ) (s : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hs : ∀ i, MeasurableSet (s i)) :
    stdGaussian ι N (Set.univ.pi s) = ∏ i, siteGaussian N (s i) := by
  classical
  unfold stdGaussian
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  let f : ι → EuclideanSpace ℝ (Fin N) → ℝ := fun i => (s i).indicator (siteDensity N)
  have hfi : ∀ i, Integrable (f i) := fun i => (integrable_siteDensity N).indicator (hs i)
  have hf0 : ∀ i x, 0 ≤ f i x := fun i x => Set.indicator_nonneg (fun y _ => siteDensity_nonneg N y) x
  have hpt : ∀ ψ : Config ι N, (Set.univ.pi s).indicator
      (fun ψ => ENNReal.ofReal ((2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) *
        Real.exp (-(1 / 2) * cinner ψ ψ))) ψ = ENNReal.ofReal (∏ i, f i (ψ i)) := by
    intro ψ
    by_cases h : ψ ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h, stdGaussian_density_eq_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (Set.indicator_of_mem (h i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem h]
      obtain ⟨i, hi⟩ : ∃ i, ψ i ∉ s i := by
        by_contra hc
        push Not at hc
        exact h fun i _ => hc i
      have : f i (ψ i) = 0 := Set.indicator_of_notMem hi _
      rw [Finset.prod_eq_zero (Finset.mem_univ i) this]
      simp
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hpt]
  have hint : Integrable (fun ψ : Config ι N => ∏ i, f i (ψ i)) := by
    have := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))))
      (f := f) hfi
    simpa [volume_pi] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ψ => Finset.prod_nonneg fun i _ => hf0 i _)]
  have hfub := integral_fintype_prod_eq_prod (μ := fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun i => f i)
  rw [← volume_pi] at hfub
  rw [hfub, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [siteGaussian_apply N (hs i), integral_indicator (hs i)]

/-- **The standard Gaussian on `Config ι N` is the product of the site Gaussians.** -/
theorem stdGaussian_eq_pi (ι : Type*) [Fintype ι] (N : ℕ) :
    stdGaussian ι N = Measure.pi fun _ : ι => siteGaussian N :=
  (Measure.pi_eq (μ' := stdGaussian ι N) fun s hs => (stdGaussian_pi_box ι N s hs)).symm

/-- The standard Gaussian mass `γ_N{|x| < p₁}` of the site truncation. -/
def cutMass (N : ℕ) (p₁ : ℝ) : ℝ≥0∞ := siteGaussian N (Metric.ball 0 p₁)

/-- The site Gaussian restricted to `|x| < p₁` and normalized. -/
def siteCut (N : ℕ) (p₁ : ℝ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  (cutMass N p₁)⁻¹ • (siteGaussian N).restrict (Metric.ball 0 p₁)

/-- **The truncated product measure** `μ_cut`: the product over the sites of the standard Gaussian
on `ℝ^N` restricted to `|φ_x| < p₁` and normalized. -/
def gaussCut (ι : Type*) [Fintype ι] (N : ℕ) (p₁ : ℝ) : Measure (Config ι N) :=
  Measure.pi fun _ : ι => siteCut N p₁

/-- The total mass `Z_cut = γ_N{|φ| < p₁}^{|ι|}` of the truncation. -/
def gaussCutMass (ι : Type*) [Fintype ι] (N : ℕ) (p₁ : ℝ) : ℝ :=
  (cutMass N p₁).toReal ^ Fintype.card ι

theorem cutMass_ne_zero (N : ℕ) {p₁ : ℝ} (hp : 0 < p₁) : cutMass N p₁ ≠ 0 := by
  unfold cutMass
  rw [siteGaussian_apply N Metric.isOpen_ball.measurableSet]
  have : 0 < ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin N)) p₁, siteDensity N x := by
    refine (integral_pos_iff_support_of_nonneg (fun x => siteDensity_nonneg N x)
      (integrable_siteDensity N).restrict).2 ?_
    have hs : Function.support (siteDensity N) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      unfold siteDensity; positivity
    rw [hs, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact Metric.measure_ball_pos _ _ hp
  exact (ENNReal.ofReal_pos.2 this).ne'

theorem cutMass_ne_top (N : ℕ) (p₁ : ℝ) : cutMass N p₁ ≠ ⊤ := measure_ne_top _ _

theorem isProbabilityMeasure_siteCut (N : ℕ) {p₁ : ℝ} (hp : 0 < p₁) :
    IsProbabilityMeasure (siteCut N p₁) :=
  ⟨by
    unfold siteCut
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.inv_mul_cancel (cutMass_ne_zero N hp) (cutMass_ne_top N p₁)⟩

theorem isProbabilityMeasure_gaussCut (ι : Type*) [Fintype ι] (N : ℕ) {p₁ : ℝ} (hp : 0 < p₁) :
    IsProbabilityMeasure (gaussCut ι N p₁) := by
  have := isProbabilityMeasure_siteCut N hp
  unfold gaussCut
  infer_instance

theorem gaussCutMass_pos (ι : Type*) [Fintype ι] (N : ℕ) {p₁ : ℝ} (hp : 0 < p₁) :
    0 < gaussCutMass ι N p₁ :=
  pow_pos (ENNReal.toReal_pos (cutMass_ne_zero N hp) (cutMass_ne_top N p₁)) _

/-- A product of scaled measures is the scaled product. -/
theorem pi_smul_const (ι : Type*) [Fintype ι] {α : Type*} [MeasurableSpace α] {c : ℝ≥0∞}
    (hc : c ≠ ⊤) (ν : Measure α) [IsFiniteMeasure ν] :
    Measure.pi (fun _ : ι => c • ν) = c ^ Fintype.card ι • Measure.pi (fun _ : ι => ν) := by
  have : IsFiniteMeasure (c • ν) := Measure.smul_finite ν hc
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- **The small-fluctuation Gaussian integral in product-measure form** (item 2 of Q15): for
`p₁ > 0` and any `G`,
`∫ 1[∀x, |φ_x| < p₁] e^{-½|φ|²} G(φ) dφ = (2π)^{N|ι|/2} Z_cut ∫ G dμ_cut`. -/
theorem integral_rSmall_gaussian (ι : Type*) [Fintype ι] (N : ℕ) {p₁ : ℝ} (hp : 0 < p₁)
    (G : Config ι N → ℂ) :
    ∫ φ : Config ι N, ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) *
        ((((Real.exp (-(1 / 2) * cinner φ φ)) : ℝ) : ℂ) * G φ) =
      (((2 * Real.pi) ^ (((N * Fintype.card ι : ℕ) : ℝ) / 2) * gaussCutMass ι N p₁ : ℝ) : ℂ) *
        ∫ φ, G φ ∂(gaussCut ι N p₁) := by
  classical
  set S : Set (Config ι N) := Set.univ.pi fun _ => Metric.ball 0 p₁ with hS
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => Metric.isOpen_ball.measurableSet
  have hind : ∀ φ : Config ι N, ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) = S.indicator 1 φ := by
    intro φ
    unfold rSmall
    by_cases h : φ ∈ S
    · rw [Set.indicator_of_mem h]
      simp only [Pi.one_apply, Complex.ofReal_eq_one]
      refine Finset.prod_eq_one fun x _ => ?_
      have : ‖φ x‖ < p₁ := by simpa using h x (Set.mem_univ x)
      simp [this]
    · rw [Set.indicator_of_notMem h]
      obtain ⟨x, hx⟩ : ∃ x, φ x ∉ Metric.ball 0 p₁ := by
        by_contra hc
        push Not at hc
        exact h fun x _ => hc x
      have : ¬ ‖φ x‖ < p₁ := by simpa using hx
      rw [Finset.prod_eq_zero (Finset.mem_univ x) (by simp [this])]
      simp
  set C : ℝ := (2 * Real.pi) ^ (((N * Fintype.card ι : ℕ) : ℝ) / 2) with hC
  set c : ℝ := (2 * Real.pi) ^ (-((N * Fintype.card ι : ℕ) : ℝ) / 2) with hc
  have hCc : (C : ℂ) * (c : ℂ) = 1 := by
    have : C * c = 1 := by
      rw [hC, hc, ← Real.rpow_add (by positivity)]
      have h0 : ((N * Fintype.card ι : ℕ) : ℝ) / 2 + -((N * Fintype.card ι : ℕ) : ℝ) / 2 = 0 := by
        ring
      rw [h0, Real.rpow_zero]
    exact_mod_cast this
  have h1 : ∫ φ : Config ι N, ((rSmall (ι := ι) (N := N) p₁ φ : ℝ) : ℂ) *
      ((((Real.exp (-(1 / 2) * cinner φ φ)) : ℝ) : ℂ) * G φ) =
      (C : ℂ) * ∫ φ, S.indicator G φ ∂(stdGaussian ι N) := by
    rw [FRWhite.integral_stdGaussian_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
    dsimp only
    rw [hind φ]
    by_cases h : φ ∈ S
    · simp only [Set.indicator_of_mem h, Pi.one_apply]
      rw [Complex.ofReal_mul, ← hc]
      linear_combination (-(((Real.exp (-(1 / 2) * cinner φ φ) : ℝ) : ℂ) * G φ)) * hCc
    · simp [Set.indicator_of_notMem h]
  have h2 : ∫ φ, S.indicator G φ ∂(stdGaussian ι N) =
      (cutMass N p₁).toReal ^ Fintype.card ι • ∫ φ, G φ ∂(gaussCut ι N p₁) := by
    have hsc : ∀ _ : ι, (siteGaussian N).restrict (Metric.ball 0 p₁) =
        cutMass N p₁ • siteCut N p₁ := fun _ => by
      unfold siteCut
      rw [smul_smul, ENNReal.mul_inv_cancel (cutMass_ne_zero N hp) (cutMass_ne_top N p₁), one_smul]
    have := isProbabilityMeasure_siteCut N hp
    rw [integral_indicator hSm, stdGaussian_eq_pi, hS, Measure.restrict_pi_pi]
    rw [show (fun _ : ι => (siteGaussian N).restrict (Metric.ball 0 p₁)) =
      fun _ => cutMass N p₁ • siteCut N p₁ from funext hsc]
    rw [pi_smul_const ι (cutMass_ne_top N p₁), integral_smul_measure, ENNReal.toReal_pow]
    rfl
  rw [h1, h2, Complex.real_smul, ← mul_assoc]
  simp only [gaussCutMass, Complex.ofReal_mul, Complex.ofReal_pow]

end

end Balaban.LargeField
