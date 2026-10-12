/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.GaussianLift

/-!
# The product of the sphere measures on open hemispheres in chart coordinates

`lintegral_sphere_pi_hemisphere`: the frozen a priori measure `Measure.pi (toSphere volume)` of
the hard-spin model, integrated against a measurable `f ≥ 0` supported in the product of the open
hemispheres `{⟨e_x, φ_x⟩ > 0}`, equals the integral over the tangent coordinates `ξ_x ∈ e_x^⊥`
with density `∏_x (1 - |ξ_x|²)^{-1/2} 1[|ξ_x| < 1]`.  This is `toSphere_eq_graph` (Lemma II.7.4 (a))
for the product measure.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace Balaban.LargeField

open SphereChart

universe u

noncomputable section

variable {ι : Type u} [Fintype ι] {N : ℕ}

/-- The density `(1 - |ξ|²)^{-1/2} 1[|ξ| < 1]` of the surface measure in the chart. -/
def chartWeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E) (ξ : perp e) : ℝ :=
  if ‖ξ‖ < 1 then 1 / Real.sqrt (1 - ‖ξ‖ ^ 2) else 0

theorem measurable_chartWeight {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (e : E) : Measurable (chartWeight e) := by
  unfold chartWeight
  refine Measurable.ite (measurableSet_lt measurable_norm measurable_const) ?_ measurable_const
  fun_prop

theorem chartWeight_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : E)
    (ξ : perp e) : 0 ≤ chartWeight e ξ := by
  unfold chartWeight; split_ifs <;> positivity

theorem toSphere_restrict_hemisphere_site (e : EuclideanSpace ℝ (Fin N)) (he : ‖e‖ = 1) :
    ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere).restrict
        {φ | 0 < inner ℝ e (φ : EuclideanSpace ℝ (Fin N))} =
      Measure.map (hemiPt e he)
        ((volume : Measure (perp e)).withDensity fun ξ => ENNReal.ofReal (chartWeight e ξ)) := by
  rw [toSphere_restrict_hemisphere e he]
  congr 1
  rw [← withDensity_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  funext ξ
  by_cases hξ : ξ ∈ Metric.ball (0 : perp e) 1
  · have : ‖ξ‖ < 1 := by simpa using hξ
    rw [Set.indicator_of_mem hξ]
    simp only [chartWeight, this, ↓reduceIte]
  · have : ¬ ‖ξ‖ < 1 := by simpa using hξ
    rw [Set.indicator_of_notMem hξ]
    simp only [chartWeight, this, ↓reduceIte]
    simp


/-- The product of the chart maps. -/
def chartMapPi (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (ξ : (x : ι) → perp (e x)) : ι → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 :=
  fun x => hemiPt (e x) (he x) (ξ x)

omit [Fintype ι] in
theorem measurable_chartMapPi (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) :
    Measurable (chartMapPi e he) :=
  measurable_pi_iff.2 fun x => ((continuous_hemiPt (e x) (he x)).measurable).comp (measurable_pi_apply x)

/-- **`toSphere_eq_graph`, product form.**  For a measurable function `f` of the spin configuration
`φ ∈ (S^{N-1})^ι` (the frozen model's a priori measure `Measure.pi toSphere`) that vanishes unless
every spin lies in the open hemisphere `⟨e_x, φ_x⟩ > 0`, the integral against the product surface
measure is the integral over the tangent coordinates `ξ_x ∈ e_x^⊥` with the graph densities
`(1 - |ξ_x|²)^{-1/2}`. -/
theorem lintegral_sphere_pi_hemisphere (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (f : (ι → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℝ≥0∞) (hf : Measurable f)
    (hsupp : ∀ φ, (∃ x, ¬ 0 < inner ℝ (e x) (φ x : EuclideanSpace ℝ (Fin N))) → f φ = 0) :
    ∫⁻ φ, f φ ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫⁻ ξ : (x : ι) → perp (e x),
        (∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))) * f (chartMapPi e he ξ)
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  set σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere with hσ
  set H : ι → Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) := fun x =>
    {φ | 0 < inner ℝ (e x) (φ : EuclideanSpace ℝ (Fin N))} with hH
  have hsub : Function.support f ⊆ Set.univ.pi H := by
    intro φ hφ x _
    by_contra hx
    exact hφ (hsupp φ ⟨x, hx⟩)
  rw [← setLIntegral_eq_of_support_subset hsub]
  set ν : (x : ι) → Measure (perp (e x)) := fun x =>
    (volume : Measure (perp (e x))).withDensity fun ξ => ENNReal.ofReal (chartWeight (e x) ξ)
    with hν
  have hsite : ∀ x, σ.restrict (H x) = (ν x).map (hemiPt (e x) (he x)) := fun x =>
    toSphere_restrict_hemisphere_site (e x) (he x)
  have hsf : ∀ x, SigmaFinite ((ν x).map (hemiPt (e x) (he x))) := fun x => by
    rw [← hsite x]; infer_instance
  have hmap : Measure.map (chartMapPi e he) (Measure.pi ν) =
      Measure.pi fun x => σ.restrict (H x) := by
    have := Measure.pi_map_pi (μ := ν) (f := fun x => hemiPt (e x) (he x))
      (fun x => ((continuous_hemiPt (e x) (he x)).measurable).aemeasurable)
    rw [show chartMapPi e he = fun ξ x => hemiPt (e x) (he x) (ξ x) from rfl, this]
    congr 1
    funext x
    exact (hsite x).symm
  have hdens : (Measure.pi ν) = (Measure.pi fun x => (volume : Measure (perp (e x)))).withDensity
      (fun ξ => ∏ x, ENNReal.ofReal (chartWeight (e x) (ξ x))) :=
    pi_withDensity_eq (fun x => (volume : Measure (perp (e x)))) (fun x => chartWeight (e x))
      (fun x => measurable_chartWeight (e x))
  change ∫⁻ φ, f φ ∂((Measure.pi fun _ : ι => σ).restrict (Set.univ.pi H)) = _
  rw [Measure.restrict_pi_pi (μ := fun _ : ι => σ) H, ← hmap, lintegral_map hf (measurable_chartMapPi e he),
    hdens, lintegral_withDensity_eq_lintegral_mul₀]
  · rfl
  · exact (Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_chartWeight (e x)).comp (measurable_pi_apply x))).aemeasurable
  · exact (hf.comp (measurable_chartMapPi e he)).aemeasurable

end

end Balaban.LargeField
