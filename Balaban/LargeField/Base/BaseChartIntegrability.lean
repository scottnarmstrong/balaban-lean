/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.HemispherePi

/-!
# Integrability of the hemisphere chart weights

The chart weight `(1 - |ξ|²)^{-1/2} 1[|ξ| < 1]` of the hemisphere chart (`chartWeight`) is
integrable on the tangent hyperplane `e^⊥`, because its integral is the surface measure of the
open hemisphere (`toSphere_restrict_hemisphere_site`); hence the product of the weights over the
sites is integrable for the product Lebesgue measure.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Balaban.LargeField

open SphereChart

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The chart weight of a hemisphere chart is integrable on the tangent hyperplane. -/
theorem integrable_chartWeight (e : EuclideanSpace ℝ (Fin N)) (he : ‖e‖ = 1) :
    Integrable (chartWeight e) (volume : Measure (perp e)) := by
  have hm : Measurable (chartWeight e) := measurable_chartWeight e
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have h := congrArg (fun m : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) =>
    m Set.univ) (toSphere_restrict_hemisphere_site e he)
  have hmap : Measure.map (hemiPt e he)
      ((volume : Measure (perp e)).withDensity fun ξ => ENNReal.ofReal (chartWeight e ξ))
        Set.univ = ∫⁻ ξ, ENNReal.ofReal (chartWeight e ξ) ∂(volume : Measure (perp e)) := by
    rw [Measure.map_apply (continuous_hemiPt e he).measurable MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfin : (((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere).restrict
      {φ | 0 < inner ℝ e (φ : EuclideanSpace ℝ (Fin N))}) Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact measure_lt_top _ _
  rw [hmap] at h
  unfold HasFiniteIntegral
  have : ∫⁻ ξ, ‖chartWeight e ξ‖ₑ ∂(volume : Measure (perp e)) =
      ∫⁻ ξ, ENNReal.ofReal (chartWeight e ξ) ∂(volume : Measure (perp e)) := by
    refine lintegral_congr fun ξ => ?_
    rw [Real.enorm_eq_ofReal (chartWeight_nonneg e ξ)]
  rw [this, ← h]
  exact hfin

/-- The product of the chart weights over the sites is integrable for the product measure. -/
theorem integrable_chartWeight_prod (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) :
    Integrable (fun ξ : (x : ι) → perp (e x) => ∏ x, chartWeight (e x) (ξ x))
      (Measure.pi fun x => (volume : Measure (perp (e x)))) :=
  Integrable.fintype_prod_dep (f := fun x => chartWeight (e x))
    (fun x => integrable_chartWeight (e x) (he x))

end Balaban.LargeField
