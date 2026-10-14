/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Model.AprioriMeasure
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Disintegration of the a priori measure over a retained set of sites

For any set `ret` of sites of the torus, the product sphere measure splits as the product of the
product sphere measures over `ret` and over its complement; for an integrable complex function
the integral is the iterated integral over the retained spins and then the remaining spins,
evaluated at the spin configuration that equals the retained one on `ret` and the other one off
`ret`. The case of a union of complete blocks is a special case.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory

/-- Integral of a complex integrable function against the a priori measure, split as an
iterated integral over the spins on a set `ret` of sites and the spins on its complement. -/
theorem baseRetained_disintegrate (d N L n : ℕ) [NeZero (L * n)]
    (ret : Set (Torus d (L * n))) [DecidablePred (· ∈ ret)]
    (f : (Torus d (L * n) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℂ)
    (hf : Integrable f (aprioriMeasure d N (L * n))) :
    ∫ φ, f φ ∂(aprioriMeasure d N (L * n)) =
      ∫ φ_ret : (↥ret → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
        ∫ φ_int : (↥retᶜ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
          f (fun x => if h : x ∈ ret then φ_ret ⟨x, h⟩ else φ_int ⟨x, h⟩)
        ∂(Measure.pi fun _ : ↥retᶜ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
      ∂(Measure.pi fun _ : ↥ret => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  set μ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere with hμ
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : Torus d (L * n) => μ)
    (fun x => x ∈ ret)
  have hsymm := hmp.symm
  have key : ∀ z : (↥ret → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) ×
      (↥retᶜ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Torus d (L * n) => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
        (fun x => x ∈ ret)).symm z =
        (fun x => if h : x ∈ ret then z.1 ⟨x, h⟩ else z.2 ⟨x, h⟩) := by
    intro z; funext x
    by_cases h : x ∈ ret <;> simp [MeasurableEquiv.piEquivPiSubtypeProd, h]
  have hf' : Integrable (f ∘ (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Torus d (L * n) => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
      (fun x => x ∈ ret)).symm)
      ((Measure.pi fun _ : ↥ret => μ).prod (Measure.pi fun _ : ↥retᶜ => μ)) := by
    have := hsymm.integrable_comp_of_integrable (g := f) (by simpa [aprioriMeasure, hμ] using hf)
    exact this
  have h1 : ∫ φ, f φ ∂(aprioriMeasure d N (L * n)) =
      ∫ z, f ((MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Torus d (L * n) => Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
        (fun x => x ∈ ret)).symm z)
        ∂((Measure.pi fun _ : ↥ret => μ).prod (Measure.pi fun _ : ↥retᶜ => μ)) := by
    exact (hsymm.integral_comp' (g := f)).symm
  rw [h1]
  have h2 := integral_prod _ hf'
  simp only [Function.comp, key] at h2
  exact h2

end Balaban.LargeField
