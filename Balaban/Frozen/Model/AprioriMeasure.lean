module

public import Balaban.Frozen.Model.Torus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The a priori measure of the hard-spin model

Def-1 (model). Hard spins (`λ = ∞`): the spin at each site lies on the unit sphere
`S^{N-1} ⊂ ℝ^N`, and the a priori measure is the product over the sites of the surface measure
on the sphere (the `λ → ∞` limit of P1 (1.5)–(1.6), p. 104, up to a constant factor that cancels
in every normalized quantity).
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- The product over the sites of the torus of the surface measure on the unit sphere
`S^{N-1} ⊂ ℝ^N` (Mathlib's `Measure.toSphere` of Lebesgue measure). -/
noncomputable def aprioriMeasure (d N ℓ : ℕ) [NeZero ℓ] :
    Measure (Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  Measure.pi fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

end Balaban
