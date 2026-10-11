module

public import Balaban.Frozen.Model.AprioriMeasure
public import Balaban.Frozen.Model.Energy
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite-volume Gibbs expectations

Def-1 (model). The expectation of a real observable in the finite-volume Gibbs state with
density `exp(-β H)` with respect to the a priori measure (P9 p. 494, `⟨·⟩_T`).
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- `⟨F⟩ = ∫ F e^{-βH} / ∫ e^{-βH}`. -/
noncomputable def gibbsExpectation (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (F : (Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℝ) : ℝ :=
  (∫ φ, F φ * Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ) /
    ∫ φ, Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ

end Balaban
