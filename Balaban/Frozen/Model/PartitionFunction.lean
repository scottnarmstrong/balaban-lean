module

public import Balaban.Frozen.Model.AprioriMeasure
public import Balaban.Frozen.Model.Energy
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The partition function with a source

Def-1 (model). P9 (1.1) (p. 493), P1 p. 108: the source term `⟨g, φ⟩ = ∑_x ∑_i g_i(x) φ_i(x)`
with a complex source `g`, added to the exponent. `log (Z(g)/Z(0))` is the generating functional
of the connected correlation functions.
-/

@[expose] public section

namespace Balaban

open MeasureTheory

/-- `Z(g) = ∫ exp(-β H(φ) + ∑_x ∑_i g_i(x) φ_i(x)) ∏_x dσ(φ_x)`. -/
noncomputable def partitionFunction (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  ∫ φ, Complex.exp (-((β * energy d N ℓ ν h φ : ℝ) : ℂ)
      + ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    ∂aprioriMeasure d N ℓ

end Balaban
