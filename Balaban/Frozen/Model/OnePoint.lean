module

public import Balaban.Frozen.Model.GibbsExpectation

/-!
# The one-point function

Def-1 (model). `M(x) = ⟨φ(x)⟩` (P9 p. 494), componentwise.
-/

@[expose] public section

namespace Balaban

/-- The component `⟨φ_i(x)⟩` of the one-point function. -/
noncomputable def onePoint (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (x : Torus d ℓ) (i : Fin N) : ℝ :=
  gibbsExpectation d N ℓ β ν h fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i

end Balaban
