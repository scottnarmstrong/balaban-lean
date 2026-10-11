module

public import Balaban.Frozen.Model.OnePoint

/-!
# The truncated two-point function

Def-1 (model). `G(x, y) = ⟨φ(x) ⊗ φ(y)⟩ - ⟨φ(x)⟩ ⊗ ⟨φ(y)⟩` (P9 p. 494), entrywise.
-/

@[expose] public section

namespace Balaban

/-- The entry `⟨φ_i(x) φ_k(y)⟩ - ⟨φ_i(x)⟩ ⟨φ_k(y)⟩` of the truncated two-point function. -/
noncomputable def twoPointTruncated (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (x y : Torus d ℓ) (i k : Fin N) : ℝ :=
  gibbsExpectation d N ℓ β ν h
      (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i * (φ y : EuclideanSpace ℝ (Fin N)) k)
    - onePoint d N ℓ β ν h x i * onePoint d N ℓ β ν h y k

end Balaban
