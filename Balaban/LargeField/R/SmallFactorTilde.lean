module

public import Balaban.LargeField.LF1.Setup

/-!
# The one-scale small-field space `Ψ̃_k(X; δ)` (P7 p. 501)

`PsiTildeSet T f δ`: `|f(y) - f(y')| < δ` for the bonds `{y, y'}` of the lattice of blocks with both
end points in `T`, and `||f(y)| - 1| < δ` for `y ∈ T`.  For the `k`-blocks of the level-`k` torus
(or of the history torus) this is `ψ_k ∈ Ψ̃_k(X; δ)` of Definition III.5.1 item 1.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

/-- `f ∈ Ψ̃(T; δ)` on a set `T` of blocks of the block lattice `Torus d m`. -/
def PsiTildeSet {d m Nspin : ℕ} (T : Set (Torus d m)) (f : Torus d m → EuclideanSpace ℝ (Fin Nspin))
    (δ : ℝ) : Prop :=
  (∀ y ∈ T, ∀ y' ∈ T, AdjT y y' → ‖f y - f y'‖ < δ) ∧ ∀ y ∈ T, |‖f y‖ - 1| < δ

end Balaban.LargeField
