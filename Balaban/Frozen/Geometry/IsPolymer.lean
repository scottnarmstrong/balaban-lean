module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation

/-!
# Polymers

Def-2 (geometry). At scale `j` the torus is partitioned into the blocks of side `s = M L^j`,
`{x : ⌊x_μ / s⌋ = c_μ for all μ}` (P1 p. 117: the partitions "determined by the lattices
`L^j M ℤ^d`"). A polymer is a nonempty union of blocks that is connected for the
nearest-neighbour adjacency of the torus. This class contains P1's localization domains `𝒟_j`
(P1 (2.26), connected unions of overlapping `LM`-cubes); the size of a polymer is measured by
its number of blocks `|X| / s^d`, which is comparable to P1's tree length `d_j(X)` (P1 (2.27))
up to constants depending on `d` and `L` (`notes/phase0/surface-v1-audit.md` §C.4).
-/

@[expose] public section

namespace Balaban

/-- `X` is a polymer of block side `s`: a nonempty union of blocks of side `s` that is
connected for the nearest-neighbour adjacency of the torus. -/
def IsPolymer (d ℓ s : ℕ) [NeZero ℓ] (X : Finset (Torus d ℓ)) : Prop :=
  X.Nonempty ∧
  (∀ x ∈ X, ∀ y : Torus d ℓ, (∀ μ, (x μ).val / s = (y μ).val / s) → y ∈ X) ∧
  ∀ x ∈ X, ∀ y ∈ X, Relation.ReflTransGen
    (fun a b => a ∈ X ∧ b ∈ X ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1) x y

end Balaban
