module

public import Balaban.LargeField.R.ActionConvPieces

/-!
# Placement of the mass switch in a converted window piece

P6 p. 14 (2.31) distinguishes the mass convention at the scale `k₀ + 1`.
The following arithmetic locates that scale in the conversion indices of a
piece.  The physical mass comparison at that index also needs the two
backgrounds on a common generating set and the hypotheses of
`massChange_region_bound_cubes`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type*} {S : Set U} {ι : Type*} [Fintype ι]
  {sc : ι → ℕ} {k1 k : ℕ}

/-- The switch `q = k₀ + 1` is among the converted scales of a piece
exactly when the piece begins strictly before `k₀` and the window ends
strictly after `k₀`. -/
theorem PieceWindowSetup.switch_mem_conversion_iff
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (i : ι) (k0 : ℕ) :
    (sc i + 2 ≤ k0 + 1 ∧ k0 + 1 ≤ k) ↔ sc i < k0 ∧ k0 < k := by
  have := W.sc_lt i
  omega

/-- A piece originating at or after `k₀` never crosses the switch while
its `pieceChain` is converted. -/
theorem PieceWindowSetup.no_switch_after_k0
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (i : ι) (k0 : ℕ)
    (hi : k0 ≤ sc i) {q : ℕ} (hq : sc i + 2 ≤ q) : q ≠ k0 + 1 := by
  have := W.sc_lt i
  omega

end Balaban.LargeField.ActionConv
