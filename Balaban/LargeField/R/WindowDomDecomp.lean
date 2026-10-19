/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysPieceCells

/-!
# The cell decompositions of the action regions of the window pieces (blocker 4)

The window conversion `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` takes for every piece `i` a
cube and wall decomposition `decomp i` of its action region `X_i` with the weights `1`
(`hwt1`) and with every cube a block of the generating set of the piece, of layer at most
`j_i + 1` (`hcells`).  Such a decomposition exists: the two-layer block decomposition of
`exists_piece_stepDecomp_positive_blocks_cells`, chosen for every piece.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.LargeField.ActionConv

/-- **The decompositions of the action regions of a family of pieces with unit weights and block
cells.**  For every piece `i` of scale `j_i ≥ 1` with the action region `X_i` of sites
`Xfine`, there is a decomposition with all weights `1` such that every cube is a block of the
generating set of the piece, of layer `≤ j_i + 1`. -/
theorem exists_window_decomp {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
    {k0 M K : ℕ} [NeZero M] [NeZero S.L] (g : Geo S n R M) {ι : Type*} (Hl : ι → RegionHistory S n R k0 K)
    (jf : ι → ℕ) (Zc : ∀ i, Finset (Torus S.d (n (jf i + 1))))
    (hZc : ∀ i, Zc i ∈ comps (S.omega (jf i + 1)) ((Hl i).F.Zp (jf i + 1)))
    (hk : ∀ i, jf i + 1 ≤ K) (hj : ∀ i, 1 ≤ jf i)
    (Xc : ∀ i, Region (locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (Hl i) (jf i) (Zc i)) :
    ∃ decomp : ∀ i, StepDecomp (Xc i), (∀ i c, (decomp i).wt c = 1) ∧
      ∀ i c, ∃ x ∈ (Xc i).sites,
        ((decomp i).cube c).sites =
          (locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)).blk
            ((locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)).layerIndex x) x ∧
        (locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)).layerIndex x ≤ jf i + 1 := by
  have h : ∀ i, ∃ Dc : StepDecomp (Xc i), (∀ c, Dc.wt c = 1) ∧
      ∀ c, ∃ x ∈ (Xc i).sites,
        (Dc.cube c).sites =
          (locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)).blk
            ((locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)).layerIndex x) x ∧
        (locGen g (Hl i) (jf i) (Zc i) (hZc i) (hk i)).layerIndex x ≤ jf i + 1 := by
    intro i
    obtain ⟨Dc, -, -, -, -, hone, hcells⟩ :=
      exists_piece_stepDecomp_positive_blocks_cells g (Hl i) (jf i) (Zc i) (hZc i) (hk i) (hj i)
        (Xc i) (hXc i)
    refine ⟨Dc, hone, fun c => ?_⟩
    obtain ⟨x, hx, hxc, hl⟩ := hcells c
    exact ⟨x, hx, hxc, by omega⟩
  choose decomp hw hc using h
  exact ⟨decomp, hw, hc⟩

end Balaban.LargeField
