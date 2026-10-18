/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysCells
public import Balaban.LargeField.R.WindowRegion
public import Balaban.Fluctuation.Theorem42WireLayers

/-!
# Positive two-layer decomposition of an actual quiet piece

The local generating set of a quiet piece has only the `j` and `j+1` layers
on `Xfine`.  Its action region therefore has a canonical positive block-cell
decomposition.  The two cardinalities below count distinct local `j` and
`j+1` blocks.  Comparing them to the `π_j` and `π_{j+1}` counts of P6 p. 14
(2.31) is the remaining geometric count bridge.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation
  Balaban.LargeField.ActionConv

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {k0 M K : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M) (Hl : RegionHistory S n R k0 K)
  (j : ℕ) (Zc : Finset (Torus S.d (n (j + 1))))
  (hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1)))
  (hk : j + 1 ≤ K)

/-- The actual local action region has a positive two-scale cell decomposition.
Its oriented boundary has at most `2d` face slots per cell. -/
theorem exists_piece_stepDecomp_positive_blocks_cells (hj : 1 ≤ j)
    (X : Region (locGen g Hl j Zc hZc hk))
    (hXs : X.sites = Xfine g Hl j Zc) :
    ∃ Dc : StepDecomp X,
      (∀ i, 0 < Dc.wt i) ∧ Dc.inc = 2 * S.d ∧
      Dc.total =
        (((X.sites.filter fun x => (locGen g Hl j Zc hZc hk).layerIndex x = j).image
          fun x => (locGen g Hl j Zc hZc hk).blk j x).card : ℝ) +
        (((X.sites.filter fun x => (locGen g Hl j Zc hZc hk).layerIndex x = j + 1).image
          fun x => (locGen g Hl j Zc hZc hk).blk (j + 1) x).card : ℝ) ∧
      (∀ q, Dc.wall q ⊆ (Dc.cube (Dc.wallCube q)).crossing) ∧
      (∀ i, Dc.wt i = 1) ∧
      (∀ i, ∃ x ∈ X.sites,
        (Dc.cube i).sites = (locGen g Hl j Zc hZc hk).blk
          ((locGen g Hl j Zc hZc hk).layerIndex x) x ∧
        ((locGen g Hl j Zc hZc hk).layerIndex x = j ∨
          (locGen g Hl j Zc hZc hk).layerIndex x = j + 1)) := by
  let G := locGen g Hl j Zc hZc hk
  have htwo : ∀ x ∈ X.sites, G.layerIndex x = j ∨ G.layerIndex x = j + 1 := by
    intro x hx
    have hxX : x ∈ Xfine g Hl j Zc := by rw [← hXs]; exact hx
    have hxj : x ∈ G.Ω j := locGen_Ω_k g Hl j Zc hZc hk hj hxX
    have hx1 : x ∈ G.Ω 1 := G.Ω_antitone le_rfl hj (by omega) hxj
    obtain ⟨h1, hK, hxl⟩ := G.layerIndex_spec hx1
    rcases (layer_mem_iff_of_top G hxj h1 hK).mp hxl with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨Dc, hpos, hinc, hcount, hwall, hone, hcells⟩ :=
    X.exists_stepDecomp_positive_blocks_cells
  refine ⟨Dc, hpos, hinc, ?_, hwall, hone, fun i => ?_⟩
  · rw [hcount]
    exact_mod_cast X.layerBlock_count_two j htwo
  · obtain ⟨x, hx, hxc⟩ := hcells i
    exact ⟨x, hx, hxc, htwo x hx⟩

/-- The actual local action region has a positive two-scale cell decomposition.
Its oriented boundary has at most `2d` face slots per cell. -/
theorem exists_piece_stepDecomp_positive_blocks (hj : 1 ≤ j)
    (X : Region (locGen g Hl j Zc hZc hk))
    (hXs : X.sites = Xfine g Hl j Zc) :
    ∃ Dc : StepDecomp X,
      (∀ i, 0 < Dc.wt i) ∧ Dc.inc = 2 * S.d ∧
      Dc.total =
        (((X.sites.filter fun x => (locGen g Hl j Zc hZc hk).layerIndex x = j).image
          fun x => (locGen g Hl j Zc hZc hk).blk j x).card : ℝ) +
        (((X.sites.filter fun x => (locGen g Hl j Zc hZc hk).layerIndex x = j + 1).image
          fun x => (locGen g Hl j Zc hZc hk).blk (j + 1) x).card : ℝ) ∧
      (∀ q, Dc.wall q ⊆ (Dc.cube (Dc.wallCube q)).crossing) := by
  obtain ⟨Dc, h1, h2, h3, h4, -, -⟩ :=
    exists_piece_stepDecomp_positive_blocks_cells g Hl j Zc hZc hk hj X hXs
  exact ⟨Dc, h1, h2, h3, h4⟩

end Balaban.LargeField
