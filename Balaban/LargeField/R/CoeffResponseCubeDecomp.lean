/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysPieceCount

/-!
# The cube sites of the decomposition of a quiet piece

`exists_piece_stepDecomp_total_le_cells` refines `exists_piece_stepDecomp_total_le`: the cells of
the decomposition are the layer blocks of the local generating set, each of weight one, each the
block `Δ_ℓ(x)` of a site `x` of the region with `ℓ ∈ {j, j+1}`.  The counting lemmas of
`CoeffResponseBudgetCount` then apply cell by cell, and `Region.layerBlock_card`,
`Region.layerBlock_layerIndex` give the number of sites and the layer of every cell.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation
  Balaban.LargeField.ActionConv Finset

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {k0 M K : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M) (Hl : RegionHistory S n R k0 K)
  (j : ℕ) (Zc : Finset (Torus S.d (n (j + 1))))
  (hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1)))
  (hk : j + 1 ≤ K)

open Classical in
/-- **The cube sites of a quiet piece.**  The decomposition of
`exists_piece_stepDecomp_total_le` can be chosen with every cell of weight one and equal to the
layer block `Δ_ℓ(x)` of a site `x` of the region, `ℓ = j` or `ℓ = j + 1`. -/
theorem exists_piece_stepDecomp_total_le_cells (hj : 1 ≤ j)
    (X : Region (locGen g Hl j Zc hZc hk))
    (hXs : X.sites = Xfine g Hl j Zc) :
    ∃ Dc : StepDecomp X,
      (∀ i, 0 < Dc.wt i) ∧ Dc.inc = 2 * S.d ∧
      Dc.total ≤ (M ^ S.d : ℝ) *
        (((Finset.univ.filter fun y : Torus S.d (n j) =>
          y ∉ (Hl.step j).Z ∧
          blockMap S.L (n (j + 1)) y ∈ Zc ∧
          blockMap S.L (n (j + 1)) y ∉ (Hl.step j).Omega).card : ℝ) +
        ((Finset.univ.filter fun y : Torus S.d (n (j + 1)) =>
          y ∈ Zc ∧ y ∈ (Hl.step j).Omega).card : ℝ)) ∧
      (∀ q, Dc.wall q ⊆ (Dc.cube (Dc.wallCube q)).crossing) ∧
      (∀ i, Dc.wt i = 1) ∧
      (∀ i, ∃ x ∈ X.sites,
        (Dc.cube i).sites = (locGen g Hl j Zc hZc hk).blk
          ((locGen g Hl j Zc hZc hk).layerIndex x) x ∧
        ((locGen g Hl j Zc hZc hk).layerIndex x = j ∨
          (locGen g Hl j Zc hZc hk).layerIndex x = j + 1)) := by
  obtain ⟨Dc, hpos, hinc, hcount, hwall, hone, hcells⟩ :=
    exists_piece_stepDecomp_positive_blocks_cells g Hl j Zc hZc hk hj X hXs
  refine ⟨Dc, hpos, hinc, ?_, hwall, hone, hcells⟩
  rw [hcount]
  have h1 := piece_lower_layerBlock_count_le g Hl j Zc hZc hk X hXs
  have h2 := piece_upper_layerBlock_count_le g Hl j Zc hZc hk X hXs
  have h1' := (Nat.cast_le (α := ℝ)).mpr h1
  have h2' := (Nat.cast_le (α := ℝ)).mpr h2
  push_cast at h1' h2'
  linarith

end Balaban.LargeField

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- A layer block of a region lies in the layer of the site that defines it. -/
theorem Region.layerBlock_layerIndex (X : Region G) {x y : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) (hy : y ∈ G.blk (G.layerIndex x) x) :
    G.layerIndex y = G.layerIndex x :=
  (X.layerBlock_eq_of_mem hx hy).1

/-- A layer block of a region has `L^{ℓ d}` sites, `ℓ` the layer of its defining site. -/
theorem Region.layerBlock_card (X : Region G) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ X.sites) :
    (G.blk (G.layerIndex x) x).card = (L ^ G.layerIndex x) ^ d := by
  obtain ⟨_, hK, _⟩ := G.layerIndex_spec (X.sub_Ω hx)
  exact card_blk G _ hK x

end Balaban.LargeField.ActionConv
