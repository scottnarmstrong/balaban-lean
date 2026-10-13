/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootMarkGeom
public import Balaban.Fluctuation.Thm31Inhab

/-!
# Non-vacuity of the root-block geometry on a concrete torus

On the torus of `RootPavingWitness` (`d = 3`, `L = 2`, `N₁ = 2`, `m₀ = m₁ = 0`, `K = 1`, fine side
`4`, cell side `2`): the root `z = 0`, its block `fineBlock z` (non-empty, contained in the box of
`rootCube z`), and a domain `Y` in `𝒟_1` meeting the block that has the root cube among its cubes.
Here the `π′`-cube has side `4`, the side of the torus, so `Y` is the whole torus.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

theorem rootMarkGeom_witness :
    ∃ (z : RootIdx 3 2 2 0 1) (Y : Set (CTorus 3 2 2 0 1)),
      (fineBlock z).Nonempty ∧
      fineBlock z ⊆ box (rootCube (m₀ := 0) z).1 (cellSide 2 0 0 1) ∧
      IsDj (L := 2) (N₁ := 2) (m₁ := 0) (K := 1) 0 1 Y ∧ (Y ∩ fineBlock z).Nonempty ∧
      rootCube (m₀ := 0) z ∈ blocksOf 0 1 Set.univ Y := by
  have hN : (2 : ℕ) ^ 0 ∣ 2 := by norm_num
  have hY : IsDj (L := 2) (N₁ := 2) (m₁ := 0) (K := 1) 0 1
      (Set.univ : Set (CTorus 3 2 2 0 1)) := isDj_univ 3 2 2 0 1 0 1
  have hne : ((Set.univ : Set (CTorus 3 2 2 0 1)) ∩ fineBlock (0 : RootIdx 3 2 2 0 1)).Nonempty :=
    ⟨rootSite 0, Set.mem_univ _, rootSite_mem_fineBlock _⟩
  exact ⟨0, Set.univ, ⟨rootSite 0, rootSite_mem_fineBlock _⟩,
    fineBlock_subset_box_rootCube _, hY, hne, rootCube_mem_blocksOf_of_isDj hN hY hne⟩

end Balaban.Fluctuation
