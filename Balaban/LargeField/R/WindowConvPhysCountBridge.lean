/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysPieceCells
public import Balaban.LargeField.Budget.Counts
public import Balaban.LargeField.R.ChiBridgeHist
public import Balaban.Multiscale.ConstraintComm

/-!
# Comparing layer blocks with physical cubes

The positive block decomposition counts the fine `L^q` layer blocks.  A physical
`π_q` cube contains at most `M^d` such blocks.  This is the finite geometric
comparison used when the analytic P6 (2.31) charge is assigned to layer cells.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.LargeField Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ K ϱ}

/-- A family of layer-`q` blocks whose sites project into `A` has at most
`M^d |A|` cells.  The condition on `A` is the exact geometric content needed
from the history; no estimate of the action is part of this theorem. -/
theorem Region.layerBlock_count_le_physical_cubes (X : Region G)
    {q M n : ℕ} [NeZero M] [NeZero n]
    (hmod : N₀ * L ^ (K - q) = M * n) (A : Finset (Torus d n))
    (hA : ∀ x ∈ X.sites, G.layerIndex x = q →
      blockMap M n (torusCast hmod (jBlock d L N₀ K q x)) ∈ A) :
    ((X.sites.filter fun x => G.layerIndex x = q).image fun x => G.blk q x).card ≤
      M ^ d * A.card := by
  classical
  let F := X.sites.filter fun x => G.layerIndex x = q
  let B := F.image fun x => jBlock d L N₀ K q x
  have hblocks : (F.image fun x => G.blk q x) =
      B.image (fun y => blockFibre (L ^ q) (N₀ * L ^ (K - q)) y) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    exact blk_eq_fibre G q x
  have hB : B.image (torusCast hmod) ⊆
      (Finset.univ.filter fun y : Torus d (M * n) => blockMap M n y ∈ A) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxX, hxq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA x hxX hxq⟩
  calc
    (F.image fun x => G.blk q x).card ≤ B.card := by
      rw [hblocks]
      exact Finset.card_image_le
    _ = (B.image (torusCast hmod)).card := by
      exact (Finset.card_image_of_injective B (torusCast_injective hmod)).symm
    _ ≤ (Finset.univ.filter fun y : Torus d (M * n) => blockMap M n y ∈ A).card :=
      Finset.card_le_card hB
    _ = M ^ d * A.card := card_preimage_blockMap rfl A

/-- The quotient of a layer block by the physical cube size is the physical
`π_q` cube containing the original fine site. -/
theorem layerBlock_physical_cube (q M n : ℕ) [NeZero M] [NeZero n]
    (hq : q ≤ K) (hmod : N₀ * L ^ (K - q) = M * n)
    (x : Torus d (N₀ * L ^ K)) :
    blockMap M n (torusCast hmod (jBlock d L N₀ K q x)) =
      blockMap (L ^ q * M) n x := by
  rw [torusCast_blockMap]
  exact blockMap_comp (Multiscale.side_eq hq) hmod x

/-- A physical-cube membership test on the fine sites is sufficient for the
`M^d` bound on the positive layer-block count. -/
theorem Region.layerBlock_count_le_cubeMap (X : Region G)
    {q M n : ℕ} [NeZero M] [NeZero n] (hq : q ≤ K)
    (hmod : N₀ * L ^ (K - q) = M * n) (A : Finset (Torus d n))
    (hA : ∀ x ∈ X.sites, G.layerIndex x = q →
      blockMap (L ^ q * M) n x ∈ A) :
    ((X.sites.filter fun x => G.layerIndex x = q).image fun x => G.blk q x).card ≤
      M ^ d * A.card := by
  apply X.layerBlock_count_le_physical_cubes hmod A
  intro x hx hqx
  rw [layerBlock_physical_cube q M n hq hmod x]
  exact hA x hx hqx

end Balaban.LargeField.ActionConv
