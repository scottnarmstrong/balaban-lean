/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonLocal
public import Balaban.Inhabited.NewLevelCanonMargin

/-!
# Blocks of the margin, distance to a translate

`blk_subset_canonZ`: the blocks (sides at most `L^{k+1}`, nested) of a site of a union of
`L^{k+1}`-cells lie in the union.  `supDist_nsmul_single`: a site and its neighbour at distance `a` in a
coordinate direction are within `a`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Localization Balaban.LargeField Balaban.Background

section Geom

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L]

/-- **The blocks (of side at most `L^{k+1}`) of a site of the margin lie in the margin.** -/
theorem blk_subset_canonZ {Pt : Set (CTorus d L N₁ m₁ (k + 1))} {r : ℕ} {ϱ' : ℝ}
    (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') {n : ℕ} (hn : n ≤ k + 1)
    {z y : CTorus d L N₁ m₁ (k + 1)}
    (hz : z ∈ {y | ∃ x ∈ nearSet r Pt, SameCell (L ^ (k + 1)) y x})
    (hy : y ∈ G.blk n z) : y ∈ {y | ∃ x ∈ nearSet r Pt, SameCell (L ^ (k + 1)) y x} := by
  obtain ⟨x, hx, hzx⟩ := hz
  have hsc : SameCell (L ^ n) y z := sameCell_of_jBlock_eq hn (GeneratingSet.mem_blk.1 hy)
  exact ⟨x, hx, (SameCell.mono (pow_dvd_pow L hn) hsc).trans hzx⟩

theorem supDist_nsmul_single (a : ℕ) (y : CTorus d L N₁ m₁ (k + 1)) (μ : Fin d) :
    supDist (y + a • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1))) y ≤ a := by
  rw [supDist_le_iff]
  intro ν
  rw [cycNorm_le_iff]
  refine ⟨if ν = μ then (a : ℤ) else 0, ?_, ?_⟩
  · split_ifs <;> simp
  · by_cases h : ν = μ <;> simp [h]

end Geom

end Balaban.Inhabited
