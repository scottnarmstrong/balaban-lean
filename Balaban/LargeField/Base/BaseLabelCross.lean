/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLabelSum
public import Balaban.LargeField.Base.BaseCrossCoef

/-!
# The label of a family of cells depends only on the bases of its cells

The patches `labelJ` of the label of `(x, Cs)` are the cells meeting the ball about `x` and the balls of
radius `9 L^{k+1+m₁}` about the bases of the cells of `Cs`, so the label is the same for a family of
cubes of the cover of a local generating set and its image in the cover of a level set (`labelSet_cubeMap`),
and the label contains these balls (`ball_subset_labelSet`, `seed_subset_labelSet`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Balaban.LargeField Balaban.Fluctuation Balaban.SmallField.Def6 Finset

section Labels

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {m₀ : ℕ} {ϱ ϱl : ℝ}
  {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
theorem labelJ_cubeMap (d0 : ↥(coverOf Gp).cubeIdx) (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    (ρs : ℕ) (Cs : Finset ↥(coverOf Gl).cubeIdx)
    (hmem : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ (coverOf Gp).cubeIdx) :
    labelJ (coverOf Gp) x ρs (Cs.image (crossCubeMap Gl Gp d0)) = labelJ (coverOf Gl) x ρs Cs := by
  unfold labelJ
  congr 1
  ext P
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨i', ⟨i, hi, rfl⟩, hP⟩
    exact ⟨i, hi, by simpa [crossCubeMap_of_mem Gl Gp d0 (hmem i hi)] using hP⟩
  · rintro ⟨i, hi, hP⟩
    exact ⟨crossCubeMap Gl Gp d0 i, ⟨i, hi, rfl⟩, by simpa [crossCubeMap_of_mem Gl Gp d0 (hmem i hi)] using hP⟩

theorem labelSet_cubeMap (d0 : ↥(coverOf Gp).cubeIdx)
    (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (ρs : ℕ) (Cs : Finset ↥(coverOf Gl).cubeIdx)
    (hmem : ∀ i ∈ Cs, (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) ∈ (coverOf Gp).cubeIdx) :
    labelSet (coverOf Gp) m₀ x ρs (Cs.image (crossCubeMap Gl Gp d0)) = labelSet (coverOf Gl) m₀ x ρs Cs := by
  unfold labelSet
  rw [labelJ_cubeMap d0 x ρs Cs hmem]

open Classical in
/-- The ball of radius `9 L^{k+1+m₁}` about the base of a cell of `Cs` lies in the label of `(x, Cs)`. -/
theorem ball_subset_labelSet (hN : L ^ m₀ ∣ N₁) {C : DecCover d L N₁ m₁ (k + 1)}
    {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} {ρs : ℕ} {Cs : Finset ↥C.cubeIdx}
    {i : ↥C.cubeIdx} (hi : i ∈ Cs) {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)}
    (hy : supDist (i : ℕ × Balaban.Localization.CTorus d L N₁ m₁ (k + 1)).2 y ≤ 9 * L ^ (k + 1 + m₁)) :
    y ∈ labelSet C m₀ x ρs Cs :=
  subset_sitesOf_piHull hN _ (Or.inr (Set.mem_iUnion₂.2 ⟨_, Finset.mem_union_right _
    (Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨cbase (L ^ (k + 1 + m₁)) y,
      cbase_mem_ballCells hy, rfl⟩⟩), mem_Pset_cbase y⟩))

/-- The ball of radius `ρs` about `x` lies in the label of `(x, Cs)`. -/
theorem seed_subset_labelSet (hN : L ^ m₀ ∣ N₁) {C : DecCover d L N₁ m₁ (k + 1)}
    {x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} {ρs : ℕ} {Cs : Finset ↥C.cubeIdx}
    {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hy : supDist x y ≤ ρs) :
    y ∈ labelSet C m₀ x ρs Cs :=
  subset_sitesOf_piHull hN _ (seed_subset_hullSet hy)

end Labels

end Balaban.LargeField.Base
