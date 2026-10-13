/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScale

/-!
# The cover proposition of the step for general `d`, `L` and cover index `m₀`

`LevelCoversG d L N N₁ m₁ k ϱ ϱm Gp Hm m₀` is the proposition `LevelCovers` of the scale record
`StepScaleData` with `3, 3, 2` replaced by `d, L, N`.  `levelCoversG_of_dvd` proves it from
`LocalCover.levelLocalCover` for every cover index `m₀ ≥ 1` with `L ^ m₀ ∣ N₁`; the only
hypothesis on `N₁` is this divisibility.  `levelCoversG_three` states that at `d = L = 3`,
`N = 2` it is the proposition `LevelCovers` (definitionally).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization

/-- The covers of `levelLocalCover` for general `d`, `L`, `N` and cover index `m₀`: for every
block `z` the cover setup, the neighbourhood equality, the connected structure, zero tree length,
the read sites and the block margin; for every source site the same with `x = s.1`. -/
def LevelCoversG (d L N N₁ m₁ k : ℕ) [NeZero N₁] [NeZero L] (ϱ ϱm : ℝ)
    (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) (m₀ : ℕ) : Prop :=
  (∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      CovSetup Gp m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z))
        (LocalCover.fam m₀ (LocalCover.blockSite k z)) ∧
      (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube m₀ k (LocalCover.blockSite k z)) ∧
          MeetsOne m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) W₀ ∧
          bondCost (scaleW L m₀ m₁ k) E₀ =
            treeLenCovOne m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z))) ∧
      treeLenCovOne m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z)) = 0 ∧
      readSites Hm k z ⊆ ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) ∧
      BlockMargin Gp (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
        (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ∧
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
        ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z))) ∧
    (∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      CovSetup Gp m₀ k (LocalCover.cube m₀ k s.1) (LocalCover.fam m₀ s.1) ∧
      (↑(LocalCover.nbhdF m₀ s.1) : Set (CTorus d L N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (LocalCover.fam m₀ s.1) ∧
      (∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube m₀ k s.1) ∧
          MeetsOne m₀ k (LocalCover.fam m₀ s.1) W₀ ∧
          bondCost (scaleW L m₀ m₁ k) E₀ =
            treeLenCovOne m₀ k (LocalCover.cube m₀ k s.1)) ∧
      treeLenCovOne m₀ k (LocalCover.cube m₀ k s.1) = 0 ∧
      s.1 ∈ LocalCover.nbhdF m₀ s.1)

/-- **The general cover proposition.**  For a whole-lattice generating set `Gp` of the top level
`k + 1` with a `DGSetting`, any generating set `Hm`, `m₀ ≥ 1` and `L ^ m₀ ∣ N₁`, the cover
proposition holds.  Divisibility is the only hypothesis on `N₁`. -/
theorem levelCoversG_of_dvd {d L N N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
    {a : ℕ → ℝ} {ν : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) (S : DGSetting Gp a ν)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) :
    LevelCoversG d L N N₁ m₁ k ϱ ϱm Gp Hm m₀ :=
  LocalCover.levelLocalCover (N := N) Hm S hG' hm₀ hN

/-- At `d = L = 3`, `N = 2` the general proposition is `LevelCovers` (the type of the `covers`
field of `StepScaleData`). -/
theorem levelCoversG_three_iff (N₁ m₁ k : ℕ) [NeZero N₁] (ϱ ϱm : ℝ)
    (Gp : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm) (m₀ : ℕ) :
    LevelCoversG 3 3 2 N₁ m₁ k ϱ ϱm Gp Hm m₀ ↔ LevelCovers N₁ m₁ k ϱ ϱm Gp Hm m₀ :=
  Iff.rfl

end Balaban.Inhabited
