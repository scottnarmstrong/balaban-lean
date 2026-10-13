/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.LevelRayTower
public import Balaban.Fluctuation.LevelLocalCover

/-!
# The scale record `StepScaleData` of the shared tower (definitions)

The proposition `LevelCovers`, the step `StepTower.step` and the structure `StepScaleData`,
split off from `Balaban.Inhabited.StepTowerScale` so that the general scale record can import
them (the theorems `StepTower.scale` etc. stay in that file).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

/-- The covers of `levelLocalCover` for `d = L = 3`, `N = 2`: for every block `z` the cover
setup, the neighbourhood equality, the connected structure, zero tree length, the read sites and
the block margin; for every source site the same with `x = s.1`. -/
def LevelCovers (N₁ m₁ k : ℕ) [NeZero N₁] (ϱ ϱm : ℝ)
    (Gp : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱm) (m₀ : ℕ) : Prop :=
  (∀ z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))),
      CovSetup Gp m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z))
        (LocalCover.fam m₀ (LocalCover.blockSite k z)) ∧
      (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) ∧
      (∃ (W₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1) × CTorus 3 3 N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube m₀ k (LocalCover.blockSite k z)) ∧
          MeetsOne m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)) W₀ ∧
          bondCost (scaleW 3 m₀ m₁ k) E₀ =
            treeLenCovOne m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z))) ∧
      treeLenCovOne m₀ k (LocalCover.cube m₀ k (LocalCover.blockSite k z)) = 0 ∧
      readSites Hm k z ⊆ ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) ∧
      BlockMargin Gp (LocalCover.nbhdF m₀ (LocalCover.blockSite k z))
        (↑(blockSites 3 3 N₁ m₁ (k + 1) k z) : Set (CTorus 3 3 N₁ m₁ (k + 1))) ∧
      (↑(blockSites 3 3 N₁ m₁ (k + 1) k z) : Set (CTorus 3 3 N₁ m₁ (k + 1))) ⊆
        ↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k z))) ∧
    (∀ s : CTorus 3 3 N₁ m₁ (k + 1) × Fin 2,
      CovSetup Gp m₀ k (LocalCover.cube m₀ k s.1) (LocalCover.fam m₀ s.1) ∧
      (↑(LocalCover.nbhdF m₀ s.1) : Set (CTorus 3 3 N₁ m₁ (k + 1))) =
        X1 Gp m₀ k (LocalCover.fam m₀ s.1) ∧
      (∃ (W₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1)))
        (E₀ : Finset (CTorus 3 3 N₁ m₁ (k + 1) × CTorus 3 3 N₁ m₁ (k + 1))),
        ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube m₀ k s.1) ∧
          MeetsOne m₀ k (LocalCover.fam m₀ s.1) W₀ ∧
          bondCost (scaleW 3 m₀ m₁ k) E₀ =
            treeLenCovOne m₀ k (LocalCover.cube m₀ k s.1)) ∧
      treeLenCovOne m₀ k (LocalCover.cube m₀ k s.1) = 0 ∧
      s.1 ∈ LocalCover.nbhdF m₀ s.1)

namespace StepTower

variable {κmin : ℝ}

/-- The step `hatStepK k T.m₁ hk ν β p₁ T.δ` of the tower `T`. -/
noncomputable abbrev step (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν β p₁ : ℝ) : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁) :=
  hatStepK (N₁ := N₁) k T.m₁ hk ν β p₁ T.δ

end StepTower

/-- **The per-scale package of the tower `T`.**  All fields are stated on the step
`T.step k hk N₁ ν β p₁ = hatStepK k T.m₁ hk ν β p₁ T.δ`. -/
structure StepScaleData {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ)
    [NeZero N₁] (ν β p₁ : ℝ) : Prop where
  core : FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c T.BG
    T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t
  xi : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
    (T.step k hk N₁ ν β p₁).D'
  ray : Nonempty ((T.step k hk N₁ ν β p₁).RayData (2 * p₁))
  cψ_pos : 0 < lvCpsi T.κ T.t (β * 3 ^ k)
  r_pos : 0 < lvR T.κ T.t (β * 3 ^ k) p₁
  fl_radius : Real.sqrt ((2 : ℕ) : ℝ) *
    (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) < T.t
  ray_margin : ((2 : ℝ) * 2 + lvR T.κ T.t (β * 3 ^ k) p₁) * p₁ < lvCpsi T.κ T.t (β * 3 ^ k)
  p_lt : p₁ < 2 * p₁
  covers : LevelCovers N₁ T.m₁ k (rhoSep T.m₁) (rhoSep T.m₁) (lvTop N₁ T.m₁ k (rhoSep T.m₁))
    (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1

end Balaban.Inhabited
