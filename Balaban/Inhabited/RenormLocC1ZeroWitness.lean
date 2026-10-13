/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Fluctuation.RenormLocC1Zero

/-!
# `locC1` at every scale of the shared tower

For a tower `T : StepTower κmin`, at the step `lvTop` of every scale `k ≥ 1`, every torus with
`3 ∣ N₁`, `5 < N₁`, every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1` and every block root `z`: the
localization principle `locC1` of `RenormExpInput` (zero class, `K_loc = 1`).  The constants
`c_K = 2 + 2 K₄ ξ₁` and `r₀ ∈ (0, 1/16]` do not depend on the scale.

`locC2`, `locDφ` and an inhabitant of `RenormExpInput` are NOT proved here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **`locC1` at every scale of the tower.** -/
theorem renLocC1_scale_of_tower {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {κa r₀ : ℝ} (hκa : κa ≤ 2 * T.κdec)
    (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16) (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) :
    HasLocPrinciple (N := 2) (lvTop N₁ T.m₁ k (rhoSep T.m₁))
      (XiCOneReal (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν T.t) r₀
      (renYs (renCube (lvTop N₁ T.m₁ k (rhoSep T.m₁))
          (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
        (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1
        (X1 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1 k (fam 1 (blockSite k z))))
      (renDY (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 1) κa 1
      (fun D _ => bgClass (lvTop N₁ T.m₁ k (rhoSep T.m₁)) ν
        ((2 + 2 * K4 3 3 2 T.BG T.κ * xiC1 3) * T.t) D)
      (fun D φ ξ => renC1On (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν T.t
        (blockSites 3 3 N₁ T.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) := by
  obtain ⟨hC₀⟩ := T.core
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) T.m₁_four hN hν0 hν
  have hHB := bgHyp_lv (k := k) T.m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c
      T.BG T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t :=
    flCore_level_transfer hC₀ hSD (opSetting_lv T.m₁_four hN hν0 hν) (isLevel_lvLow hk)
      isLevel_lvTop hHB
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  exact renLocC1_zero_at hC hatConn_lvTop isLevel_lvTop le_rfl hN3 (by norm_num) (by norm_num)
    T.κ0_nonneg T.κdec_lower T.κ_lower T.κ_one T.κ_log hκa hr₀0 hr₀1 z

end Balaban.Inhabited
