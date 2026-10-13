/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FlCoreMono
public import Balaban.Inhabited.StepTowerRenEnd
import Mathlib.Tactic.Linarith

/-!
# The core of the tower at any smaller radii

`StepTower.core` has the radius `t` in both radius slots of `FlCore`; by `FlCore.mono` it holds at
any radii `e, e' ≤ t`, also at every scale of the tower (`StepTowerRen.flCore_scale`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- **The core of the tower at radii `e, e' ≤ t`.** -/
theorem StepTower.core_mono {κmin : ℝ} (T : StepTower κmin) {e e' : ℝ} (he : 0 < e)
    (het : e ≤ T.t) (he' : 0 < e') (he't : e' ≤ T.t) :
    Nonempty (FlCore 2 (Gp T.m₁ (rhoSep T.m₁)) (Hm T.m₁ (rhoSep T.m₁)) 1 nuW T.c T.BG T.κ e
      (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ e') := by
  obtain ⟨h⟩ := T.core
  exact ⟨h.mono he het he' he't⟩

/-- **`StepTowerRen.flCore_scale` at radii `e, e' ≤ t`.** -/
theorem StepTowerRen.flCore_scale_mono {κmin : ℝ} (R : StepTowerRen κmin) (k : ℕ) (hk : 1 ≤ k)
    (N₁ : ℕ) [NeZero N₁] (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) {e e' : ℝ} (he : 0 < e) (het : e ≤ R.t) (he' : 0 < e')
    (he't : e' ≤ R.t) :
    FlCore 2 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (lvLow N₁ R.m₁ k (rhoSep R.m₁)) 1 ν R.c
      R.BG R.κ e (levelKc 3 3) (Cchi 3 3) R.c₂ R.BG₂ e' :=
  (R.flCore_scale k hk N₁ hN hν0 hν).mono he het he' he't

end Balaban.Inhabited
