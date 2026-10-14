/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseConstrainedCov
public import Balaban.Localization.Decoupled2Self

/-!
# The x-variant standing data is inhabited at the first step

`base_xCover_exists`: `Dec2.XCover (coverOf G) G a 1 ν (Cchi d L)` holds at `k = 0` (one layer,
the whole level), with `a_0 = 1` and `a_1 = compWeight L 1 1 = 1`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization

/-- **`XCover` is inhabited at the first step `k = 0`.**  The weights are those of
`baseDGSetting_exists` with `a_0` set to `1`, so that `1/2 ≤ a_0 ≤ 2`. -/
theorem base_xCover_exists {d L N₁ m₁ : ℕ} [NeZero L] [NeZero N₁] (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hN₁ : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ 2 ≤ 1) :
    ∃ (G : GeneratingSet d L (N₁ * L ^ m₁) 1 (Inhabited.LevelStep.rhoSepG d L m₁))
      (a : ℕ → ℝ), Dec2.XCover (coverOf G) G a 1 ν (Cchi d L) := by
  obtain ⟨G, -, S⟩ := baseDGSetting_exists (m₁ := m₁) (N₁ := N₁) hd hL hM hN₁ hν0 hν
  have hL2 : 2 ≤ L := by omega
  refine ⟨G, Function.update (Background.compWeight L 1) 0 1, ?_⟩
  have hw : IsAdmissibleWeights 1 (Function.update (Background.compWeight L 1) 0 1) := by
    intro j h1 h2
    rw [Function.update_of_ne (by omega)]
    exact S.weights j h1 h2
  refine Dec2.xCover_self (k := 0) (aT := 1)
    { dg := { S with weights := hw }
      hak1 := by rw [Function.update_self]; norm_num
      hak2 := by rw [Function.update_self]; norm_num
      haT1 := by norm_num
      haT2 := by norm_num }
end Balaban.LargeField.Base
