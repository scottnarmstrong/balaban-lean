/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.StepTowerRenG
public import Balaban.Inhabited.TowerCoreRatesGeneral
public import Balaban.Fluctuation.DetRateGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The producer of the general numerical tower

`exists_stepTowerG` shows that `StepTowerG d L N κmin` is inhabited for every cover index `m₀ ≥ 1`
and every requested output-rate floor: the rates `κ₀`, `κ_dec`, `κ'` are chosen first, then the
interpolation rate `κ` is taken above every lower bound it has to meet (the requested `κmin`,
the determinant margins at the chosen `κ'`, and the cover-index condition at `m₀`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

/-- **The general tower is inhabited**, with cover index `m₀` and output-rate floor
`entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`. -/
theorem exists_stepTowerG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec := by
  obtain ⟨T, h1, h2, -⟩ := exists_stepTowerRenG d L N hd hL hN m₀ hm₀ κroot entropyLoss κmin
  exact ⟨T.toStepTowerG, h1, h2⟩

end Balaban.Inhabited
