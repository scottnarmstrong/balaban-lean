/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The general tower with the determinant data at the doubled radius

`StepTowerThetaG d L N κmin` extends `StepTowerRenSolG d L N κmin` by the step core and the two
determinant margins at the chart radius `2 t`, and by a parameter radius `r₀` so small that
`ξ₂ (3/2) r₀ ≤ 1`.  The producer `exists_stepTowerThetaG` is in
`Balaban.Inhabited.StepTowerGProducers`; the bridge from the fixed `3, 3, 2` record and the
fixed-record corollary are in `Balaban.Inhabited.StepTowerTheta`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep

/-- **The general tower with the determinant data at the doubled radius.**  Besides
`StepTowerRenSolG`, the step core `FlCore` and the two determinant margins at the radius `2 t`, and
a parameter radius `r₀` so small that `ξ₂ · (3/2) · r₀ ≤ 1`. -/
structure StepTowerThetaG (d L N : ℕ) [NeZero L] (κmin : ℝ) extends
    StepTowerRenSolG d L N κmin where
  core2 : Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 (νref L) c BG κ (2 * t)
    (levelKc d L) (Cchi d L) c₂ BG₂ (2 * t))
  dom_margin2 : decDomMargin d L N BG κ (xiC1 d * (2 * t)) < δc
  coer_margin2 : K4 d L N BG κ * (xiC1 d * (2 * t)) < coerciveConst d / 2
  r₀_xi : xiK2 d L N * ((3 / 2 : ℝ) * r₀) ≤ 1

end Balaban.Inhabited
