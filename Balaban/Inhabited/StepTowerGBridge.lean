/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.StepTowerG

/-!
# The bridge from the fixed tower to the general tower

`StepTower.toG` maps the fixed `d = L = 3`, `N = 2` tower to `StepTowerG 3 3 2`.  The scalar
fields are preserved; the core is transported along `rhoSepG 3 3 m₁ = rhoSep m₁` and
`νref 3 = nuW`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

/-- **The general tower record is inhabited** at `d = L = 3`, `N = 2` for every `κmin`. -/
theorem exists_stepTowerG_three (κmin : ℝ) : Nonempty (StepTowerG 3 3 2 κmin) :=
  (exists_stepTower κmin).map StepTower.toG

end Balaban.Inhabited
