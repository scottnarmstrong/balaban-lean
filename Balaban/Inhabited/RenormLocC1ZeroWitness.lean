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

`renLocC1_scale_of_tower` now lives in `RenormRadiusLoc`, as a corollary of the general
`renLocC1_scale_of_towerG_of_le_at`.

`locC2`, `locDφ` and an inhabitant of `RenormExpInput` are NOT proved here.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

end Balaban.Inhabited
