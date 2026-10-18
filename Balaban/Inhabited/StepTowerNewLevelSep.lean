/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityLevelRho
public import Balaban.Localization.I5Inhabited

/-!
# The separation of the tower's class against the local generating sets (`StepTowerNewLevelSep`)

`localClass_newLevel_of_expansion_rho` needs `hsep : ϱ ≤ minSep L (L ^ m₁)` on the torus
`CTorus d L N₁ m₁ (k + 1)`.  The class of the tower's step lives on the torus of index `T.m₁` with
the separation `ϱ = rhoSep T.m₁` (`StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)`).  The theorem
`not_rhoSep_le_minSep` shows that the hypothesis `hsep` is false there: `rhoSep m ≥ 360 · 3 ^ m`
while `minSep 3 (3 ^ m) = 15 · 3 ^ m`.  It holds one cube index finer
(`rhoSep_le_minSep_of_four`, `m ≥ 4`), i.e. for the local sets read on the torus of index `m + 4`
with the same number of sites.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField Balaban.Localization.I5Inhabited

/-- **`hsep` fails on the tower's own torus**: the class separation `rhoSep m` of the tower is
larger than the separation `minSep 3 (3 ^ m) = 15 · 3 ^ m` of the local generating sets on the
torus of cube index `m`. -/
theorem not_rhoSep_le_minSep (m : ℕ) : ¬ rhoSep m ≤ minSep 3 (3 ^ m) := by
  intro h
  have h1 : (0 : ℝ) ≤ Background.bgR0 3 3 := Localization.I5Inhabited.bgR0_nonneg_aux
  have h2 := Localization.I5Inhabited.rhoSep_tail_nonneg
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  unfold rhoSep minSep at h
  push_cast at h
  linarith

end Balaban.Inhabited
