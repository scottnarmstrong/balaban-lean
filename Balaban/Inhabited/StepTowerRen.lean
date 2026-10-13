/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.TowerCoreRatesRen
public import Balaban.Fluctuation.RenormStrictData
public import Balaban.Fluctuation.RenormDecAnalytic
public import Balaban.Inhabited.RenormLocC1ZeroWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shared tower with the renormalization margins

`StepTowerRen κmin` extends `StepTower κmin` by the strict margin
`2 K₄ ξ₁ t < δ_*′(famConst BG κ, γ₁/8)` (which does not follow from `FlCore`) and one radius `r₀`
with the three margins `D₀ ≤ 1`, `D₀ ≤ δ_*′`, `D₁ ≤ δ_*′` in the forms taken by `renDec_analytic`
and `renDec_sharp` at `ε = t`.  `exists_stepTowerRen` shows that the record is inhabited for every
`κmin`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover Filter Topology

/-- The shared tower with the renormalization margins. -/
structure StepTowerRen (κmin : ℝ) extends StepTower κmin where
  ren_margin : 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) <
    deltaStar' 3 3 2 (famConst 3 3 BG κ) (gamma1 3 / 8)
  r₀ : ℝ
  r₀_pos : 0 < r₀
  r₀_le : r₀ ≤ 1 / 16
  D₀_le_one : 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) + 3 * r₀ ≤ 1
  D₀_le_star : 2 * (K4 3 3 2 BG κ * (xiC1 3 * t)) + 3 * r₀ ≤
    deltaStar' 3 3 2 (famConst 3 3 BG κ) (gamma1 3 / 8)
  D₁_le_star : (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 BG κ + bgK1 3 3 2) * xiC1 3)) * t * r₀ ≤
    deltaStar' 3 3 2 (famConst 3 3 BG κ) (gamma1 3 / 8)


end Balaban.Inhabited
