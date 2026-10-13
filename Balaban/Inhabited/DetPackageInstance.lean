/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.StepTowerOfG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The determinant package at one scale of the shared tower

* `detPackage_instance`: the package of `detPackage_fromTower` at `k = 1`, `N₁ = 6`, for a tower
  supplied by `exists_stepTower`.  It lives here because `exists_stepTower` is a corollary of the
  general producer, which depends on `DetPackageFromTower`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Localization.DecEquiv Matrix

section Package

variable {κmin : ℝ}

/-- **Non-vacuity at one scale** (`k = 1`, `N₁ = 6`, `ν = 0`, `β = 0`, `p₁ = 1`): for every
`κmin` there is a tower `T`, a datum `D` of the chart at the step, and a family of records with the
term formula for which the sum identity and the bound at the hull rate hold at `D`. -/
theorem detPackage_instance (κmin : ℝ) :
    ∃ T : StepTower κmin, ∃ D : BgData (T.step 1 le_rfl 6 0 0 1).G' 2,
      XiCData (T.step 1 le_rfl 6 0 0 1).G' (compWeight 3 1) 0 (1 + 1) 1 T.t D ∧
      ∃ E : ∀ z : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))),
          DetExpansionLocC (T.step 1 le_rfl 6 0 0 1) 1 z T.t (towerDetRate T.κ)
            (towerDetConst T.κ),
        (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step 1 le_rfl 6 0 0 1).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 0 (rho4 3 3 2 T.BG T.κ) D y T') ∧
        ∀ z (X : Set (CTorus 3 3 6 T.m₁ (1 + 1))),
          ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) *
            Real.exp (-hullRate 3 3 (towerDetRate T.κ) * sizeJ 1 (1 + 1) X) := by
  obtain ⟨T⟩ := exists_stepTower κmin
  obtain ⟨βray, -, ⟨hS⟩⟩ := T.scale_instance
  obtain ⟨E, hE, -, hb, -⟩ := detPackage_fromTower T 1 le_rfl 6 (by norm_num) (by norm_num)
    (ν := 0) le_rfl (by norm_num) 0 1
  exact ⟨T, _, hS.xi, E, hE, fun z X => hb z _ hS.xi X⟩

end Package

end Balaban.Inhabited
