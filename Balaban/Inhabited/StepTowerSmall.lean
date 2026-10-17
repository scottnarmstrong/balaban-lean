/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.BgSettingDataNum
import Mathlib.Tactic.Linarith

/-!
# Towers whose step size satisfies the numerical smallness conditions

`exists_stepTower_pred`: the fixed tower of `exists_stepTower` can be taken with any predicate on
`(m₁, BG, BG₂, κ, t)` that holds for all small `t > 0` and every choice of the other parameters.
`exists_stepTower_base` applies it to the smallness conditions `ChainNum`, `FlNum` of
`joint_num_eventually` at `r₀ = 324`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Filter Topology

/-- **The tower record with an eventual predicate on its step size.** -/
theorem exists_stepTower_pred (κmin : ℝ) (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T : StepTower κmin, Pr T.m₁ T.BG T.BG₂ T.κ T.t := by
  obtain ⟨T, hPT, hm, -, h0⟩ :=
    exists_stepTowerThetaG_pred 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin Pr hP
  have := aEnt_nonneg 3 3
  exact ⟨T.toStepTowerRenSolG.toStepTowerRenEndG.toStepTowerRenG.toStepTowerG.ofThree
    (h0 (by simp; linarith)) hm, hPT⟩

/-- **Towers with the smallness conditions `ChainNum`, `FlNum`.** For every `κmin` there is a tower
`T` and constants `δ₃`, `δ_fl` with `ChainNum` and `FlNum` at the tower's own `m₁, BG, BG₂, κ, t`
and `r₀ = 324`. -/
theorem exists_stepTower_base (κmin : ℝ) :
    ∃ (T : StepTower κmin) (δ₃ δfl : ℝ),
      ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl := by
  obtain ⟨T, hT⟩ := exists_stepTower_pred κmin
    (fun m₁ BG BG₂ κ t => 0 ≤ BG → 0 ≤ BG₂ → ∃ δ₃ δfl : ℝ,
      ChainNum 3 3 2 m₁ BG κ 324 t δ₃ ∧ FlNum 3 3 2 BG BG₂ κ t δ₃ t δfl)
    (fun m₁ BG BG₂ κ => by
      by_cases h : 0 ≤ BG ∧ 0 ≤ BG₂
      · exact (BgSettingData.joint_num_eventually 3 3 2 m₁ (by norm_num) h.1 h.2 κ 324).mono
          fun t ht _ _ => ht
      · exact Eventually.of_forall fun t h1 h2 => absurd ⟨h1, h2⟩ h)
  obtain ⟨hC⟩ := T.core
  have hBG : 0 ≤ T.BG := hC.hS.fam.2.1
  have hBG₂ : 0 ≤ T.BG₂ := hC.hS2.fam.2.1
  obtain ⟨δ₃, δfl, h1, h2⟩ := hT hBG hBG₂
  exact ⟨T, δ₃, δfl, h1, h2⟩

end Balaban.Inhabited
