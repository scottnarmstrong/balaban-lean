/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Inhabited.StepTowerGBridge
public import Balaban.Inhabited.StepTowerScale

/-!
# The general scale record at the fixed tower is the fixed scale record

For `T : StepTower κmin`, the step `T.toG.step` of the general tower and the step `T.step` of the
fixed tower live over the equal separation parameters `rhoSepG 3 3 T.m₁` and `rhoSep T.m₁`.  The
two steps correspond under this equality, and `StepScaleDataG T.toG …` implies
`StepScaleData T …` field by field.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

namespace StepTower

variable {κmin : ℝ}

/-- The general step of `T.toG` and the fixed step of `T` correspond along
`rhoSepG 3 3 T.m₁ = rhoSep T.m₁`. -/
theorem toG_step_heq (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν β p₁ : ℝ) : HEq (T.toG.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁) := by
  have key : ∀ ϱ : ℝ, ϱ = rhoSep T.m₁ →
      HEq (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁ T.δ)
        (T.step k hk N₁ ν β p₁) := by
    intro ϱ hϱ; subst hϱ; exact HEq.rfl
  exact key _ (rhoSepG_three _)

/-- The block couplings of the two steps agree. -/
theorem toG_step_betaU (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν β p₁ : ℝ) :
    (T.toG.step k hk N₁ ν β p₁).betaU = (T.step k hk N₁ ν β p₁).betaU := by
  have key : ∀ ϱ : ℝ, ϱ = rhoSep T.m₁ →
      (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁ T.δ).betaU =
        (T.step k hk N₁ ν β p₁).betaU := by
    intro ϱ hϱ; subst hϱ; rfl
  exact key _ (rhoSepG_three _)

/-- **The general scale record at the fixed tower gives the fixed scale record.** -/
theorem scaleData_of_toG (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
    {ν β p₁ : ℝ} (h : StepScaleDataG T.toG k hk N₁ ν β p₁) :
    StepScaleData T k hk N₁ ν β p₁ := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have hbe := toG_step_betaU T k hk N₁ ν β p₁
  have key : ∀ ϱ : ℝ, ϱ = rhoSep T.m₁ →
      FlCore 2 (lvTopG 3 3 N₁ T.m₁ k ϱ) (lvLowG 3 3 N₁ T.m₁ k ϱ) 1 ν T.c T.BG T.κ T.t
        (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t →
      XiCData (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁ T.δ).G'
        (compWeight 3 1) ν (k + 1) 1 T.t
        (hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁ T.δ).D' →
      Nonempty ((hatStepKG (d := 3) (L := 3) (N := 2) (N₁ := N₁) le_rfl k T.m₁ ϱ hk ν β p₁
        T.δ).RayData (2 * p₁)) →
      LevelCoversG 3 3 2 N₁ T.m₁ k ϱ ϱ (lvTopG 3 3 N₁ T.m₁ k ϱ) (lvLowG 3 3 N₁ T.m₁ k ϱ) 1 →
      FlCore 2 (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 ν T.c T.BG
          T.κ T.t (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t ∧
        XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
          (T.step k hk N₁ ν β p₁).D' ∧
        Nonempty ((T.step k hk N₁ ν β p₁).RayData (2 * p₁)) ∧
        LevelCovers N₁ T.m₁ k (rhoSep T.m₁) (rhoSep T.m₁) (lvTop N₁ T.m₁ k (rhoSep T.m₁))
          (lvLow N₁ T.m₁ k (rhoSep T.m₁)) 1 := by
    intro ϱ hϱ; subst hϱ; exact fun a b c d => ⟨a, b, c, d⟩
  obtain ⟨c1, c2, c3, c4⟩ := key _ (rhoSepG_three _) h.core h.xi h.ray h.covers
  refine ⟨c1, c2, c3, ?_, ?_, ?_, ?_, h.p_lt, c4⟩
  · simpa [hb, lvCpsiG_three, lvRG_three] using h.cψ_pos
  · simpa [hb, lvCpsiG_three, lvRG_three] using h.r_pos
  · have := h.fl_radius
    rw [hbe] at this
    simpa [hb, lvCpsiG_three, lvRG_three] using this
  · simpa [hb, lvCpsiG_three, lvRG_three] using h.ray_margin

end StepTower

end Balaban.Inhabited
