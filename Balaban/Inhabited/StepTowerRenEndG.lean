/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenG
public import Balaban.Inhabited.StepTowerRenEnd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The general tower with the endpoint margin

`StepTowerRenEndG d L N κmin` extends `StepTowerRenG d L N κmin` by the margin
`K₂'(B_fam) (b_* t r₀) ≤ c₆`, for general dimension, block size and number of components.
`StepTowerRenEnd.toG` is the bridge from the fixed `3, 3, 2` record.  The producer
`exists_stepTowerRenEndG` (the radius `r₀` is decreased until the margin holds, all other margins
persisting) is in `Balaban.Inhabited.StepTowerGProducers`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep

/-- The general tower with the renormalization margins and the endpoint margin. -/
structure StepTowerRenEndG (d L N : ℕ) [NeZero L] (κmin : ℝ) extends
    StepTowerRenG d L N κmin where
  end_margin : cK2' d L N (famConst d L BG κ) *
    ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * t * r₀) ≤ c6 d L N

/-- **The bridge**: the fixed `3, 3, 2` record with the endpoint margin is a general one. -/
noncomputable def StepTowerRenEnd.toG {κmin : ℝ} (T : StepTowerRenEnd κmin) :
    StepTowerRenEndG 3 3 2 κmin :=
  { T.toStepTowerRen.toG with end_margin := T.end_margin }

namespace StepTowerRenEnd

variable {κmin : ℝ} (T : StepTowerRenEnd κmin)

@[simp] theorem toG_toStepTowerRenG : T.toG.toStepTowerRenG = T.toStepTowerRen.toG := rfl
@[simp] theorem toG_r₀ : T.toG.r₀ = T.r₀ := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl

end StepTowerRenEnd

/-- A general tower with the endpoint margin at `3, 3, 2` with `κ₀ = a_Ent + 2` and `m₀ = 1`
gives a fixed tower with the endpoint margin. -/
theorem StepTowerRenEndG.nonempty_fixed_of_three {κmin : ℝ} (T : StepTowerRenEndG 3 3 2 κmin)
    (h0 : T.κ0 = aEnt 3 3 + 2) (hm : T.m₀ = 1) : Nonempty (StepTowerRenEnd κmin) :=
  ⟨StepTowerRenEnd.mk (StepTowerRen.mk (T.toStepTowerG.ofThree h0 hm) T.ren_margin T.r₀
    T.r₀_pos T.r₀_le T.D₀_le_one T.D₀_le_star T.D₁_le_star) T.end_margin⟩

end Balaban.Inhabited
