/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTower
public import Balaban.Inhabited.StepTowerG
public import Balaban.Inhabited.StepTowerRen
public import Balaban.Inhabited.TowerCoreRatesGeneral
public import Balaban.Inhabited.TowerCoreRatesVariantsGeneral
public import Balaban.Fluctuation.DetRateGeneral
public import Balaban.Fluctuation.RenormStrictData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The general tower with the renormalization margins

`StepTowerRenG d L N κmin` extends `StepTowerG d L N κmin` by the strict margin
`2 K₄ ξ₁ t < δ_*′(famConst BG κ, γ₁/8)` and one radius `r₀` with the three margins
`D₀ ≤ 1`, `D₀ ≤ δ_*′`, `D₁ ≤ δ_*′`, for general dimension, block size and number of components.
`StepTowerRenG.shrink` decreases `r₀` (all margins persist), and `StepTowerRen.toG` is the bridge
from the fixed `3, 3, 2` record.  The producer `exists_stepTowerRenG` is in
`Balaban.Inhabited.StepTowerGProducers`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep

/-- The general tower with the renormalization margins. -/
structure StepTowerRenG (d L N : ℕ) [NeZero L] (κmin : ℝ) extends StepTowerG d L N κmin where
  ren_margin : 2 * (K4 d L N BG κ * (xiC1 d * t)) <
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)
  r₀ : ℝ
  r₀_pos : 0 < r₀
  r₀_le : r₀ ≤ 1 / 16
  D₀_le_one : 2 * (K4 d L N BG κ * (xiC1 d * t)) + 3 * r₀ ≤ 1
  D₀_le_star : 2 * (K4 d L N BG κ * (xiC1 d * t)) + 3 * r₀ ≤
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)
  D₁_le_star : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * t * r₀ ≤
    deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)

/-- **The bridge**: the fixed `3, 3, 2` record with margins is a general one. -/
noncomputable def StepTowerRen.toG {κmin : ℝ} (T : StepTowerRen κmin) :
    StepTowerRenG 3 3 2 κmin :=
  { T.toStepTower.toG with
    ren_margin := T.ren_margin
    r₀ := T.r₀
    r₀_pos := T.r₀_pos
    r₀_le := T.r₀_le
    D₀_le_one := T.D₀_le_one
    D₀_le_star := T.D₀_le_star
    D₁_le_star := T.D₁_le_star }

namespace StepTowerRen

variable {κmin : ℝ} (T : StepTowerRen κmin)

@[simp] theorem toG_toStepTowerG : T.toG.toStepTowerG = T.toStepTower.toG := rfl
@[simp] theorem toG_r₀ : T.toG.r₀ = T.r₀ := rfl
@[simp] theorem toG_κ : T.toG.κ = T.κ := rfl
@[simp] theorem toG_t : T.toG.t = T.t := rfl
@[simp] theorem toG_BG : T.toG.BG = T.BG := rfl
@[simp] theorem toG_κ0 : T.toG.κ0 = T.κ0 := rfl
@[simp] theorem toG_κdec : T.toG.κdec = T.κdec := rfl
@[simp] theorem toG_κ' : T.toG.κ' = T.κ' := rfl
@[simp] theorem toG_m₁ : T.toG.m₁ = T.m₁ := rfl
@[simp] theorem toG_m₀ : T.toG.m₀ = 1 := rfl

end StepTowerRen

/-- **The margins of the record persist when `r₀` decreases.** -/
def StepTowerRenG.shrink {d L N : ℕ} [NeZero L] {κmin : ℝ} (R : StepTowerRenG d L N κmin)
    (r : ℝ) (hr0 : 0 < r) (hr : r ≤ R.r₀) : StepTowerRenG d L N κmin :=
  { R with
    r₀ := r
    r₀_pos := hr0
    r₀_le := hr.trans R.r₀_le
    D₀_le_one := by have := R.D₀_le_one; linarith
    D₀_le_star := by have := R.D₀_le_star; linarith
    D₁_le_star := by
      have h := R.D₁_le_star
      have hb : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t := by
        obtain ⟨hC₀⟩ := R.core
        have hK4 := K4_pos (d := d) (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1
          (by have := R.hd; omega)
        have hK1 := bgK1_pos d L N
        have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
        have := R.t_pos
        positivity
      have : (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * r ≤
          (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * R.r₀ :=
        mul_le_mul_of_nonneg_left hr hb
      linarith }

/-- The shrunk record has the radius `r`. -/
@[simp] theorem StepTowerRenG.shrink_r₀ {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenG d L N κmin) (r : ℝ) (hr0 : 0 < r) (hr : r ≤ R.r₀) :
    (R.shrink r hr0 hr).r₀ = r := rfl

end Balaban.Inhabited
