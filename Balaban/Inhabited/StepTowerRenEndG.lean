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
`exists_stepTowerRenEndG` shows that the record is inhabited (the radius `r₀` is decreased until
the margin holds, all other margins persisting), and `StepTowerRenEnd.toG` is the bridge from the
fixed `3, 3, 2` record.
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

/-- **The general record with the endpoint margin is inhabited**, with cover index `m₀` and
output-rate floor `entropyLoss + c₁ κ_root ≤ (3/2) κ_dec`. -/
theorem exists_stepTowerRenEndG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (κroot entropyLoss κmin : ℝ) :
    ∃ T : StepTowerRenEndG d L N κmin, T.m₀ = m₀ ∧
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec := by
  obtain ⟨R, hm, hent⟩ := exists_stepTowerRenG d L N hd hL hN m₀ hm₀ κroot entropyLoss κmin
  obtain ⟨hC₀⟩ := R.core
  have hd0 : 0 < d := by omega
  have hB1 := famConst_ge_one (L := L) hC₀.hS.fam.2.1 R.κ hd0
  have hK2 : 0 ≤ cK2' d L N (famConst d L R.BG R.κ) :=
    cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L R.BG R.κ) (by linarith)
  have hc6 : 0 < c6 d L N := c6_pos (d := d) (L := L) (N := N) hd0
  have hK4 := K4_pos (d := d) (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1 hd0
  have hK1 := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hcoef : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t := by
    have := R.t_pos
    positivity
  have hA := mul_nonneg hK2 hcoef
  obtain ⟨r, hr0, hr1, -, hr2, -⟩ := exists_radius_margins hA hc6 hc6 R.r₀_pos R.r₀_pos
  refine ⟨{ R with
    r₀ := r
    r₀_pos := hr0
    r₀_le := hr1.trans R.r₀_le
    D₀_le_one := by have := R.D₀_le_one; linarith
    D₀_le_star := by have := R.D₀_le_star; linarith
    D₁_le_star := by
      have h := R.D₁_le_star
      have : (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * r ≤
          (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * R.r₀ :=
        mul_le_mul_of_nonneg_left hr1 hcoef
      linarith
    end_margin := by
      calc _ = cK2' d L N (famConst d L R.BG R.κ) *
          ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t) * r := by
            ring
        _ ≤ c6 d L N := hr2 }, hm, hent⟩

end Balaban.Inhabited
