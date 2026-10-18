/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Inhabited.DecMarkCorrFamilyFromTowerG
public import Balaban.Inhabited.MarkRealDiscSlice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Radius facts of the tower used in the two-torus comparison of the energy coefficient

For a scale package `D : StepScaleDataG T k hk N₁ ν β p₁` with `0 < p₁`, the hat radius
`c_ψ = lvCpsiG …` of the package satisfies `markedRad … c_ψ < t` and `2 p₁ ≤ c_ψ`, and the marks of
the interpolation family have radius `markedRad … p₁ < t` on the closed unit disc.  These are the
numerical hypotheses (`hum`, `hrad`, `hρc`) of the two-torus comparison of the marks.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section Rad

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ} {hk : 1 ≤ k}
  {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- The hat radius of the scale package: `markedRad … c_ψ < t` for `c_ψ = lvCpsiG …`. -/
theorem markedRad_lvCpsiG_lt (D : StepScaleDataG T k hk N₁ ν β p₁) :
    markedRad d L N k 1 T.κ (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t := by
  have hd2 : 2 ≤ d := by have := T.hd; omega
  have hb : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN hd2 k T.m₁ _ hk ν β p₁ T.δ
  have h := D.fl_radius
  rw [hb] at h
  unfold markedRad
  rw [Complex.norm_real] at h ⊢
  exact h

/-- `2 p₁ ≤ c_ψ` for the hat radius of the scale package. -/
theorem two_mul_le_lvCpsiG (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    2 * p₁ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hr := D.r_pos
  unfold lvRG at hr
  have h1 : 4 < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) / (2 * p₁) := by linarith
  rw [lt_div_iff₀ (by positivity)] at h1
  nlinarith

/-- The marks have radius `markedRad … p₁ < t` on the closed unit disc. -/
theorem norm_mul_markedRad_lt (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁)
    (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖u‖ * markedRad d L N k 1 T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hd2 : 2 ≤ d := by have := T.hd; omega
  have hb : (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN hd2 k T.m₁ _ hk ν β p₁ T.δ
  rw [hb]
  have hmem := compWeightG_mem T hk
  have hCs : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by have := T.hd; omega) T.hL (by linarith [hmem.1]) T.κ
  have hle : markedRad d L N k 1 T.κ p₁
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≤
      markedRad d L N k 1 T.κ (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
        (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) :=
    markedRad_mono d L N k 1 T.κ _ hCs (by have := two_mul_le_lvCpsiG T D hp; linarith)
  have hmr : 0 ≤ markedRad d L N k 1 T.κ p₁
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    unfold markedRad
    exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (mul_nonneg hCs hp.le))
  have hlt := markedRad_lvCpsiG_lt T D
  calc ‖u‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hu hmr
    _ = _ := one_mul _
    _ < T.t := lt_of_le_of_lt hle hlt

end Rad

end Balaban.Inhabited
