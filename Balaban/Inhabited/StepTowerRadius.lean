/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerTheta
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The renormalization margins at any class radius `e ≤ t`

For a tower `R` and `0 < e ≤ R.t`, the eight margins of the tower records hold with `R.t`
replaced by `e` (same `r₀`), `ThetaChartMargin` holds at class radius `e` with chart radius
`e + ξ₂ (3/2) e r₀ ≤ 2 e`, and the renormalized datum at class radius `t/2` lies in the step chart
at the radius `t`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **The eight margins of the tower at any radius `e ≤ t`.** -/
theorem StepTowerRenSol.margins_of_le {κmin : ℝ} (R : StepTowerRenSol κmin) {e : ℝ}
    (het : e ≤ R.t) :
    2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) <
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) + 3 * R.r₀ ≤ 1 ∧
      2 * (K4 3 3 2 R.BG R.κ * (xiC1 3 * e)) + 3 * R.r₀ ≤
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀ ≤
        deltaStar' 3 3 2 (famConst 3 3 R.BG R.κ) (gamma1 3 / 8) ∧
      cK2' 3 3 2 (famConst 3 3 R.BG R.κ) *
          ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀) ≤
        c6 3 3 2 ∧
      bgK1 3 3 2 * (xiC1 3 * e) < deltaStar 3 3 2 ∧
      bgK1 3 3 2 * (xiC1 3 * e) + 3 * R.r₀ ≤ deltaStar 3 3 2 ∧
      8 * e * R.r₀ ≤ deltaStar 3 3 2 := by
  obtain ⟨hC₀⟩ := R.core
  have hd : 0 < 3 := by norm_num
  have hK4 := K4_pos (L := 3) (N := 2) (κ := R.κ) hC₀.hS.fam.2.1 hd
  have hK1 := bgK1_pos 3 3 2
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  have hB1 := famConst_ge_one (L := 3) hC₀.hS.fam.2.1 R.κ hd
  have hK2 : 0 ≤ cK2' 3 3 2 (famConst 3 3 R.BG R.κ) :=
    cK2'_nonneg (d := 3) (L := 3) (N := 2) (B := famConst 3 3 R.BG R.κ) (by linarith)
  have hr := R.r₀_pos
  have hKX : 0 ≤ K4 3 3 2 R.BG R.κ * xiC1 3 := by positivity
  have hK1X : 0 ≤ bgK1 3 3 2 * xiC1 3 := by positivity
  have hc : 0 ≤ 3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3) := by positivity
  have h1 : K4 3 3 2 R.BG R.κ * (xiC1 3 * e) ≤ K4 3 3 2 R.BG R.κ * (xiC1 3 * R.t) := by
    have := mul_le_mul_of_nonneg_left het hKX; linarith
  have h2 : bgK1 3 3 2 * (xiC1 3 * e) ≤ bgK1 3 3 2 * (xiC1 3 * R.t) := by
    have := mul_le_mul_of_nonneg_left het hK1X; linarith
  have h3 : (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * e * R.r₀ ≤
      (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 R.BG R.κ + bgK1 3 3 2) * xiC1 3)) * R.t * R.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het hc) hr.le
  refine ⟨?_, ?_, ?_, h3.trans R.D₁_le_star, ?_, ?_, ?_, ?_⟩
  · linarith [R.ren_margin]
  · linarith [R.D₀_le_one]
  · linarith [R.D₀_le_star]
  · exact (mul_le_mul_of_nonneg_left h3 hK2).trans R.end_margin
  · linarith [R.sol_margin]
  · linarith [R.sol_K]
  · have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het (by norm_num : (0:ℝ) ≤ 8))
      hr.le
    nlinarith [R.sol_ζ]

/-- **The chart margin at any class radius `e ≤ t`**, with chart radius at most `2 e`. -/
theorem StepTowerTheta.thetaChartMargin_of_le {κmin : ℝ} (R : StepTowerTheta κmin) {e : ℝ}
    (he : 0 < e) (het : e ≤ R.t) :
    ThetaChartMargin 3 3 2 e (e + xiK2 3 3 2 * (3 / 2 * e * R.r₀)) R.r₀ ∧
      e + xiK2 3 3 2 * (3 / 2 * e * R.r₀) ≤ 2 * e := by
  have hM := thetaChartMargin_of_stepTowerRenSol R.toStepTowerRenSol
  have hr := R.r₀_pos
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  have hK1 := bgK1_pos 3 3 2
  have hK2 := cK2_pos 3 3 2
  have hxK := xiK2_pos'
  have hδ : (3 / 2 : ℝ) * e * R.r₀ ≤ (3 / 2 : ℝ) * R.t * R.r₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left het (by norm_num)) hr.le
  refine ⟨⟨he, hr, by positivity, hδ.trans hM.δ_one, ?_, ?_, hδ.trans hM.star, ?_, ?_, rfl⟩, ?_⟩
  · have := mul_le_mul_of_nonneg_left het (by norm_num : (0 : ℝ) ≤ (4 * 3 + 6) * (2 * 3 + 1))
    have h2 := hM.small
    nlinarith
  · have := mul_le_mul_of_nonneg_left het hX
    linarith [hM.data]
  · have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left het hX) hK1.le
    linarith [hM.K₁]
  · have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left het hX) hK1.le
    have h2 := mul_le_mul_of_nonneg_left hδ hK2.le
    linarith [hM.c₀]
  · have h := mul_le_mul_of_nonneg_left R.r₀_xi he.le
    nlinarith

section Half

variable {κmin : ℝ}

/-- **The renormalized datum at class radius `t/2` lies in the step chart at radius `t`.**  The
hypotheses are those of `StepTowerTheta.detGrouped_ambient`. -/
theorem StepTowerTheta.renDatum_half_mem_xiCData (R : StepTowerTheta κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
    (hD : XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
      (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν (R.t / 2) D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < R.r₀) :
    XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a
      (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t
      (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) := by
  have ht := R.t_pos
  have hH := bgHyp_lv (k := k) R.m₁ hν0 hν
  obtain ⟨hM, hle⟩ := R.thetaChartMargin_of_le (e := R.t / 2) (by positivity) (by linarith)
  exact renE0_theta_domain_of_le _ hH (R.t / 2) _ R.t R.r₀ hM (by linarith) D hD ξ hξ

end Half

end Balaban.Inhabited
