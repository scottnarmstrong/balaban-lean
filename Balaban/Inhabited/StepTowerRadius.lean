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

/-- **The eight margins of the general tower at any radius `e ≤ t`.** -/
theorem StepTowerRenSolG.margins_of_le {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (R : StepTowerRenSolG d L N κmin) {e : ℝ}
    (het : e ≤ R.t) :
    2 * (K4 d L N R.BG R.κ * (xiC1 d * e)) <
        deltaStar' d L N (famConst d L R.BG R.κ) (gamma1 d / 8) ∧
      2 * (K4 d L N R.BG R.κ * (xiC1 d * e)) + 3 * R.r₀ ≤ 1 ∧
      2 * (K4 d L N R.BG R.κ * (xiC1 d * e)) + 3 * R.r₀ ≤
        deltaStar' d L N (famConst d L R.BG R.κ) (gamma1 d / 8) ∧
      (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀ ≤
        deltaStar' d L N (famConst d L R.BG R.κ) (gamma1 d / 8) ∧
      cK2' d L N (famConst d L R.BG R.κ) *
          ((3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀) ≤
        c6 d L N ∧
      bgK1 d L N * (xiC1 d * e) < deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * e) + 3 * R.r₀ ≤ deltaStar d L N ∧
      8 * e * R.r₀ ≤ deltaStar d L N := by
  obtain ⟨hC₀⟩ := R.core
  have hd : 0 < d := by have := R.hd; omega
  have hK4 := K4_pos (L := L) (N := N) (κ := R.κ) hC₀.hS.fam.2.1 hd
  have hK1 := bgK1_pos d L N
  have hX : 0 ≤ xiC1 d := by unfold xiC1; positivity
  have hB1 := famConst_ge_one (L := L) hC₀.hS.fam.2.1 R.κ hd
  have hK2 : 0 ≤ cK2' d L N (famConst d L R.BG R.κ) :=
    cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L R.BG R.κ) (by linarith)
  have hr := R.r₀_pos
  have hKX : 0 ≤ K4 d L N R.BG R.κ * xiC1 d := by positivity
  have hK1X : 0 ≤ bgK1 d L N * xiC1 d := by positivity
  have hc : 0 ≤ 3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d) := by positivity
  have h1 : K4 d L N R.BG R.κ * (xiC1 d * e) ≤ K4 d L N R.BG R.κ * (xiC1 d * R.t) := by
    have := mul_le_mul_of_nonneg_left het hKX; linarith
  have h2 : bgK1 d L N * (xiC1 d * e) ≤ bgK1 d L N * (xiC1 d * R.t) := by
    have := mul_le_mul_of_nonneg_left het hK1X; linarith
  have h3 : (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * e * R.r₀ ≤
      (3 / 2 + 32 / 15 * (3 + (K4 d L N R.BG R.κ + bgK1 d L N) * xiC1 d)) * R.t * R.r₀ :=
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
      8 * e * R.r₀ ≤ deltaStar 3 3 2 :=
  R.toG.margins_of_le het

/-- **The chart margin at any class radius `e ≤ t`**, with chart radius at most `2 e`. -/
theorem StepTowerTheta.thetaChartMargin_of_le {κmin : ℝ} (R : StepTowerTheta κmin) {e : ℝ}
    (he : 0 < e) (het : e ≤ R.t) :
    ThetaChartMargin 3 3 2 e (e + xiK2 3 3 2 * (3 / 2 * e * R.r₀)) R.r₀ ∧
      e + xiK2 3 3 2 * (3 / 2 * e * R.r₀) ≤ 2 * e := by
  exact R.toG.thetaChartMargin_of_le he het

section HalfG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

/-- **The renormalized datum at class radius `t/2` lies in the step chart at radius `t`, general
tower.**  The hypotheses are those of `StepTowerThetaG.detGrouped_ambient`. -/
theorem StepTowerThetaG.renDatum_half_mem_xiCData (T : StepTowerThetaG d L N κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (D : BgData (T.step k hk N₁ ν β p₁).G' N)
    (hD : XiCOneReal (T.step k hk N₁ ν β p₁).G'
      (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν (T.t / 2) D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < T.r₀) :
    XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t
      (renThetaDatum (T.step k hk N₁ ν β p₁) (T.t / 2) D ξ) := by
  have ht := T.t_pos
  have hH := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
  obtain ⟨hM, hle⟩ := T.thetaChartMargin_of_le (e := T.t / 2) (by positivity) (by linarith)
  exact renE0_theta_domain_of_le _ hH (T.t / 2) _ T.t T.r₀ hM (by linarith) D hD ξ hξ

end HalfG

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
  have h := R.toG.renDatum_half_mem_xiCData k hk N₁ hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  dsimp only [StepTowerTheta.toG_m₁, StepTowerTheta.toG_t, StepTowerTheta.toG_r₀] at h
  generalize hρ : rhoSepG 3 3 R.m₁ = ϱ at h
  have e : ϱ = rhoSep R.m₁ := hρ.symm.trans (rhoSepG_three _)
  subst e
  exact h D hD ξ hξ

end Half

end Balaban.Inhabited
