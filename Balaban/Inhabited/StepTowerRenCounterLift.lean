/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenSol
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Towers with the renormalization margins from small step radius

All margins of `StepTowerRenSol` are monotone in the step radius `t` and in `r₀`.  For a step
tower `T₀` there are `t* > 0` and `r* > 0` such that every step tower `T` with the constants
`BG`, `κ` of `T₀` and `T.t ≤ t*` is the underlying step tower of a `StepTowerRenSol` of radius
`r₀` for every `0 < r₀ ≤ r*`.  This applies to the towers `t_k = λ ε_{k+1}` of
`e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_phi`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited

/-- **The margins of the solution tower at small radius.**  For `T₀ : StepTower κmin` there are
`t*, r* > 0` such that every `T : StepTower κmin` with `T.BG = T₀.BG`, `T.κ = T₀.κ`,
`T.t ≤ t*` and every `0 < r₀ ≤ r*` is the underlying step tower of some
`R : StepTowerRenSol κmin` with `R.r₀ = r₀`. -/
theorem exists_stepTowerRenSol_of_small {κmin : ℝ} (T₀ : StepTower κmin) :
    ∃ ts rs : ℝ, 0 < ts ∧ 0 < rs ∧ ∀ T : StepTower κmin, T.BG = T₀.BG → T.κ = T₀.κ →
      T.t ≤ ts → ∀ r₀ : ℝ, 0 < r₀ → r₀ ≤ rs →
      ∃ R : StepTowerRenSol κmin, R.toStepTower = T ∧ R.r₀ = r₀ := by
  obtain ⟨hC₀⟩ := T₀.core
  have hBG : 0 ≤ T₀.BG := hC₀.hS.fam.2.1
  have hB1 := famConst_ge_one (d := 3) (L := 3) hBG T₀.κ (by norm_num)
  have hK2 : 0 ≤ cK2' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) :=
    cK2'_nonneg (by linarith)
  have hc6 : 0 < c6 3 3 2 := c6_pos 3 3 2 (by norm_num)
  have hds : 0 < deltaStar 3 3 2 := deltaStar_pos 3 3 2 (by norm_num)
  have hdp : 0 < deltaStar' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) (gamma1 3 / 8) :=
    deltaStar'_pos (by linarith) (by have := gamma1_pos (d := 3) (by norm_num); positivity)
  have hK4 := K4_pos (d := 3) (L := 3) (N := 2) (κ := T₀.κ) hBG (by norm_num)
  have hK1 := bgK1_pos 3 3 2
  have hX : 0 ≤ xiC1 3 := by unfold xiC1; positivity
  set P : ℝ := min (min 1 (deltaStar' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) (gamma1 3 / 8)))
    (min (deltaStar 3 3 2) (c6 3 3 2)) with hP
  have hP0 : 0 < P := lt_min (lt_min one_pos hdp) (lt_min hds hc6)
  have hP1 : P ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hPd : P ≤ deltaStar' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) (gamma1 3 / 8) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hPs : P ≤ deltaStar 3 3 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hPc : P ≤ c6 3 3 2 := (min_le_right _ _).trans (min_le_right _ _)
  set b : ℝ := 3 / 2 + 32 / 15 * (3 + (K4 3 3 2 T₀.BG T₀.κ + bgK1 3 3 2) * xiC1 3) with hb
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  set M : ℝ := 16 + b + cK2' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) * b with hM
  have hM0 : 16 ≤ M := by
    have : 0 ≤ cK2' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) * b := mul_nonneg hK2 hb0
    rw [hM]; linarith
  have hM1 : 0 < M := by linarith
  set m : ℝ := 2 * (K4 3 3 2 T₀.BG T₀.κ * xiC1 3) + bgK1 3 3 2 * xiC1 3 + 1 with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  clear_value P b M m
  refine ⟨min 1 (P / (2 * m)), P / (2 * M), lt_min one_pos (by positivity), by positivity,
    fun T hBGT hκT ht r₀ hr hrs => ?_⟩
  have ht1 : T.t ≤ 1 := ht.trans (min_le_left _ _)
  have ht2 : m * T.t ≤ P / 2 := by
    have := ht.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hMr : M * r₀ ≤ P / 2 := by
    rw [le_div_iff₀ (by positivity)] at hrs
    linarith
  have htp := T.t_pos
  have hmt : ∀ x : ℝ, 0 ≤ x → x ≤ m → x * T.t ≤ P / 2 := fun x hx hxm =>
    (mul_le_mul_of_nonneg_right hxm htp.le).trans ht2
  have hKX := mul_nonneg hK4.le hX
  have hK1X := mul_nonneg hK1.le hX
  have e1 : 2 * (K4 3 3 2 T₀.BG T₀.κ * (xiC1 3 * T.t)) ≤ P / 2 := by
    have := hmt (2 * (K4 3 3 2 T₀.BG T₀.κ * xiC1 3)) (by positivity) (by rw [hm]; linarith)
    linarith [show 2 * (K4 3 3 2 T₀.BG T₀.κ * (xiC1 3 * T.t)) =
      2 * (K4 3 3 2 T₀.BG T₀.κ * xiC1 3) * T.t by ring]
  have e2 : bgK1 3 3 2 * (xiC1 3 * T.t) ≤ P / 2 := by
    have := hmt (bgK1 3 3 2 * xiC1 3) (by positivity) (by rw [hm]; linarith)
    linarith [show bgK1 3 3 2 * (xiC1 3 * T.t) = bgK1 3 3 2 * xiC1 3 * T.t by ring]
  have hbM : b ≤ M := by
    have : 0 ≤ cK2' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) * b := mul_nonneg hK2 hb0
    rw [hM]; linarith
  have hcbM : cK2' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) * b ≤ M := by rw [hM]; linarith
  have e3 : 3 * r₀ ≤ P / 2 :=
    (mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ M) hr.le).trans hMr
  have hbr : b * T.t * r₀ ≤ b * r₀ := by
    calc b * T.t * r₀ = (b * r₀) * T.t := by ring
      _ ≤ b * r₀ := mul_le_of_le_one_right (mul_nonneg hb0 hr.le) ht1
  have e4 : b * T.t * r₀ ≤ P / 2 :=
    hbr.trans ((mul_le_mul_of_nonneg_right hbM hr.le).trans hMr)
  have e5 : cK2' 3 3 2 (famConst 3 3 T₀.BG T₀.κ) * (b * T.t * r₀) ≤ P / 2 :=
    (mul_le_mul_of_nonneg_left hbr hK2).trans
      (by rw [← mul_assoc]; exact (mul_le_mul_of_nonneg_right hcbM hr.le).trans hMr)
  have e6 : 8 * T.t * r₀ ≤ P / 2 := by
    have : 8 * T.t * r₀ ≤ 8 * r₀ := by
      calc 8 * T.t * r₀ = (8 * r₀) * T.t := by ring
        _ ≤ 8 * r₀ := mul_le_of_le_one_right (by positivity) ht1
    exact this.trans ((mul_le_mul_of_nonneg_right (by linarith : (8 : ℝ) ≤ M) hr.le).trans hMr)
  have e7 : r₀ ≤ 1 / 16 := by
    have h16 : 16 * r₀ ≤ M * r₀ := mul_le_mul_of_nonneg_right hM0 hr.le
    linarith
  refine ⟨{ toStepTower := T
            ren_margin := ?_, r₀ := r₀, r₀_pos := hr, r₀_le := e7, D₀_le_one := ?_
            D₀_le_star := ?_, D₁_le_star := ?_, end_margin := ?_, sol_margin := ?_
            sol_K := ?_, sol_ζ := ?_ }, rfl, rfl⟩
  · show 2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t)) < _
    rw [hBGT, hκT]; linarith
  · show 2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t)) + 3 * r₀ ≤ 1
    rw [hBGT, hκT]; linarith
  · show 2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t)) + 3 * r₀ ≤ _
    rw [hBGT, hκT]; linarith
  · show (3 / 2 + 32 / 15 * (3 + (K4 3 3 2 T.BG T.κ + bgK1 3 3 2) * xiC1 3)) * T.t * r₀ ≤ _
    rw [hBGT, hκT]; (try rw [← hb]); linarith
  · show cK2' 3 3 2 (famConst 3 3 T.BG T.κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 3 3 2 T.BG T.κ + bgK1 3 3 2) * xiC1 3)) * T.t * r₀) ≤ _
    rw [hBGT, hκT]; (try rw [← hb]); linarith
  · show bgK1 3 3 2 * (xiC1 3 * T.t) < _
    linarith
  · show bgK1 3 3 2 * (xiC1 3 * T.t) + 3 * r₀ ≤ _
    linarith
  · show 8 * T.t * r₀ ≤ _
    linarith

end Balaban.Inhabited
