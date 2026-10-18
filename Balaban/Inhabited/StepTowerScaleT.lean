/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCoreMono
public import Balaban.Inhabited.StepTowerSmall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Towers at a smaller step radius

Every condition of `StepTower` that involves the step radius `t` is monotone in `t`, the core by
`FlCore.mono`.  Hence a tower can be shrunk to any smaller radius `t' ∈ (0, t]` keeping all the
other parameters `(m₁, c, B_G, κ, c₂, B_G₂, δ_c, δ, δ')` (`exists_stepTower_shrink`).  This is the
tower at the scale-dependent step radius `t_k = ε_{k+1}` of the source (P4 (H.1)), with the
parameters independent of the scale.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited

/-- **A tower at any smaller step radius, with the other parameters unchanged.** -/
theorem exists_stepTower_shrink {κmin : ℝ} (T : StepTower κmin) {t' : ℝ} (ht0 : 0 < t')
    (htT : t' ≤ T.t) :
    ∃ T' : StepTower κmin, T'.t = t' ∧ T'.m₁ = T.m₁ ∧ T'.c = T.c ∧ T'.BG = T.BG ∧
      T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧ T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' := by
  have hX : 0 < xiC1 3 := lt_of_lt_of_le one_pos (one_le_xiC1 3)
  have hK4 : 0 < K4 3 3 2 T.BG T.κ := by
    obtain ⟨hC⟩ := T.core
    exact K4_pos hC.hS.fam.2.1 (by norm_num)
  have hc2 : 0 < cK2 3 3 2 := cK2_pos 3 3 2
  have hc2' : 0 ≤ cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := cK2'_nonneg (d := 3) (L := 3) (N := 2) T.fam_nonneg
  have hC4 : (8 : ℝ) ≤ compC4 3 := compC4_ge 3
  have hK1 : 0 < bgK1 3 3 2 := bgK1_pos 3 3 2
  have hxt : xiC1 3 * t' ≤ xiC1 3 * T.t := mul_le_mul_of_nonneg_left htT hX.le
  have hdm : decDomMargin 3 3 2 T.BG T.κ (xiC1 3 * t') ≤
      decDomMargin 3 3 2 T.BG T.κ (xiC1 3 * T.t) := by
    unfold decDomMargin
    have h0 : 0 ≤ xiC1 3 * t' := by positivity
    have h1 : K4 3 3 2 T.BG T.κ * (xiC1 3 * t') ≤ K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t) :=
      mul_le_mul_of_nonneg_left hxt hK4.le
    have h2 : 0 ≤ K4 3 3 2 T.BG T.κ * (xiC1 3 * t') := by positivity
    have h3 : K4 3 3 2 T.BG T.κ * (xiC1 3 * t') *
        (K4 3 3 2 T.BG T.κ * (xiC1 3 * t') + 2 * (1 + 3 * (xiC1 3 * t'))) ≤
        K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t) *
        (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t) + 2 * (1 + 3 * (xiC1 3 * T.t))) :=
      mul_le_mul h1 (by linarith) (by linarith) (mul_nonneg hK4.le (by have := T.t_pos; positivity))
    nlinarith
  refine ⟨{ T with
    t := t'
    t_pos := ht0
    core := T.core_mono ht0 htT ht0 htT
    dom_margin := lt_of_le_of_lt hdm T.dom_margin
    coer_margin := by
      have := mul_le_mul_of_nonneg_left hxt hK4.le
      linarith [T.coer_margin]
    t_cap := by linarith [T.t_cap]
    bg0_cap := by nlinarith [T.bg0_cap]
    cK2_cap := by nlinarith [T.cK2_cap]
    cK2'_cap := by nlinarith [T.cK2'_cap]
    bg1_cap := by nlinarith [T.bg1_cap, mul_le_mul_of_nonneg_left hxt hK1.le]
    xi_small := by linarith [T.xi_small] }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Balaban.Inhabited
