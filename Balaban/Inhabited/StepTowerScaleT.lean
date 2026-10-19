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
theorem StepTowerG.exists_shrink {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {t' : ℝ} (ht0 : 0 < t') (htT : t' ≤ T.t) :
    ∃ T' : StepTowerG d L N κmin, T'.t = t' ∧ T'.m₁ = T.m₁ ∧ T'.c = T.c ∧ T'.BG = T.BG ∧
      T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧ T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' ∧
      T'.κ0 = T.κ0 ∧ T'.m₀ = T.m₀ := by
  have hX : 0 < xiC1 d := lt_of_lt_of_le one_pos (one_le_xiC1 d)
  have hK4 : 0 < K4 d L N T.BG T.κ := by
    obtain ⟨hC⟩ := T.core
    exact K4_pos hC.hS.fam.2.1 (by have := T.hd; omega)
  have hc2 : 0 < cK2 d L N := cK2_pos d L N
  have hc2' : 0 ≤ cK2' d L N (famConst d L T.BG₂ T.κ) := cK2'_nonneg T.fam_nonneg
  have hC4 : (8 : ℝ) ≤ compC4 d := compC4_ge d
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hxt : xiC1 d * t' ≤ xiC1 d * T.t := mul_le_mul_of_nonneg_left htT hX.le
  have hdm : decDomMargin d L N T.BG T.κ (xiC1 d * t') ≤
      decDomMargin d L N T.BG T.κ (xiC1 d * T.t) := by
    unfold decDomMargin
    have h0 : 0 ≤ xiC1 d * t' := by positivity
    have h1 : K4 d L N T.BG T.κ * (xiC1 d * t') ≤ K4 d L N T.BG T.κ * (xiC1 d * T.t) :=
      mul_le_mul_of_nonneg_left hxt hK4.le
    have h2 : 0 ≤ K4 d L N T.BG T.κ * (xiC1 d * t') := by positivity
    have h3 : K4 d L N T.BG T.κ * (xiC1 d * t') *
        (K4 d L N T.BG T.κ * (xiC1 d * t') + 2 * (1 + 3 * (xiC1 d * t'))) ≤
        K4 d L N T.BG T.κ * (xiC1 d * T.t) *
        (K4 d L N T.BG T.κ * (xiC1 d * T.t) + 2 * (1 + 3 * (xiC1 d * T.t))) :=
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
    xi_small := by linarith [T.xi_small] }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- **A tower at any smaller step radius, with the other parameters unchanged.** -/
theorem exists_stepTower_shrink {κmin : ℝ} (T : StepTower κmin) {t' : ℝ} (ht0 : 0 < t')
    (htT : t' ≤ T.t) :
    ∃ T' : StepTower κmin, T'.t = t' ∧ T'.m₁ = T.m₁ ∧ T'.c = T.c ∧ T'.BG = T.BG ∧
      T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧ T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' := by
  obtain ⟨T', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := T.toG.exists_shrink ht0 htT
  exact ⟨T'.ofThree (h11.trans T.κ0_eq) (h12.trans rfl), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Balaban.Inhabited
