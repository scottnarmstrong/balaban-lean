/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTower
public import Balaban.Inhabited.LevelStepSettingGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The scale constants of the ray margin for general `d`, `L`, `N`

The constants `lvKappa`, `lvCpsi`, `lvR` of `LevelRayTower` (dimension 3, block size 3, `N = 2`)
for general `d`, `L`, `N`:
`lvCpsiG d L N κ t b = t √b / (2 √N (C_max + 1))` with `C_max = covSupMaxC d L N κ`, and
`lvRG d L N κ t b p₁ = lvCpsiG d L N κ t b / (2 p₁) - 4`.  At `(3, 3, 2)` they are the landed ones.

The numeral `2` of `lvKappa` is `N` (in `√N`) and the three numerals of `covSupMaxC 3 3 2 κ` are
`d`, `L`, `N`; the other numerals (`2` in the denominator, `1`, `4`) are step numerals.

`scale_C_items_numeric`: for `d ≥ 2`, `L ≥ 3`, `N ≥ 1`, `κ`, `t`, `A₁ > 0` there is `β₀`, not
depending on the scale `k ≥ 1`, such that for `β ≥ β₀`, `b = β L^{k(d-2)}` (the block coupling,
`hatStepKG_betaU`) and `0 < p₁ ≤ pLog A₁ p b` the radius `c_ψ` and the source radius `r` are
positive, `(4 + r) p₁ < c_ψ`, and the fluctuation radius inequality holds.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization

namespace LevelStep

/-- The constant `κ₁ = t / (2 √N (C_max + 1))` of the radii, for general `d`, `L`, `N`. -/
noncomputable def lvKappaG (d L N : ℕ) (κ t : ℝ) : ℝ :=
  t / (2 * Real.sqrt (N : ℝ) * (covSupMaxC d L N κ + 1))

/-- The radius `c_ψ` at the scale, as a function of `b`, for general `d`, `L`, `N`. -/
noncomputable def lvCpsiG (d L N : ℕ) (κ t b : ℝ) : ℝ :=
  t * Real.sqrt b / (2 * Real.sqrt (N : ℝ) * (covSupMaxC d L N κ + 1))

/-- The source radius `r = c_ψ/(2 p₁) - 4`, for general `d`, `L`, `N`. -/
noncomputable def lvRG (d L N : ℕ) (κ t b p₁ : ℝ) : ℝ := lvCpsiG d L N κ t b / (2 * p₁) - 4

theorem lvKappaG_three (κ t : ℝ) : lvKappaG 3 3 2 κ t = lvKappa κ t := rfl

theorem lvCpsiG_three (κ t b : ℝ) : lvCpsiG 3 3 2 κ t b = lvCpsi κ t b := rfl

theorem lvRG_three (κ t b p₁ : ℝ) : lvRG 3 3 2 κ t b p₁ = lvR κ t b p₁ := rfl

theorem covSupMaxC_nonneg_general {d L N : ℕ} (hd : 0 < d) (hL : 3 ≤ L) (κ : ℝ) :
    0 ≤ covSupMaxC d L N κ := by
  have ha : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  exact (covSupConstC_nonneg (N := N) hd hL one_pos κ).trans
    (covSupConstC_le_covSupMaxC hd hL κ ha)

/-- For `L ≥ 3` the weight `a_k = compWeight L 1 k` of the step lies in `[1/2, 2]` at every
scale `k ≥ 1`. -/
theorem compWeight_one_mem {L : ℕ} (hL : 3 ≤ L) {k : ℕ} (hk : 1 ≤ k) :
    compWeight L (1 : ℝ) k ∈ Set.Icc (1 / 2 : ℝ) 2 :=
  compWeight_mem_Icc hL (by norm_num) (by norm_num) hk

theorem lvKappaG_pos {d L N : ℕ} (hd : 0 < d) (hL : 3 ≤ L) (hN : 1 ≤ N) (κ : ℝ) {t : ℝ}
    (ht : 0 < t) : 0 < lvKappaG d L N κ t := by
  have := covSupMaxC_nonneg_general (N := N) hd hL κ
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  unfold lvKappaG
  positivity

theorem lvCpsiG_eq (d L N : ℕ) (κ t b : ℝ) :
    lvCpsiG d L N κ t b = lvKappaG d L N κ t * Real.sqrt b := by
  unfold lvCpsiG lvKappaG
  ring

/-- **The numeric threshold at every scale.**  The threshold `β₀` does not depend on `k ≥ 1`;
`b = β L^{k(d-2)}` is the block coupling of `hatStepKG`. -/
theorem scale_C_items_numeric {d L N : ℕ} (hd : 2 ≤ d) (hL : 3 ≤ L) (hN : 1 ≤ N) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {t : ℝ} (κ : ℝ) (ht : 0 < t) :
    ∃ β₀ : ℝ, 2 ≤ β₀ ∧ ∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      0 < lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) ∧
      0 < lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁ ∧
      Real.sqrt (N : ℝ) *
        (‖(((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC d L N (compWeight L (1 : ℝ) k) κ *
            lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))))) < t ∧
      ((2 : ℝ) * 2 + lvRG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ <
        lvCpsiG d L N κ t (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hd0 : 0 < d := by omega
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hCm := covSupMaxC_nonneg_general (N := N) hd0 hL κ
  set κ₁ : ℝ := lvKappaG d L N κ t with hκ₁
  have hκ₁0 : 0 < κ₁ := lvKappaG_pos hd0 hL hN κ ht
  refine ⟨max 2 (pLogThreshold A₁ p (κ₁ / 16)), le_max_left _ _, ?_⟩
  intro k hk β hβ p₁ hp0 hp₁
  have hβ2 : 2 ≤ β := (le_max_left _ _).trans hβ
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  set b : ℝ := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hbβ : β ≤ b := by rw [hb]; nlinarith
  have hb1 : (1 : ℝ) < b := by linarith
  have hb0 : 0 < b := by linarith
  have hle : p₁ ≤ κ₁ / 16 * Real.sqrt b :=
    hp₁.trans (pLog_le_mul_sqrt hA.le p (by positivity) hb1.le
      (((le_max_right _ _).trans hβ).trans hbβ))
  set T : ℝ := Real.sqrt b with hT
  have hT0 : 0 < T := Real.sqrt_pos.2 hb0
  have hcψ : lvCpsiG d L N κ t b = κ₁ * T := lvCpsiG_eq d L N κ t b
  have hcψ0 : 0 < lvCpsiG d L N κ t b := by rw [hcψ]; positivity
  have h8 : 8 * p₁ < lvCpsiG d L N κ t b := by
    rw [hcψ]
    have h4 : 0 < κ₁ * T := by positivity
    nlinarith
  have hr0 : 0 < lvRG d L N κ t b p₁ := by
    unfold lvRG
    have : 4 < lvCpsiG d L N κ t b / (2 * p₁) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  refine ⟨hcψ0, hr0, ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hcψ]
    have e : b ^ (-(1 / 2 : ℝ)) = T⁻¹ := by
      rw [Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow]
    rw [e]
    have hmem := compWeight_one_mem hL hk
    have hC0 : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) κ :=
      covSupConstC_nonneg hd0 hL (by linarith [hmem.1]) κ
    have hCle : covSupConstC d L N (compWeight L (1 : ℝ) k) κ ≤ covSupMaxC d L N κ :=
      covSupConstC_le_covSupMaxC hd0 hL κ hmem
    have e2 : Real.sqrt (N : ℝ) * (T⁻¹ *
        (covSupConstC d L N (compWeight L (1 : ℝ) k) κ * (κ₁ * T))) =
        covSupConstC d L N (compWeight L (1 : ℝ) k) κ * t / (2 * (covSupMaxC d L N κ + 1)) := by
      rw [hκ₁]; unfold lvKappaG; field_simp
    rw [e2, div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold lvRG
    have : (2 * 2 + (lvCpsiG d L N κ t b / (2 * p₁) - 4)) * p₁ = lvCpsiG d L N κ t b / 2 := by
      field_simp; ring
    rw [this]
    linarith

end LevelStep

end Balaban.Inhabited
