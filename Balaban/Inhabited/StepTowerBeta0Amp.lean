/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Marks
public import Balaban.Inhabited.StepTowerChainStructAmp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# The source amplitude at a physical source, uniformly in the step radius

`sourceAmp_scale_general_agree`: the statement of `sourceAmp_scale_general` with the radius `t` a
variable after the threshold (`t ≥ c L^{-α(k+1)}`, `2 α < d - 2`; the cutoff condition is
`p₁ ≤ (κ₁/16) √b` with `κ₁ ∝ t`).  `StepTower.exists_beta0_amp_agree`: the first entry of the
numerical condition of the composed activity, for towers that agree with `T₀` on `m₁, BG, BG₂, κ`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

namespace LevelStep

/-- **The amplitude at a physical source at every scale, uniformly in the step radius.** -/
theorem sourceAmp_scale_general_agree {d L N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 1 ≤ N)
    {A₁ κ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₁ : ℝ, 3 ≤ β₁ ∧ ∀ (k : ℕ) (β t b : ℝ), b = β * (L : ℝ) ^ (k * (d - 2)) → β₁ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p b →
      0 < lvRG d L N κ t b p₁ ∧ ∀ P K q : ℝ, 0 ≤ P → 0 ≤ K → 0 ≤ q →
        b * (P / (lvRG d L N κ t b p₁) ^ 3) + q * K / lvRG d L N κ t b p₁ ≤
          P * (4 * A₁ / lvKappaG d L N κ t) ^ 3 * (Real.log b) ^ (3 * p) / Real.sqrt b +
          q * (4 * A₁ * K / lvKappaG d L N κ t) * (Real.log b) ^ p / Real.sqrt b := by
  have hd0 : 0 < d := by omega
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hCm := covSupMaxC_nonneg_general (N := N) hd0 hL κ
  set κ₀ : ℝ := 1 / (2 * Real.sqrt (N : ℝ) * (covSupMaxC d L N κ + 1)) with hκ₀
  have hκ₀0 : 0 < κ₀ := by rw [hκ₀]; positivity
  obtain ⟨β₂, hβ₂, H⟩ := exists_beta0_pLog_le_t_sqrt hd hL hA.le p hc (c' := κ₀ / 16) (by positivity)
    hα
  refine ⟨β₂, hβ₂, ?_⟩
  intro k β t b hb hβ hct p₁ hp0 hp₁
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hct
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hβ3 : 3 ≤ β := by linarith
  have hbβ : β ≤ b := by rw [hb]; nlinarith
  have hexp : Real.exp 1 ≤ b := by
    have := Real.exp_one_lt_three
    linarith
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  set κ₁ : ℝ := lvKappaG d L N κ t with hκ₁def
  have hκ₁t : κ₁ = κ₀ * t := by rw [hκ₁def, hκ₀]; unfold lvKappaG; field_simp
  have hκ₁ : 0 < κ₁ := by rw [hκ₁t]; positivity
  have hℓ : 1 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 hexp
  have hx1 : 1 ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  have hw1 : 1 ≤ (Real.log b) ^ p := one_le_pow₀ hℓ
  have hpL : pLog A₁ p b = A₁ * (Real.log b) ^ p := rfl
  have hp16 : p₁ ≤ κ₁ / 16 * Real.sqrt b := by
    have := H k β t p₁ (by linarith) hct hp0 (by rw [← hb]; exact hp₁)
    rw [hκ₁t, ← hb] at *
    calc p₁ ≤ κ₀ / 16 * t * Real.sqrt b := this
      _ = κ₀ * t / 16 * Real.sqrt b := by ring
  have hcψeq : lvCpsiG d L N κ t b = κ₁ * Real.sqrt b := lvCpsiG_eq d L N κ t b
  have hc16 : 16 * p₁ ≤ lvCpsiG d L N κ t b := by rw [hcψeq]; linarith
  have e : 4 * p₁ * lvRG d L N κ t b p₁ = 2 * lvCpsiG d L N κ t b - 16 * p₁ := by
    unfold lvRG; field_simp; ring
  have hcψ0 : 0 < lvCpsiG d L N κ t b := by rw [hcψeq]; positivity
  have hr0 : 0 < lvRG d L N κ t b p₁ := by
    by_contra h
    have h := not_lt.1 h
    have : 4 * p₁ * lvRG d L N κ t b p₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hrbound : κ₁ * Real.sqrt b ≤ 4 * A₁ * (Real.log b) ^ p * lvRG d L N κ t b p₁ := by
    calc κ₁ * Real.sqrt b = lvCpsiG d L N κ t b := hcψeq.symm
      _ ≤ 2 * lvCpsiG d L N κ t b - 16 * p₁ := by linarith
      _ = 4 * p₁ * lvRG d L N κ t b p₁ := e.symm
      _ ≤ 4 * pLog A₁ p b * lvRG d L N κ t b p₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
      _ = _ := by rw [hpL]; ring
  refine ⟨hr0, fun P K q hP hK hq => ?_⟩
  have hamp := sourceAmp_le (x := Real.sqrt b) (w := (Real.log b) ^ p)
    (r := lvRG d L N κ t b p₁) (P := P) (K := K) (A := A₁) (κ₁ := κ₁) (q := q) hx1 hw1 hA hκ₁
    hP hK hq hrbound
  rwa [Real.sq_sqrt hb0.le, ← pow_mul, show p * 3 = 3 * p by ring] at hamp

end LevelStep

end Balaban.Inhabited
