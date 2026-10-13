/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Balaban.Inhabited.LevelRayTowerGeneral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
/-!
# The amplitude at every scale for general `d`, `L`, `N`
`scale_amp_exists_general` is `scale_amp_exists` with the radius `lvRG d L N κ t b p₁`.  The
numerals `3, 3, 2` of the landed statement are `d, L, N`; the numerals `16`, `4`, `3` in the proof are
step numerals (the cutoff share `κ₁/16`, the factor `4 p₁ r = 2 c_ψ - 16 p₁`, the cube).
-/
@[expose] public section
namespace Balaban.Inhabited
open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Filter Topology
namespace LevelStep
/-- **The amplitude at every scale is at most `C (log b)^{3p}/√b`**, general `d`, `L`, `N`. -/
theorem scale_amp_exists_general {d L N : ℕ} (hd : 0 < d) (hL : 3 ≤ L) (hN : 1 ≤ N) {A₁ κ t P K : ℝ} (hA : 0 < A₁) (p : ℕ) (ht : 0 < t) (hP : 0 ≤ P)
    (hK : 0 ≤ K) :
    ∃ β₁ C : ℝ, Real.exp 1 ≤ β₁ ∧ 0 < C ∧ ∀ b : ℝ, β₁ ≤ b → ∀ β : ℝ, 1 ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p b →
      b * (P / (lvRG d L N κ t b p₁) ^ 3) + K / (β * lvRG d L N κ t b p₁) ≤
        C * (Real.log b) ^ (3 * p) / Real.sqrt b := by
  set κ₁ : ℝ := lvKappaG d L N κ t with hκ₁def
  have hκ₁ : 0 < κ₁ := lvKappaG_pos hd hL hN κ ht
  have hthr : 0 < κ₁ / 16 := by positivity
  refine ⟨max (Real.exp 1) (pLogThreshold A₁ p (κ₁ / 16)),
    P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁ + 1, le_max_left _ _, by positivity, ?_⟩
  intro b hb β hβ p₁ hp0 hp₁
  have hexp : Real.exp 1 ≤ b := le_trans (le_max_left _ _) hb
  have hbp : pLogThreshold A₁ p (κ₁ / 16) ≤ b := le_trans (le_max_right _ _) hb
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hexp
  have hb0 : 0 < b := by linarith
  have hℓ : 1 ≤ Real.log b := (Real.le_log_iff_exp_le hb0).2 hexp
  have hx1 : 1 ≤ Real.sqrt b := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  have hw1 : 1 ≤ (Real.log b) ^ p := one_le_pow₀ hℓ
  have hpL : pLog A₁ p b = A₁ * (Real.log b) ^ p := rfl
  have hp16 : pLog A₁ p b ≤ κ₁ / 16 * Real.sqrt b := pLog_le_mul_sqrt hA.le p hthr hb1 hbp
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
  have hamp := scale_amp_le (x := Real.sqrt b) (w := (Real.log b) ^ p)
    (r := lvRG d L N κ t b p₁) (P := P) (K := K) (A := A₁) (κ₁ := κ₁) (β := β) hx1 hw1 hA hκ₁
    hP hK hrbound hβ
  rw [Real.sq_sqrt hb0.le, ← pow_mul, show p * 3 = 3 * p by ring] at hamp
  refine hamp.trans ?_
  have : 0 ≤ (Real.log b) ^ (3 * p) / Real.sqrt b := by positivity
  calc _ = (P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁) *
        ((Real.log b) ^ (3 * p) / Real.sqrt b) := by ring
    _ ≤ (P * (4 * A₁ / κ₁) ^ 3 + 4 * A₁ * K / κ₁ + 1) *
        ((Real.log b) ^ (3 * p) / Real.sqrt b) :=
      mul_le_mul_of_nonneg_right (by linarith) this
    _ = _ := by ring


end LevelStep
end Balaban.Inhabited
