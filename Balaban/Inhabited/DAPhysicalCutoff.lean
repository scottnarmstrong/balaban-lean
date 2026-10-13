/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The logarithmic fluctuation cutoff of the papers

The fluctuation cutoff of P4 (2.38)-(2.40) is `p₁(β) = A₁ (log β)^p`.  `pLog A₁ p β` is this
function.  We prove that it is positive for `β > 1`, increasing for `β ≥ 1`, and that it is
eventually small against `√β`: with `H = A₁ (4p/e)^p`, the bound
`(log β)^p ≤ (4p/e)^p β^{1/4}` gives `pLog A₁ p β / √β ≤ c` as soon as `β ≥ (H/c)^4`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Real

/-- **The cutoff of the papers**, `p₁(β) = A₁ (log β)^p`. -/
noncomputable def pLog (A₁ : ℝ) (p : ℕ) (β : ℝ) : ℝ := A₁ * (Real.log β) ^ p

/-- The constant `A₁ (4p/e)^p` of the elementary bound. -/
noncomputable def pLogConst (A₁ : ℝ) (p : ℕ) : ℝ := A₁ * (4 * p / Real.exp 1) ^ p

/-- The threshold `(A₁ (4p/e)^p / c)^4` beyond which `pLog / √β ≤ c`. -/
noncomputable def pLogThreshold (A₁ : ℝ) (p : ℕ) (c : ℝ) : ℝ := (pLogConst A₁ p / c) ^ 4

theorem pLog_pos {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {β : ℝ} (hβ : 1 < β) : 0 < pLog A₁ p β := by
  unfold pLog
  have := Real.log_pos hβ
  positivity

theorem pLog_nonneg {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) {β : ℝ} (hβ : 1 ≤ β) : 0 ≤ pLog A₁ p β := by
  unfold pLog
  have := Real.log_nonneg hβ
  positivity

theorem pLog_mono {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) {β β' : ℝ} (hβ : 1 ≤ β) (h : β ≤ β') :
    pLog A₁ p β ≤ pLog A₁ p β' := by
  unfold pLog
  have h0 := Real.log_nonneg hβ
  have h1 := Real.log_le_log (by linarith) h
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 p) hA

/-- `y ≤ (4p/e) exp(y/(4p))` for `y ≥ 0`, `p ≥ 1`. -/
theorem le_const_mul_exp {y : ℝ} (p : ℕ) (hp : 1 ≤ p) :
    y ≤ (4 * p / Real.exp 1) * Real.exp (y / (4 * p)) := by
  have hp0 : (0 : ℝ) < 4 * p := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h := Real.add_one_le_exp (y / (4 * p) - 1)
  have he : Real.exp (y / (4 * p)) = Real.exp 1 * Real.exp (y / (4 * p) - 1) := by
    rw [← Real.exp_add]; ring_nf
  have he0 := Real.exp_pos 1
  rw [he]
  have : (4 * p / Real.exp 1) * (Real.exp 1 * Real.exp (y / (4 * p) - 1)) =
      4 * p * Real.exp (y / (4 * p) - 1) := by field_simp
  rw [this]
  have h2 : y / (4 * p) ≤ Real.exp (y / (4 * p) - 1) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hp0.le
  have h4 : 4 * (p : ℝ) * (y / (4 * p)) = y := by field_simp
  linarith

/-- **`(log β)^p ≤ (4p/e)^p β^{1/4}`**, with `β^{1/4} = exp(log β / 4)`, for `β ≥ 1`. -/
theorem log_pow_le (p : ℕ) {β : ℝ} (hβ : 1 ≤ β) :
    (Real.log β) ^ p ≤ (4 * p / Real.exp 1) ^ p * Real.exp (Real.log β / 4) := by
  have hy := Real.log_nonneg hβ
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp; linarith
  have h := le_const_mul_exp (y := Real.log β) p hp
  calc (Real.log β) ^ p ≤ ((4 * p / Real.exp 1) * Real.exp (Real.log β / (4 * p))) ^ p :=
        pow_le_pow_left₀ hy h p
    _ = (4 * p / Real.exp 1) ^ p * Real.exp (Real.log β / 4) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        have : (p : ℝ) ≠ 0 := by positivity
        field_simp

/-- **The cutoff is eventually small against `√β`**: for `A₁ ≥ 0`, `c > 0` and
`β ≥ (A₁ (4p/e)^p / c)^4` (and `β ≥ 1`), `pLog A₁ p β ≤ c √β`. -/
theorem pLog_le_mul_sqrt {A₁ : ℝ} (hA : 0 ≤ A₁) (p : ℕ) {c : ℝ} (hc : 0 < c) {β : ℝ}
    (hβ1 : 1 ≤ β) (hβ : pLogThreshold A₁ p c ≤ β) : pLog A₁ p β ≤ c * Real.sqrt β := by
  set u : ℝ := Real.exp (Real.log β / 4) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hu4 : u ^ 4 = β := by
    rw [hu, ← Real.exp_nat_mul]
    have : ((4 : ℕ) : ℝ) * (Real.log β / 4) = Real.log β := by push_cast; ring
    rw [this, Real.exp_log (by linarith)]
  have hsq : Real.sqrt β = u ^ 2 := by
    rw [← hu4, show u ^ 4 = (u ^ 2) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hH : 0 ≤ pLogConst A₁ p := by
    unfold pLogConst; positivity
  have hw : pLogConst A₁ p / c ≤ u := by
    have h4 : (pLogConst A₁ p / c) ^ 4 ≤ u ^ 4 := by rw [hu4]; exact hβ
    exact le_of_pow_le_pow_left₀ (by norm_num) hu0.le h4
  have hlog := log_pow_le p hβ1
  have h1 : pLog A₁ p β ≤ pLogConst A₁ p * u := by
    unfold pLog pLogConst
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hlog hA
  rw [hsq]
  have h2 : pLogConst A₁ p ≤ c * u := by
    rw [div_le_iff₀ hc] at hw; linarith
  calc pLog A₁ p β ≤ pLogConst A₁ p * u := h1
    _ ≤ (c * u) * u := mul_le_mul_of_nonneg_right h2 hu0.le
    _ = c * u ^ 2 := by ring

end Balaban.Inhabited
