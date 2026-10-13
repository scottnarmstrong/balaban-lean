/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.DetCauchyGraph
public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.DetOutputTermsWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant rate conditions for general `d` and `L`

For arbitrary `d`, `L` the condition `(detDeg d L + 1)² · 2 / e^κ < 1` follows from
`log 2 + 2 log (detDeg d L + 1) < κ`; the rate
`detRateG d L κ = (κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` is positive exactly under this
hypothesis and is monotone in `κ`; and the hull rate satisfies `kout ≤ hullRate d L (detRateG d L κ)`
as soon as `2 d L (1 + B) (kout + c₁ log 2) + log 2 + 2 log (detDeg d L + 1) ≤ κ`.  The landed
`d = L = 3` statements are the instances (`detRateG_three`, `detDeg_three_rate_of_general`,
`hullRate_ge_of_le_of_general`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Inhabited

lemma detDeg_succ_pos' (d L : ℕ) : (0 : ℝ) < ((detDeg d L + 1 : ℕ) : ℝ) := by
  exact_mod_cast Nat.succ_pos _

/-- **The determinant rate condition for general `d`, `L`.** -/
theorem detDeg_rate_general (d L : ℕ) {κ : ℝ}
    (hκ : Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) < κ) :
    ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 := by
  have hD := detDeg_succ_pos' d L
  rw [mul_div_assoc', div_lt_one (Real.exp_pos κ)]
  have e : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * 2 =
      Real.exp (Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) := by
    have h2 : 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) =
        Real.log (((detDeg d L + 1 : ℕ) : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; ring
    rw [Real.exp_add, Real.exp_log (by norm_num), h2, Real.exp_log (by positivity)]
    ring
  rw [e]
  exact Real.exp_lt_exp.2 hκ

/-- The determinant rate `(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)`. -/
noncomputable def detRateG (d L : ℕ) (κ : ℝ) : ℝ :=
  (κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)

/-- The rate is positive exactly under the hypothesis of `detDeg_rate_general`. -/
theorem detRateG_pos_iff {d L : ℕ} (hd : 0 < d) (hL : 0 < L) {κ : ℝ} :
    0 < detRateG d L κ ↔ Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) < κ := by
  have h : (0 : ℝ) < 2 * d * L := by positivity
  unfold detRateG
  rw [div_pos_iff_of_pos_right h]
  constructor <;> intro x <;> linarith

theorem detRateG_mono {d L : ℕ} (hd : 0 < d) (hL : 0 < L) : Monotone (detRateG d L) := by
  intro a b hab
  have h : (0 : ℝ) < 2 * d * L := by positivity
  unfold detRateG
  exact div_le_div_of_nonneg_right (by linarith) h.le

/-- The general rate at `d = L = 3` is the landed `towerDetRate`. -/
theorem detRateG_three (κ : ℝ) : detRateG 3 3 κ = towerDetRate κ := by
  unfold detRateG towerDetRate
  norm_num

/-- **The hull rate for general `d`, `L`.** -/
theorem hullRate_ge_general {d L : ℕ} (hd : 0 < d) (hL : 0 < L) [NeZero L] {κ kout : ℝ}
    (h : 2 * d * L * (1 + collarB d L) * (kout + c1 d L * Real.log 2) + Real.log 2 +
      2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ κ) :
    kout ≤ hullRate d L (detRateG d L κ) := by
  have hB := collarB_nonneg d L
  have hp : (0 : ℝ) < 2 * d * L := by positivity
  have hq : (0 : ℝ) < 1 + collarB d L := by linarith
  unfold hullRate
  have : kout + c1 d L * Real.log 2 ≤ detRateG d L κ / (1 + collarB d L) := by
    rw [le_div_iff₀ hq]
    unfold detRateG
    rw [le_div_iff₀ hp]
    nlinarith [h]
  linarith

/-- The landed hypothesis `57 ≤ κ` implies the general one at `d = L = 3`. -/
theorem detDeg_three_rate_of_general {κ : ℝ} (hκ : 57 ≤ κ) :
    ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 :=
  detDeg_rate_general 3 3 (lt_of_lt_of_le log_detDeg_three_lt hκ)

/-- The landed `hullRate_ge_of_le` as the instance `d = L = 3` of `hullRate_ge_general`. -/
theorem hullRate_ge_of_le_of_general {κ kout : ℝ}
    (h : 18 * 60751 * (kout + 3375 * Real.log 2) + Real.log 2 +
      2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) ≤ κ) :
    kout ≤ hullRate 3 3 (towerDetRate κ) := by
  rw [← detRateG_three]
  refine hullRate_ge_general (by norm_num) (by norm_num) ?_
  rw [collarB_three, c1_three]
  norm_num
  push_cast at h ⊢
  linarith

end Balaban.Fluctuation
