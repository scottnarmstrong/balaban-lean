/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalCfinInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The invertibility polydisc of the square-root cut family does not reach the unit cube

`taggedCfin_isUnit_near_one` gives invertibility of `C(s)` on `‖s p - 1‖ ≤ δ` when
`B δ ≤ (e^κ - 1)/2`, with `B = B_C² A_U + 1`.  The polydisc radius is therefore at most
`(e^κ - 1)/(2B)`.  Here `B_C ≥ (8/3) e^{H κ}` and `A_U ≥ 2`, so
`B ≥ 1 + (128/9) e^{2 H κ}` with `H = pdH d ≥ 1`, and the radius is at most
`(9/256) e^{(1 - 2H) κ} ≤ 9/256`, for every `κ ≥ 0`, every `M` and every admissible `r`.
In particular the polydisc never contains the interpolation cube `[0,1]^P`
(whose points are at distance `1` from `s = 1`).
-/

@[expose] public section

namespace Balaban.Green

variable {d L : ℕ} [NeZero L]

theorem one_le_ballConst {r : ℝ} (hr : 0 < r) : 1 ≤ ballConst d r := by
  have hq : Real.exp (-r) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hq0 : 0 < Real.exp (-r) := Real.exp_pos _
  unfold ballConst
  refine one_le_pow₀ ?_
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem finalGap_le_one : finalGap d L ≤ 1 := by
  unfold finalGap
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [div_le_one (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hL) (sub_nonneg.2 hL)]

theorem one_le_pdH (d : ℕ) : 1 ≤ pdH d := by
  unfold pdH
  have h1 : (1 : ℝ) ≤ 16 ^ d := one_le_pow₀ (by norm_num)
  have h2 : (0 : ℝ) ≤ 9 * d * 7 ^ d := by positivity
  linarith

/-- **(A), lower bound for the defect constant.**  For `κ ≥ 0` and `0 ≤ r ≤ ε/8`,
`B = B_C² A_U + 1 ≥ 1 + (128/9) e^{2 H κ}` (any real `κ`) with `H = pdH d`. -/
theorem defect_constant_ge (hd : 0 < d) {κ r : ℝ} (hr : r ≤ pdEps d L / 8) :
    1 + 128 / 9 * Real.exp (2 * (pdH d * κ)) ≤
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (finalDecayC d L * ballConst d (blockDecayRate d - r)) + 1 := by
  have hε := pdEps_pos (d := d) (L := L) hd
  have hδ0 : pdEps d L ≤ blockDecayRate d := min_le_left _ _
  have hb1 := one_le_ballConst (d := d) (r := pdEps d L / 2) (by linarith)
  have hb2 := one_le_ballConst (d := d) (r := blockDecayRate d - r) (by linarith)
  have hsq0 : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 (finalGap_pos (NeZero.pos L))
  have hsq1 : Real.sqrt (finalGap d L) ≤ 1 := Real.sqrt_le_one.2 finalGap_le_one
  have hE : 0 < Real.exp (pdH d * κ) := Real.exp_pos _
  have hBC : 8 / 3 * Real.exp (pdH d * κ) ≤
      4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L) := by
    rw [le_div_iff₀ hsq0]
    nlinarith [mul_le_mul_of_nonneg_left hsq1 hE.le, mul_le_mul_of_nonneg_left hb1 hE.le]
  have hAU : 2 ≤ finalDecayC d L * ballConst d (blockDecayRate d - r) := by
    have h2 : 2 ≤ finalDecayC d L := by
      unfold finalDecayC
      have := blockDecayConst_pos (L := L) hd
      linarith
    nlinarith
  have hsq : Real.exp (2 * (pdH d * κ)) = Real.exp (pdH d * κ) * Real.exp (pdH d * κ) := by
    rw [← Real.exp_add]; ring_nf
  have hp : 0 ≤ 8 / 3 * Real.exp (pdH d * κ) := by positivity
  have hm := mul_le_mul hBC hBC hp (le_trans hp hBC)
  have hm2 := mul_le_mul hm hAU (by norm_num) (by positivity)
  rw [hsq]
  nlinarith

/-- **(A), the polydisc never reaches the unit cube.**  Under the hypothesis of
`taggedCfin_isUnit_near_one`, `δ < 9/256`, for every `κ ≥ 0`.  Equivalently the radius
`(e^κ - 1)/(2B)` is at most `9/256`, so `taggedCfin_isUnit_near_one` never applies to the
points of `[0,1]^P` at distance `1` from `s = 1`. -/
theorem polydisc_radius_lt_one (hd : 0 < d) {κ r δ : ℝ} (hκ : 0 ≤ κ)
    (hr : r ≤ pdEps d L / 8) (hδ0 : 0 < δ)
    (hq : ((4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) *
      (finalDecayC d L * ballConst d (blockDecayRate d - r)) + 1) * δ ≤ (Real.exp κ - 1) / 2) :
    δ < 9 / 256 := by
  have hB := defect_constant_ge (L := L) (κ := κ) hd hr
  have hH := one_le_pdH d
  have hE : Real.exp κ ≤ Real.exp (2 * (pdH d * κ)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hE0 : 0 < Real.exp (2 * (pdH d * κ)) := Real.exp_pos _
  have h1 : (1 + 128 / 9 * Real.exp (2 * (pdH d * κ))) * δ ≤ (Real.exp κ - 1) / 2 :=
    le_trans (mul_le_mul_of_nonneg_right hB hδ0.le) hq
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon (by positivity : (0 : ℝ) ≤ 128 / 9 *
    Real.exp (2 * (pdH d * κ)))]

end Balaban.Green
