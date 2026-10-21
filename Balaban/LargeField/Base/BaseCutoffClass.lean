/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCutoffChi1
public import Balaban.LargeField.Analytic.Constants

/-!
# The margin inequalities at the constants of the class

The hypotheses of `baseSectorCubeProduct_eq_one_of_chi1` are three numerical conditions:

* `δ₁ ≤ δ₀/2` for the scale-one tolerance `δ₁ = (β₁ a)^{-1/2} p₀(β₁)` against `δ₀ = (β₀ a)^{-1/2}
  p₀(β₀)`: with `β₁ = β₀ L^{d-2}` and `(d-2) log L ≤ log (β₀ a)` this holds as soon as
  `L^{(d-2)/2} ≥ 2^{p₀+1}` (`deltaRun_one_le_half`);
* `√N E ≤ δ₀/8` for the closeness `E = K_w c_F (2d+2) K₁ (4dLδ₀) e^{-γ_w c M₁}`: this is the
  condition `γ_w c M₁ ≥ log (32 √N K_w c_F (2d+2) K₁ d L)` on the cube size, independent of `δ₀`
  (`exp_term_small`);
* `3 ρ/√β ≤ δ₀/4` for `ρ = N ‖W‖_row p₁`: `N ‖W‖_row p₁ ≤ a^{-1/2} p₀/12`, i.e. `p₁/p₀ ≤
  1/(12 N √a ‖W‖_row)` (`tangent_small`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban

/-- **`δ₁ ≤ δ₀/2`**: the scale-one tolerance against the base tolerance. -/
theorem deltaRun_one_le_half {A0 a : ℝ} {p0 : ℕ} {b : ℕ → ℝ} {L d : ℕ} (hA0 : 0 < A0)
    (ha : 0 < a) (hb0 : 0 < b 0) (hb1 : b 1 = b 0 * (L : ℝ) ^ (d - 2)) (hL1 : 1 < L)
    (hlam : ((d - 2 : ℕ) : ℝ) * Real.log L ≤ Real.log (b 0 * a))
    (hpos : 0 < Real.log (b 0 * a))
    (hLd : (2 : ℝ) ^ (p0 + 1) ≤ (L : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2)) :
    deltaRun A0 p0 a b 1 ≤ deltaRun A0 p0 a b 0 / 2 := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (lt_trans zero_lt_one hL1)
  have hLpow : (0 : ℝ) < (L : ℝ) ^ (d - 2) := by positivity
  have hx : 0 < b 0 * a := mul_pos hb0 ha
  have hb1a : b 1 * a = (b 0 * a) * (L : ℝ) ^ (d - 2) := by rw [hb1]; ring
  have hlog1 : Real.log (b 1 * a) = Real.log (b 0 * a) + ((d - 2 : ℕ) : ℝ) * Real.log L := by
    rw [hb1a, Real.log_mul hx.ne' hLpow.ne', Real.log_pow]
  have hlam1 : Real.log (b 1 * a) ≤ 2 * Real.log (b 0 * a) := by rw [hlog1]; linarith
  have hlam1pos : 0 < Real.log (b 1 * a) := by
    rw [hlog1]; have : 0 ≤ ((d - 2 : ℕ) : ℝ) * Real.log L := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ L by exact_mod_cast hL1.le)
      positivity
    linarith
  have hrp : (b 1 * a) ^ (-(1 / 2 : ℝ)) =
      (b 0 * a) ^ (-(1 / 2 : ℝ)) * ((L : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2))⁻¹ := by
    rw [hb1a, Real.mul_rpow hx.le hLpow.le, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le,
      show ((d - 2 : ℕ) : ℝ) * -(1 / 2) = -(((d - 2 : ℕ) : ℝ) / 2) by ring, Real.rpow_neg hL0.le]
  unfold deltaRun pZero runLam
  rw [hrp]
  have hx0 : 0 ≤ (b 0 * a) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  have hp : Real.log (b 1 * a) ^ p0 ≤ 2 ^ p0 * Real.log (b 0 * a) ^ p0 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hlam1pos.le hlam1 p0
  have hinv : ((L : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2))⁻¹ ≤ ((2 : ℝ) ^ (p0 + 1))⁻¹ :=
    inv_anti₀ (by positivity) hLd
  have hlp : 0 ≤ Real.log (b 0 * a) ^ p0 := pow_nonneg hpos.le _
  have hinv0 : 0 ≤ ((L : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2))⁻¹ := by positivity
  calc (b 0 * a) ^ (-(1 / 2 : ℝ)) * ((L : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2))⁻¹ *
        (A0 * Real.log (b 1 * a) ^ p0)
      ≤ (b 0 * a) ^ (-(1 / 2 : ℝ)) * ((2 : ℝ) ^ (p0 + 1))⁻¹ *
        (A0 * (2 ^ p0 * Real.log (b 0 * a) ^ p0)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hinv hx0) _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hp hA0.le
    _ = (b 0 * a) ^ (-(1 / 2 : ℝ)) * (A0 * Real.log (b 0 * a) ^ p0) / 2 := by
        rw [pow_succ]; field_simp

/-- **`√N E ≤ δ₀/8`**: with `C = 32 √N K_w c_F (2d+2) K₁ d L`, the closeness term
`√N · K_w c_F (2d+2) K₁ (4 d L δ₀) e^{-x}` is at most `δ₀/8` as soon as `x ≥ log C`
(`x = γ_w c M₁`, a condition on the cube size independent of `δ₀`). -/
theorem exp_term_small {s Kw cf D k1 dd L' δ₀ x : ℝ} (hKw : 0 < Kw) (hcf : 0 < cf)
    (hD : 0 < D) (hk1 : 0 < k1) (hdd : 0 < dd) (hL' : 0 < L') (hδ : 0 < δ₀)
    (hs0 : 0 < s) (hx : Real.log (32 * s * Kw * cf * D * k1 * dd * L') ≤ x) :
    s * (Kw * (cf * (D * (k1 * (4 * dd * L' * δ₀)))) * Real.exp (-x)) ≤ δ₀ / 8 := by
  set C := 32 * s * Kw * cf * D * k1 * dd * L' with hC
  have hC0 : 0 < C := by positivity
  have h1 : Real.exp (-x) ≤ 1 / C := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ hC0 ?_
    calc C = Real.exp (Real.log C) := (Real.exp_log hC0).symm
      _ ≤ Real.exp x := Real.exp_le_exp.2 hx
  have : s * (Kw * (cf * (D * (k1 * (4 * dd * L' * δ₀)))) * Real.exp (-x)) =
      (C / 8) * δ₀ * Real.exp (-x) := by rw [hC]; ring
  rw [this]
  calc (C / 8) * δ₀ * Real.exp (-x) ≤ (C / 8) * δ₀ * (1 / C) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = δ₀ / 8 := by field_simp

/-- **`3 ρ/√β ≤ δ₀/4`** from `ρ ≤ √β δ₀/12`; with `δ₀ = (β a)^{-1/2} p₀` the hypothesis reads
`ρ ≤ a^{-1/2} p₀/12`, i.e. `N ‖W‖_row p₁ ≤ a^{-1/2} p₀/12`. -/
theorem tangent_small {ρ β δ₀ : ℝ} (hβ : 0 < β) (hρ : ρ ≤ Real.sqrt β * δ₀ / 12) :
    3 * (ρ / Real.sqrt β) ≤ δ₀ / 4 := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  rw [← mul_div_assoc, div_le_iff₀ hs]
  linarith

theorem sqrt_mul_delta {β a p : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    Real.sqrt β * ((β * a) ^ (-(1 / 2 : ℝ)) * p) = a ^ (-(1 / 2 : ℝ)) * p := by
  rw [Real.mul_rpow hβ.le ha.le, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hβ]
  norm_num

end Balaban.LargeField.Base
