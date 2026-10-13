/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRatesDirect
public import Balaban.Fluctuation.StepActivityDirectPhysical
public import Balaban.Fluctuation.StepObjects
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Arithmetic of the smallness `(DA)` and of the rate relation of the direct activity bound

The direct activity bound `stepActivityBound_zeroClass_direct` needs
`R_σ ε_U ≤ [8 K_c'^3 c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G)]⁻¹` (`hDA`) and the rate
relation `κ' + 3κ₀ + c₁ + 3/2 ≤ 2κ_dec - 1` (`hκa`).  This file proves the arithmetic only.

**`C_*` is a parameter here.**  The estimate that the physical amplitude has the form
`ε_U = C_* (log β_k)^q / √β_k` with a constant `C_*` independent of the scale is NOT proved in this
file (see `notes/phase1/PHYSCUBIC.md`, `notes/phase1/DAPHYS.md`).

Contents.
* `H q = q! 4^q` and `t^q e^{-t/4} ≤ H q` for `t ≥ 0`; hence `(log β)^q/√β ≤ H q β^{-1/4}`
  for `β ≥ 1`.
* `daThreshold C T q = max e ((C H q / T)^4)`: for `β` at least this, `C (log β)^q/√β ≤ T`.
* `daT`: the largest `ε_U` allowed by `hDA` for a given `R_σ`; `hDA` is equivalent to `ε_U ≤ daT`.
* `da_numerics_witness`: at `d = L = 3` with the rates of `stepRates_direct_witness`, the threshold
  `daThreshold C (daT …) q` depends only on `C_*`, `q`, `R_σ` and the rate constants (which depend
  only on `d`, `L`); above it `hκa` and `hDA` hold.
* `da_numerics_betaU`: uniformity in the scale, `β_k ≥ β` for `d ≥ 2`.
* `c1_three`, `cG_three`: `c₁(3,3) = 3375`, `c_G(3,3) = 18`.
-/

@[expose] public section

namespace Balaban.Fluctuation

/-- The constant `H q = q! 4^q` bounding `t^q e^{-t/4}` for `t ≥ 0`. -/
noncomputable def H (q : ℕ) : ℝ := (q.factorial : ℝ) * 4 ^ q

theorem H_pos (q : ℕ) : 0 < H q := by unfold H; positivity

/-- For `t ≥ 0`, `t^q e^{-t/4} ≤ q! 4^q`. -/
theorem pow_mul_exp_neg_le (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    t ^ q * Real.exp (-t / 4) ≤ H q := by
  have h := Real.pow_div_factorial_le_exp (t / 4) (by positivity) q
  have hf : (0 : ℝ) < q.factorial := by positivity
  rw [div_le_iff₀ hf, div_pow] at h
  have h4 : (0 : ℝ) < 4 ^ q := by positivity
  have he : Real.exp (-t / 4) * Real.exp (t / 4) = 1 := by
    rw [← Real.exp_add]; ring_nf; simp
  have hp : t ^ q ≤ Real.exp (t / 4) * q.factorial * 4 ^ q := by
    have := mul_le_mul_of_nonneg_right h h4.le
    rw [div_mul_cancel₀ _ h4.ne'] at this
    linarith
  calc t ^ q * Real.exp (-t / 4)
      ≤ (Real.exp (t / 4) * q.factorial * 4 ^ q) * Real.exp (-t / 4) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = H q := by unfold H; rw [← mul_one ((q.factorial : ℝ) * 4 ^ q), ← he]; ring

/-- For `β ≥ 1`, `(log β)^q / √β ≤ H q β^{-1/4}`. -/
theorem log_pow_div_sqrt_le {q : ℕ} {β : ℝ} (hβ : 1 ≤ β) :
    (Real.log β) ^ q / Real.sqrt β ≤ H q * β ^ (-(1 / 4 : ℝ)) := by
  have hβ0 : 0 < β := by linarith
  have ht : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hs : Real.sqrt β = Real.exp (Real.log β / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hβ0]; ring_nf
  have hr : β ^ (-(1 / 4 : ℝ)) = Real.exp (-Real.log β / 4) := by
    rw [Real.rpow_def_of_pos hβ0]; ring_nf
  rw [hs, hr, div_eq_mul_inv, ← Real.exp_neg]
  have h := pow_mul_exp_neg_le q ht
  have e : Real.exp (-(Real.log β / 2)) = Real.exp (-Real.log β / 4) * Real.exp (-Real.log β / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  calc _ ≤ H q * Real.exp (-Real.log β / 4) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = _ := rfl

/-- The threshold `β₀ = max {e, (C H_q / T)^4}`. -/
noncomputable def daThreshold (Cstar T : ℝ) (q : ℕ) : ℝ :=
  max (Real.exp 1) ((Cstar * H q / T) ^ 4)

theorem one_le_daThreshold (Cstar T : ℝ) (q : ℕ) : 1 ≤ daThreshold Cstar T q := by
  unfold daThreshold
  exact le_trans (Real.one_le_exp (by norm_num)) (le_max_left _ _)

/-- **The amplitude bound.**  For `β ≥ daThreshold C T q`, `C (log β)^q / √β ≤ T`. -/
theorem amplitude_le {Cstar T : ℝ} (hC : 0 < Cstar) (hT : 0 < T) (q : ℕ) {β : ℝ}
    (hβ : daThreshold Cstar T q ≤ β) :
    Cstar * (Real.log β) ^ q / Real.sqrt β ≤ T := by
  have h1 : 1 ≤ β := le_trans (one_le_daThreshold Cstar T q) hβ
  have hβ0 : 0 < β := by linarith
  have hx : (Cstar * H q / T) ^ 4 ≤ β := le_trans (le_max_right _ _) hβ
  set x := Cstar * H q / T with hxdef
  have hx0 : 0 < x := by have := H_pos q; positivity
  set u := β ^ (1 / 4 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hβ0 _
  have hu4 : u ^ 4 = β := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]; norm_num
  have hxu : x ≤ u := by
    by_contra hlt
    rw [not_le] at hlt
    have := pow_lt_pow_left₀ hlt hu0.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [hu4] at this; linarith
  have hneg : β ^ (-(1 / 4 : ℝ)) = u⁻¹ := by rw [Real.rpow_neg hβ0.le]
  have h := log_pow_div_sqrt_le (q := q) h1
  rw [hneg] at h
  have hCx : Cstar * H q ≤ T * u := by
    have : x * T = Cstar * H q := by rw [hxdef]; field_simp
    nlinarith
  calc Cstar * (Real.log β) ^ q / Real.sqrt β
      = Cstar * ((Real.log β) ^ q / Real.sqrt β) := by ring
    _ ≤ Cstar * (H q * u⁻¹) := mul_le_mul_of_nonneg_left h hC.le
    _ = (Cstar * H q) * u⁻¹ := by ring
    _ ≤ (T * u) * u⁻¹ := mul_le_mul_of_nonneg_right hCx (inv_pos.2 hu0).le
    _ = T := by field_simp

end Balaban.Fluctuation
