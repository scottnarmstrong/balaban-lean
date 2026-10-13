/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.EarlyMassRatio
public import Balaban.Inhabited.Numerics

/-!
# Non-vacuity of `EarlyMassRatio`

For every `d ≥ 2`, `L ≥ 2` there are couplings `β, ν` with the exact running coefficients
(`ε = 0`, `a = 5/4`), `β ν L^d = 1` (so `k₀ ≥ 1` is genuine), `A₀ = 1`, `p₀ = 1`, and
`λ_1 ≥ 2`, so that the largeness condition `2 a E < A₀² λ_1^{2p₀}` (`5/2 < 4`) holds at the
scale `k = 1 ≤ k₀`; hence `2 ν_1 < δ_1²`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField

/-- All hypotheses of `two_nu_lt_delta_sq` hold at the scale `k = 1 ≤ k₀`. -/
theorem earlyMassRatio_hyps_nonempty {d L : ℕ} (hd : 2 ≤ d) (hL : 2 ≤ L) :
    ∃ (β ν : ℝ) (b nr : ℕ → ℝ), RunningHyp d L β ν (5 / 4) 0 b nr ∧ KZeroGenuine β ν ∧
      1 ≤ kZero d L β ν ∧
      2 * (5 / 4 : ℝ) * Real.exp (2 * 0) < (1 : ℝ) ^ 2 * runLam (5 / 4) b 1 ^ (2 * 1) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  set β : ℝ := 4 / 5 * Real.exp 2 with hβdef
  have hβ : 0 < β := by positivity
  set ν : ℝ := 1 / (β * (L : ℝ) ^ d) with hνdef
  have hν : 0 < ν := by positivity
  obtain ⟨b, nr, h⟩ := runningHyp_nonempty (d := d) (L := L) hd hL hβ hν
  have hβν : β * ν = 1 / (L : ℝ) ^ d := by
    rw [hνdef]; field_simp
  have hg : KZeroGenuine β ν := by
    unfold KZeroGenuine
    rw [hβν, div_le_one (by positivity)]
    exact one_le_pow₀ hL1
  have hk : 1 ≤ kZero d L β ν := by
    unfold kZero
    refine le_csSup (kZero_bddAbove (by omega) hL (mul_pos hβ hν)) ?_
    show β * ν * (L : ℝ) ^ (1 * d) ≤ 1
    rw [hβν, one_mul]
    have : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    rw [one_div, inv_mul_cancel₀ this.ne']
  refine ⟨β, ν, b, nr, h, hg, hk, ?_⟩
  have hb1 : b 1 = β * (L : ℝ) ^ (1 * (d - 2)) := by
    obtain ⟨γ, hγ, hlog, he⟩ := h.beta_eq 1
    have h0 : Real.log γ = 0 := abs_nonpos_iff.1 hlog
    have : γ = 1 := by
      rcases Real.log_eq_zero.1 h0 with h1 | h1 | h1
      · linarith
      · exact h1
      · linarith
    rw [he, this, mul_one]
  have hge : β ≤ b 1 := by
    rw [hb1, one_mul]
    exact le_mul_of_one_le_right hβ.le (one_le_pow₀ hL1)
  have hlam : 2 ≤ runLam (5 / 4) b 1 := by
    unfold runLam
    have e : Real.exp 2 = β * (5 / 4) := by rw [hβdef]; ring
    calc (2 : ℝ) = Real.log (β * (5 / 4)) := by rw [← e, Real.log_exp]
      _ ≤ _ := Real.log_le_log (by positivity) (by nlinarith)
  have : (4 : ℝ) ≤ runLam (5 / 4) b 1 ^ 2 := by nlinarith
  simp only [mul_zero, Real.exp_zero, one_pow, one_mul, mul_one]
  norm_num
  linarith

end Balaban.Inhabited
