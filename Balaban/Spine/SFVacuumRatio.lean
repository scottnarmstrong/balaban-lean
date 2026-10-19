/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One step of the coupling flow changes `β` by a bounded factor

The coefficient bounds (H.6) at `k + 1` give `β_{k+1} = β_k L^{d-2}/(1 + ξ₃^{(k)})` with
`|ξ₃^{(k)}| ≤ (c₈/4) q^{k+1} ≤ 1/4` (`Flow.betaSeq`, `CoeffBounds.flow`).  So
`β_{k+1} ≥ (4/5) β_k L^{d-2} ≥ (4/5) β_k` whenever `β_k > 0` (`CoeffBounds.beta_succ_ge`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban

/-- **The step of the coupling flow is a bounded factor** (P4 (5.28), (H.6)): under the coefficient
bounds at `k + 1`, if `β_k > 0` then `β_{k+1} > 0` and `(4/5) β_k L^{d-2} ≤ β_{k+1}`. -/
theorem CoeffBounds.beta_succ_ge {d L k : ℕ} {P : Consts} {β ν a : ℕ → ℝ}
    (h : CoeffBounds d L (k + 1) P β ν a) (hL : 1 ≤ L) (hk : 0 < β k) :
    0 < β (k + 1) ∧ 4 / 5 * (β k * (L : ℝ) ^ (d - 2)) ≤ β (k + 1) := by
  obtain ⟨ξ, β₀, ν₀, hξ, hc, hseq⟩ := h.flow
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hq : 0 < Flow.rate (L : ℝ) P.γ := Flow.rate_pos hL0 P.γ
  have hn : ‖ξ k 2‖ ≤ 1 / 4 := by
    have h1 := hξ k
    have hc8 : 0 ≤ P.c₈ := by
      have : 0 ≤ P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (k + 1) := (norm_nonneg _).trans h1
      have hp : 0 < Flow.rate (L : ℝ) P.γ ^ (k + 1) := pow_pos hq _
      by_contra hneg
      have hneg := not_le.1 hneg
      have : P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (k + 1) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hp
      linarith
    have hr1 : Flow.rate (L : ℝ) P.γ ≤ 1 := by nlinarith [mul_nonneg hc8 hq.le]
    have hpow : Flow.rate (L : ℝ) P.γ ^ (k + 1) ≤ Flow.rate (L : ℝ) P.γ := by
      rw [pow_succ]
      calc Flow.rate (L : ℝ) P.γ ^ k * Flow.rate (L : ℝ) P.γ ≤ 1 * Flow.rate (L : ℝ) P.γ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ hq.le hr1) hq.le
        _ = _ := one_mul _
    have h3 : ‖ξ k 2‖ ≤ ‖ξ k‖ := by
      simpa using norm_le_pi_norm (ξ k) 2
    have h4 : P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (k + 1) ≤ P.c₈ / 4 * Flow.rate (L : ℝ) P.γ :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    nlinarith
  have hw : ‖(1 + ξ k 2) - 1‖ ≤ 1 / 4 := by simpa using hn
  have hre : |(1 + ξ k 2).re - 1| ≤ 1 / 4 := by
    have := Complex.abs_re_le_norm ((1 + ξ k 2) - 1)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  have hre' : 3 / 4 ≤ (1 + ξ k 2).re ∧ (1 + ξ k 2).re ≤ 5 / 4 := by
    rw [abs_le] at hre; constructor <;> linarith [hre.1, hre.2]
  have hw0 : (1 + ξ k 2) ≠ 0 := by
    intro h0
    have : (1 + ξ k 2).re = 0 := by rw [h0]; simp
    linarith [hre'.1]
  have e1 := (hseq k (by omega)).1
  have e2 := (hseq (k + 1) le_rfl).1
  rw [Flow.betaSeq] at e2
  rw [← e1] at e2
  have e3 : ((β (k + 1) : ℝ) : ℂ) * (1 + ξ k 2) = ((β k * (L : ℝ) ^ (d - 2) : ℝ) : ℂ) := by
    rw [e2]; push_cast; field_simp
  have e4 := congrArg Complex.re e3
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at e4
  have hpos : 0 < β k * (L : ℝ) ^ (d - 2) := by positivity
  have hb : 0 < β (k + 1) := by
    by_contra hneg
    have hneg := not_lt.1 hneg
    nlinarith [mul_nonneg (neg_nonneg.2 hneg) (by linarith [hre'.1] : 0 ≤ (1 + ξ k 2).re)]
  refine ⟨hb, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hre'.2 hb.le]

end Balaban.SmallField.Def6
