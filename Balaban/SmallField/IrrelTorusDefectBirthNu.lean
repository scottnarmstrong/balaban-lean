/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2BirthMass

/-!
# Birth masses of the running flow: positivity and the free-flow coefficients

For the running coefficients of `CoeffBounds` the mass `ν_j` of every level `j ≤ k` is positive
(the steps `ν_n ↦ ν_{n+1} = ν_n L² (1 + ξ₃)/(1 + ξ₂)` have `‖ξ‖ ≤ 1/4`, so the ratio has positive
real part).  The free-flow coefficients through a prescribed positive mass `ν'_k ≤ ν̄` satisfy
`CoeffBounds`.  Both facts are used to restate the filed torus defect bound on the birth-mass
domains (author ruling R6).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField Balaban.SmallField.Def6

variable {d L k : ℕ} [NeZero L]

omit [NeZero L] in
/-- Each flow step has `‖ξ^{(n)}‖ ≤ 1/4`. -/
theorem flow_norm_le_quarter {P : Consts} (hP : P.Admissible d L) (hL : 2 ≤ L)
    {ξ : ℕ → Fin 3 → ℂ} (hξ : ∀ n, ‖ξ n‖ ≤ P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (n + 1))
    (hs : P.c₈ * Flow.rate (L : ℝ) P.γ ≤ 1 - Flow.rate (L : ℝ) P.γ) (n : ℕ) :
    ‖ξ n‖ ≤ 1 / 4 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hq0 : 0 ≤ Flow.rate (L : ℝ) P.γ := (Flow.rate_pos hLpos _).le
  have hq1 : Flow.rate (L : ℝ) P.γ < 1 := Flow.rate_lt_one hL1 hP.γ_pos
  have hqn : Flow.rate (L : ℝ) P.γ ^ n ≤ 1 := pow_le_one₀ hq0 hq1.le
  have hqn0 : 0 ≤ Flow.rate (L : ℝ) P.γ ^ n := pow_nonneg hq0 n
  refine (hξ n).trans ?_
  have h1 : P.c₈ * Flow.rate (L : ℝ) P.γ ^ (n + 1) =
      (P.c₈ * Flow.rate (L : ℝ) P.γ) * Flow.rate (L : ℝ) P.γ ^ n := by ring
  have h2 : (P.c₈ * Flow.rate (L : ℝ) P.γ) * Flow.rate (L : ℝ) P.γ ^ n ≤ 1 := by
    calc (P.c₈ * Flow.rate (L : ℝ) P.γ) * Flow.rate (L : ℝ) P.γ ^ n
        ≤ (1 - Flow.rate (L : ℝ) P.γ) * Flow.rate (L : ℝ) P.γ ^ n :=
          mul_le_mul_of_nonneg_right hs hqn0
      _ ≤ 1 * 1 := mul_le_mul (by linarith) hqn hqn0 (by norm_num)
      _ = 1 := one_mul 1
  calc P.c₈ / 4 * Flow.rate (L : ℝ) P.γ ^ (n + 1)
      = (P.c₈ * Flow.rate (L : ℝ) P.γ ^ (n + 1)) / 4 := by ring
    _ ≤ 1 / 4 := by rw [h1]; linarith

omit [NeZero L] in
/-- **The mass of every level of the running flow is positive**: `ν_j > 0` for `j ≤ k`, given
`ν_k > 0`. -/
theorem CoeffBounds.nu_pos_of_le {P : Consts} (hP : P.Admissible d L) (hL : 2 ≤ L)
    {β ν a : ℕ → ℝ} (h : CoeffBounds d L k P β ν a) {j : ℕ} (hjk : j ≤ k) : 0 < ν j := by
  obtain ⟨ξ, β₀, ν₀, hξ, hs, hseq⟩ := h.flow
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have key : ∀ t : ℕ, t ≤ k → 0 < ν (k - t) := by
    intro t
    induction t with
    | zero => intro _; simpa using h.nu_pos
    | succ t ih =>
      intro ht
      have hpos := ih (by omega)
      set n := k - (t + 1) with hn
      have hn1 : n + 1 = k - t := by omega
      have h0 := hseq n (by omega)
      have h1 := hseq (n + 1) (by omega)
      have ha : ‖ξ n 1‖ ≤ 1 / 4 :=
        (norm_le_pi_norm (ξ n) 1).trans (flow_norm_le_quarter hP hL hξ hs n)
      have hb : ‖ξ n 2‖ ≤ 1 / 4 :=
        (norm_le_pi_norm (ξ n) 2).trans (flow_norm_le_quarter hP hL hξ hs n)
      have ha1 : (1 + ξ n 1) ≠ 0 := by
        intro h0
        have : ξ n 1 = -1 := by linear_combination h0
        rw [this] at ha; norm_num at ha
      have hre_a : 3 / 4 ≤ (1 + ξ n 1).re := by
        have := Complex.abs_re_le_norm (ξ n 1)
        have h2 := (abs_le.1 (this.trans ha)).1
        simp only [Complex.add_re, Complex.one_re]; linarith
      have hre_b : 3 / 4 ≤ (1 + ξ n 2).re := by
        have := Complex.abs_re_le_norm (ξ n 2)
        have h2 := (abs_le.1 (this.trans hb)).1
        simp only [Complex.add_re, Complex.one_re]; linarith
      have hstep : (ν (k - t) : ℂ) * (1 + ξ n 1) = (ν n : ℂ) * (L : ℂ) ^ 2 * (1 + ξ n 2) := by
        rw [← hn1, h1.2, h0.2, Flow.nuSeq]
        field_simp
        push_cast
        ring
      have hstep' : ((ν (k - t) : ℝ) : ℂ) * (1 + ξ n 1) =
          (((ν n) * (L : ℝ) ^ 2 : ℝ) : ℂ) * (1 + ξ n 2) := by
        push_cast; exact hstep
      have hre := congrArg Complex.re hstep'
      rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
      have hL2 : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
      by_contra hneg
      push Not at hneg
      have : (ν n) * (L : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hL2.le
      nlinarith
  have := key (k - j) (by omega)
  rwa [show k - (k - j) = j by omega] at this

/-- **The coefficient bounds (H.6) hold for the free flow through any positive mass `νk ≤ ν̄`**
(`ξ = 0`), given them for some running coefficients with the same `a_k`. -/
theorem coeffBounds_complete_of {P : Consts} {β ν a : ℕ → ℝ}
    (hP : P.Admissible d L) (hC : CoeffBounds d L k P β ν a) {νk : ℝ} (hνpos : 0 < νk)
    (hνle : νk ≤ P.νbar) :
    CoeffBounds d L k P (betaComplete d L P νk) (nuComplete L k νk) a where
  flow := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    obtain ⟨-, -, -, -, hs, -⟩ := hC.flow
    refine ⟨0, |P.B| + 1 + νk⁻¹, νk * ((L : ℝ) ^ k)⁻¹ ^ 2, fun n => ?_, hs,
      fun n _ => ⟨?_, ?_⟩⟩
    · have h1 := Flow.rate_pos hL P.γ
      have h2 := hP.c₈_pos
      rw [Pi.zero_apply, norm_zero]
      positivity
    · rw [Flow.betaSeq_eq]
      simp [Flow.gammaSeq, betaComplete]
    · rw [Flow.nuSeq_eq]
      simp [Flow.deltaSeq, nuComplete]
  beta_gt := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have h1 : 0 < (L : ℝ) ^ (k * (d - 2)) := by positivity
    have h2 : P.B ≤ |P.B| := le_abs_self _
    have h3 : 0 < νk⁻¹ := inv_pos.2 hνpos
    unfold betaComplete
    exact mul_lt_mul_of_pos_right (by linarith) h1
  nu_pos := by rw [nuComplete_self]; exact hνpos
  nu_le := by rw [nuComplete_self]; exact hνle
  a_ge := hC.a_ge
  a_lt := hC.a_lt

end Balaban.SmallField.Def6v2
