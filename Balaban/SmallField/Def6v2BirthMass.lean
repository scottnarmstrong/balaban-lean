/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Birth

/-!
# The birth mass against the ideal mass of the current scale

Along the renormalized flow the fine mass `ν_j L^{-2j}` of a level born at scale `j` and the ideal
mass `ν_k L^{-2k}` of the current scale differ by the product of the factors
`(1 + ξ₃)/(1 + ξ₂)` of the steps `j, …, k - 1`.  The flow bounds of `CoeffBounds` control this
product from both sides by a constant.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.SmallField Balaban.SmallField.Def6

variable {d L k : ℕ}


/-- **The birth mass exceeds the ideal mass by at most the factor `e²`.**  Along a flow
`ν_{n+1} = ν_n L² (1 + ξ₃)/(1 + ξ₂)` with `‖ξ_n‖ ≤ (c₈/4) q^{n+1}` and `c₈ q ≤ 1 - q`
(`CoeffBounds.flow`), for `j ≤ k`
`ν_j L^{-2j} · L^{2j} = ν_j ≤ e² · ν_k L^{-2(k-j)}`.  The exact comparison `ν_j ≤ ν_k L^{-2(k-j)}`
(the hypothesis `hm` of `polyAniso_subset_birthXiDom_of_mass`) is equivalent to
`∏_{n=j}^{k-1} (1 + ξ₃^{(n)})/(1 + ξ₂^{(n)}) ≥ 1` and is not implied by the flow bounds; this
lemma gives the uniform allowance `Λ = e²` instead (P4 (H.6), (5.32)). -/
theorem physMass_mul_sq_le_exp_nuIdeal_core [NeZero L] {P : Consts} (hγ : 0 < P.γ)
    (hc8 : 0 < P.c₈) (hL : 2 ≤ L)
    {β ν a : ℕ → ℝ} (h : CoeffBounds d L k P β ν a) {j : ℕ} (hjk : j ≤ k) :
    physMass L j (ν j) * ((L : ℝ) ^ j) ^ 2 ≤ Real.exp 2 * nuIdeal L k (ν k) j := by
  obtain ⟨ξ, β₀, ν₀, hξ, hs, hseq⟩ := h.flow
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  set q := Flow.rate (L : ℝ) P.γ with hq
  have hq0 : 0 ≤ q := (Flow.rate_pos hLpos _).le
  have hq1 : q < 1 := Flow.rate_lt_one hL1 hγ
  have hb := fun n => Flow.norm_gammaSeq_le hq0 hq1 hc8.le hs hξ n
  have hS : ∀ n, P.c₈ * Flow.ratePartialSum q n ≤ 1 := by
    intro n
    have h1 := Flow.ratePartialSum_le hq0 hq1 n
    have h2 : P.c₈ * (q / (1 - q)) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one (by linarith)]; exact hs
    exact (mul_le_mul_of_nonneg_left h1 hc8.le).trans h2
  have hδj : ‖Flow.deltaSeq ξ j‖ ≤ Real.exp 1 :=
    (hb j).2.2.1.trans (Real.exp_le_exp.2 (hS j))
  have hδk : ‖(Flow.deltaSeq ξ k)⁻¹‖ ≤ Real.exp 1 :=
    (hb k).2.2.2.trans (Real.exp_le_exp.2 (hS k))
  have hνj := hseq j hjk
  have hνk := hseq k le_rfl
  rw [Flow.nuSeq_eq] at hνj hνk
  have hνkpos : 0 < ν k := h.nu_pos
  have key : ((ν j : ℝ) : ℂ) * ((L : ℝ) : ℂ) ^ (2 * k) * Flow.deltaSeq ξ k =
      ((ν k : ℝ) : ℂ) * ((L : ℝ) : ℂ) ^ (2 * j) * Flow.deltaSeq ξ j := by
    rw [hνj.2, hνk.2]; ring
  have hδk0 : Flow.deltaSeq ξ k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hνk
    exact hνkpos.ne' (by exact_mod_cast hνk.2)
  have hnorm := congrArg norm key
  simp only [norm_mul, Complex.norm_real, norm_pow, Real.norm_eq_abs,
    abs_of_pos hνkpos, abs_of_pos hLpos] at hnorm
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := pow_pos hLpos j
  have hLt : (0 : ℝ) < (L : ℝ) ^ t := pow_pos hLpos t
  have hδkn : 0 < ‖Flow.deltaSeq ξ (j + t)‖ := norm_pos_iff.2 hδk0
  have hinv : ‖(Flow.deltaSeq ξ (j + t))⁻¹‖ = (‖Flow.deltaSeq ξ (j + t)‖)⁻¹ := norm_inv _
  rw [hinv] at hδk
  unfold physMass nuIdeal
  rw [show j + t - j = t by omega]
  have h3 : ((L : ℝ) ^ j) ^ 2 * (|ν j| * ((L : ℝ) ^ t) ^ 2 * ‖Flow.deltaSeq ξ (j + t)‖) =
      ((L : ℝ) ^ j) ^ 2 * (ν (j + t) * ‖Flow.deltaSeq ξ j‖) := by
    linear_combination hnorm
  have h4 := mul_left_cancel₀ (pow_pos hLj 2).ne' h3
  have hLt2 : (0 : ℝ) < ((L : ℝ) ^ t) ^ 2 := by positivity
  have h5 : |ν j| * ((L : ℝ) ^ t) ^ 2 ≤ Real.exp 2 * ν (j + t) := by
    have h6 : |ν j| * ((L : ℝ) ^ t) ^ 2 = ν (j + t) * ‖Flow.deltaSeq ξ j‖ *
        (‖Flow.deltaSeq ξ (j + t)‖)⁻¹ := by
      field_simp
      linarith [h4]
    rw [h6, show Real.exp 2 = Real.exp 1 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
    have := mul_le_mul hδj hδk (by positivity) (Real.exp_pos 1).le
    calc ν (j + t) * ‖Flow.deltaSeq ξ j‖ * (‖Flow.deltaSeq ξ (j + t)‖)⁻¹
        = ν (j + t) * (‖Flow.deltaSeq ξ j‖ * (‖Flow.deltaSeq ξ (j + t)‖)⁻¹) := by ring
      _ ≤ ν (j + t) * (Real.exp 1 * Real.exp 1) :=
          mul_le_mul_of_nonneg_left this hνkpos.le
      _ = Real.exp 1 * Real.exp 1 * ν (j + t) := by ring
  have h7 : ν j * ((L : ℝ) ^ t) ^ 2 ≤ Real.exp 2 * ν (j + t) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hLt2.le).trans h5
  have hinvt : (((L : ℝ) ^ t)⁻¹) ^ 2 = (((L : ℝ) ^ t) ^ 2)⁻¹ := by rw [inv_pow]
  rw [hinvt]
  have hLj2 : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by positivity
  have e3 : ν j * (((L : ℝ) ^ j)⁻¹) ^ 2 * ((L : ℝ) ^ j) ^ 2 = ν j := by
    rw [inv_pow]; field_simp
  rw [e3, ← div_eq_mul_inv, ← mul_div_assoc, le_div_iff₀ hLt2]
  exact h7

theorem physMass_mul_sq_le_exp_nuIdeal [NeZero L] {P : Consts} (hP : P.Admissible d L) (hL : 2 ≤ L)
    {β ν a : ℕ → ℝ} (h : CoeffBounds d L k P β ν a) {j : ℕ} (hjk : j ≤ k) :
    physMass L j (ν j) * ((L : ℝ) ^ j) ^ 2 ≤ Real.exp 2 * nuIdeal L k (ν k) j :=
  physMass_mul_sq_le_exp_nuIdeal_core hP.γ_pos hP.c₈_pos hL h hjk

end Balaban.SmallField.Def6v2
