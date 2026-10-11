/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.C1Star
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The running coefficients for real `ξ`

For real `ξ` with `‖ξ_k‖ ≤ (c₈/4) q^{k+1}` and `c₈ q / (1 - q) ≤ 1/2`, the sequences
`gammaR, deltaR, betaR` are real, positive, `γ_j, δ_j ∈ [1/2, 2]`, `β_j = β L^{j(d-2)} γ_j`, and
they depend continuously on `ξ` (finitely many factors).
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

section Seq

variable {L d : ℕ} {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ}

theorem norm_xiC (k : ℕ) : ‖xiC ξ k‖ = ‖ξ k‖ := by
  simp [xiC, Pi.norm_def, Complex.nnnorm_real]

theorem abs_le_norm_pi (x : Fin 3 → ℝ) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have := norm_le_pi_norm x i
  simpa using this

theorem gammaSeq_xiC (j : ℕ) :
    gammaSeq (xiC ξ) j = ((∏ i ∈ range j, (1 + ξ i 2)⁻¹ : ℝ) : ℂ) := by
  simp [gammaSeq, xiC]

theorem deltaSeq_xiC (j : ℕ) :
    deltaSeq (xiC ξ) j = ((∏ i ∈ range j, ((1 + ξ i 2) / (1 + ξ i 1)) : ℝ) : ℂ) := by
  simp [deltaSeq, xiC]

theorem gammaR_eq (j : ℕ) : gammaR ξ j = ∏ i ∈ range j, (1 + ξ i 2)⁻¹ := by
  rw [gammaR, gammaSeq_xiC, Complex.ofReal_re]

theorem deltaR_eq (j : ℕ) : deltaR ξ j = ∏ i ∈ range j, ((1 + ξ i 2) / (1 + ξ i 1)) := by
  rw [deltaR, deltaSeq_xiC, Complex.ofReal_re]

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h := Real.log_two_gt_d9
  calc Real.exp (1 / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith)
    _ = 2 := Real.exp_log (by norm_num)

theorem betaR_eq (β : ℝ) (j : ℕ) :
    betaR L d ξ β j = β * (L : ℝ) ^ (j * (d - 2)) * gammaR ξ j := by
  have := betaSeq_eq (L : ℝ) d (xiC ξ) (β : ℂ) j
  rw [betaR, this, gammaSeq_xiC, ← gammaR_eq]
  norm_cast

/-- The standing smallness hypotheses on the running coefficients. -/
structure SeqHyp (L : ℕ) (γ₀ c₈ : ℝ) (ξ : ℕ → Fin 3 → ℝ) : Prop where
  hL : 2 ≤ L
  hγ : 0 < γ₀
  hc : 0 ≤ c₈
  small : c₈ * rate (L : ℝ) γ₀ / (1 - rate (L : ℝ) γ₀) ≤ 1 / 2
  bound : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * rate (L : ℝ) γ₀ ^ (k + 1)

namespace SeqHyp

variable (H : SeqHyp L γ₀ c₈ ξ)
include H

theorem hL1 : (1 : ℝ) < L := by exact_mod_cast H.hL

theorem hq0 : 0 ≤ rate (L : ℝ) γ₀ := (rate_pos (by linarith [H.hL1]) _).le

theorem hq1 : rate (L : ℝ) γ₀ < 1 := rate_lt_one H.hL1 H.hγ

theorem hs : c₈ * rate (L : ℝ) γ₀ ≤ 1 - rate (L : ℝ) γ₀ := by
  have h1 : 0 < 1 - rate (L : ℝ) γ₀ := by linarith [H.hq1]
  have := H.small
  rw [div_le_iff₀ h1] at this
  nlinarith

theorem bound_xiC : ∀ k, ‖xiC ξ k‖ ≤ c₈ / 4 * rate (L : ℝ) γ₀ ^ (k + 1) := fun k => by
  rw [norm_xiC]; exact H.bound k

theorem abs_xi_le (k : ℕ) (i : Fin 3) : |ξ k i| ≤ 1 / 4 := by
  have := norm_le_quarter H.hq0 H.hq1 H.hc H.hs H.bound_xiC k
  rw [norm_xiC] at this
  exact (abs_le_norm_pi _ _).trans this

theorem one_add_pos (k : ℕ) (i : Fin 3) : 0 < 1 + ξ k i := by
  have := abs_le.1 (H.abs_xi_le k i)
  linarith [this.1]

theorem exp_le_two : Real.exp (c₈ * (rate (L : ℝ) γ₀ / (1 - rate (L : ℝ) γ₀))) ≤ 2 := by
  refine le_trans (Real.exp_le_exp.2 ?_) exp_half_le_two
  have := H.small
  rwa [← mul_div_assoc]

theorem gammaR_pos (j : ℕ) : 0 < gammaR ξ j := by
  rw [gammaR_eq]
  exact Finset.prod_pos fun i _ => inv_pos.2 (H.one_add_pos i 2)

theorem deltaR_pos (j : ℕ) : 0 < deltaR ξ j := by
  rw [deltaR_eq]
  exact Finset.prod_pos fun i _ => div_pos (H.one_add_pos i 2) (H.one_add_pos i 1)

theorem gammaR_bounds (j : ℕ) : 1 / 2 ≤ gammaR ξ j ∧ gammaR ξ j ≤ 2 := by
  obtain ⟨h1, h2, -, -⟩ := norm_gammaSeq_le H.hq0 H.hq1 H.hc H.hs H.bound_xiC j
  have hB : Real.exp (c₈ * ratePartialSum (rate (L : ℝ) γ₀) j) ≤ 2 := by
    refine le_trans (Real.exp_le_exp.2 ?_) H.exp_le_two
    exact mul_le_mul_of_nonneg_left (ratePartialSum_le H.hq0 H.hq1 j) H.hc
  have hp := H.gammaR_pos j
  have e : gammaSeq (xiC ξ) j = (gammaR ξ j : ℂ) := by
    rw [gammaSeq_xiC, gammaR_eq]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at h1
  rw [e, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at h2
  refine ⟨?_, h1.trans hB⟩
  have := h2.trans hB
  rw [inv_le_comm₀ hp (by norm_num)] at this
  linarith

theorem deltaR_bounds (j : ℕ) : 1 / 2 ≤ deltaR ξ j ∧ deltaR ξ j ≤ 2 := by
  obtain ⟨-, -, h1, h2⟩ := norm_gammaSeq_le H.hq0 H.hq1 H.hc H.hs H.bound_xiC j
  have hB : Real.exp (c₈ * ratePartialSum (rate (L : ℝ) γ₀) j) ≤ 2 := by
    refine le_trans (Real.exp_le_exp.2 ?_) H.exp_le_two
    exact mul_le_mul_of_nonneg_left (ratePartialSum_le H.hq0 H.hq1 j) H.hc
  have hp := H.deltaR_pos j
  have e : deltaSeq (xiC ξ) j = (deltaR ξ j : ℂ) := by
    rw [deltaSeq_xiC, deltaR_eq]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at h1
  rw [e, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp] at h2
  refine ⟨?_, h1.trans hB⟩
  have := h2.trans hB
  rw [inv_le_comm₀ hp (by norm_num)] at this
  linarith

theorem betaR_ge {β : ℝ} (hβ : 0 < β) (j : ℕ) : β / 2 ≤ betaR L d ξ β j := by
  rw [betaR_eq]
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (j * (d - 2)) := one_le_pow₀ H.hL1.le
  have h2 := (H.gammaR_bounds j).1
  have : β / 2 ≤ β * 1 * (1 / 2) := by linarith
  refine this.trans ?_
  have hL0 : 0 ≤ (L : ℝ) ^ (j * (d - 2)) := by positivity
  calc β * 1 * (1 / 2) ≤ β * (L : ℝ) ^ (j * (d - 2)) * (1 / 2) := by gcongr
    _ ≤ β * (L : ℝ) ^ (j * (d - 2)) * gammaR ξ j := by gcongr

theorem betaR_pos {β : ℝ} (hβ : 0 < β) (j : ℕ) : 0 < betaR L d ξ β j :=
  lt_of_lt_of_le (by positivity) (H.betaR_ge hβ j)

end SeqHyp

end Seq

section Continuity

variable {L : ℕ} {γ₀ c₈ : ℝ} {ξ : ℝ → ℕ → Fin 3 → ℝ}

theorem tendsto_gammaR (hc : ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k)))
    (H0 : SeqHyp L γ₀ c₈ (ξ 0)) (j : ℕ) :
    Tendsto (fun ν => gammaR (ξ ν) j) (𝓝[>] 0) (𝓝 (gammaR (ξ 0) j)) := by
  simp only [gammaR_eq]
  refine tendsto_finsetProd _ fun i _ => ?_
  have h2 : Tendsto (fun ν => ξ ν i 2) (𝓝[>] 0) (𝓝 (ξ 0 i 2)) :=
    (continuous_apply 2).continuousAt.tendsto.comp (hc i)
  exact (tendsto_const_nhds.add h2).inv₀ (H0.one_add_pos i 2).ne'

theorem tendsto_deltaR (hc : ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k)))
    (H0 : SeqHyp L γ₀ c₈ (ξ 0)) (j : ℕ) :
    Tendsto (fun ν => deltaR (ξ ν) j) (𝓝[>] 0) (𝓝 (deltaR (ξ 0) j)) := by
  simp only [deltaR_eq]
  refine tendsto_finsetProd _ fun i _ => ?_
  have h2 : Tendsto (fun ν => ξ ν i 2) (𝓝[>] 0) (𝓝 (ξ 0 i 2)) :=
    (continuous_apply 2).continuousAt.tendsto.comp (hc i)
  have h1 : Tendsto (fun ν => ξ ν i 1) (𝓝[>] 0) (𝓝 (ξ 0 i 1)) :=
    (continuous_apply 1).continuousAt.tendsto.comp (hc i)
  exact (tendsto_const_nhds.add h2).div (tendsto_const_nhds.add h1) (H0.one_add_pos i 1).ne'

theorem tendsto_betaR {d : ℕ} (hc : ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k)))
    (H0 : SeqHyp L γ₀ c₈ (ξ 0)) (β : ℝ) (j : ℕ) :
    Tendsto (fun ν => betaR L d (ξ ν) β j) (𝓝[>] 0) (𝓝 (betaR L d (ξ 0) β j)) := by
  simp only [betaR_eq]
  exact tendsto_const_nhds.mul (tendsto_gammaR hc H0 j)

end Continuity

end Balaban.Correlations
