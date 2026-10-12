/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31WitnessData
public import Balaban.Fluctuation.StepActivityWitnessMain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform bounds for the analytic background field near the background

The background-field component `svec φ_k(ψ^{(k)} + w)(y)_i` has an analytic extension in the
complex displacement `w` (`exists_analytic_ext`).  Near `w = 0` the extension of the potential and
of the components of the field are analytic, and, for a small fluctuation radius `p`, the complex
ray `u ψ'(ψ̂)`, `|u| < 2`, `‖ψ̂‖ ≤ p`, stays in the ball of analyticity (`exists_tube_obs`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology

section Svec

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The component `svec φ y i` of an analytic family of fields is analytic. -/
theorem analyticAt_svecFam {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {x : X}
    {φ : X → G.Ω 1 × Fin N → ℂ} (hφ : ∀ r, AnalyticAt ℂ (fun v => φ v r) x)
    (y : Torus d (N₀ * L ^ K)) (i : Fin N) : AnalyticAt ℂ (fun v => svec G (φ v) y i) x := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · simp only [svec_of_mem G _ ⟨y, hy⟩ i]
    exact hφ (⟨y, hy⟩, i)
  · simp only [svec_of_not_mem G _ hy i]
    exact analyticAt_const

theorem norm_svec_sub_le (φ ψ : G.Ω 1 × Fin N → ℂ) (y : Torus d (N₀ * L ^ K)) (i : Fin N) :
    ‖svec G φ y i - svec G ψ y i‖ ≤ ‖φ - ψ‖ := by
  classical
  by_cases hy : y ∈ G.Ω 1
  · rw [svec_of_mem G _ ⟨y, hy⟩ i, svec_of_mem G _ ⟨y, hy⟩ i]
    exact norm_le_pi_norm (φ - ψ) (⟨y, hy⟩, i)
  · rw [svec_of_not_mem G _ hy i, svec_of_not_mem G _ hy i, sub_self, norm_zero]
    exact norm_nonneg _

end Svec

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}

theorem exists_tube_obs (R : S.RayData pp) {T : ℝ} (hT : 0 < T) :
    ∃ (P : S.EC → ℂ) (B : S.EC → (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) (r p : ℝ),
      0 < r ∧ 0 < p ∧ p < pp ∧
      (∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w) ∧
      (∀ w, S.InDom w → bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (S.dataUC (S.psi0C + w)) = B w) ∧
      (∀ v : S.EC, ‖v‖ ≤ r → AnalyticAt ℂ P v ∧ ∀ q, AnalyticAt ℂ (fun w => B w q) v) ∧
      (∀ v : S.EC, ‖v‖ ≤ r → ‖(S.β : ℂ) * P v‖ ≤ T ∧
        ∀ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N),
          ‖svec (stepG d L N₁ m₁ k ϱ) (B v) y i - svec (stepG d L N₁ m₁ k ϱ) (B 0) y i‖ ≤ 1) ∧
      (∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ p → ‖u • S.shiftUC x‖ ≤ r) := by
  obtain ⟨hD1, hD2⟩ := S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R
  obtain ⟨P, B, hPB1, hPB2⟩ := S.exists_analytic_ext R.ha₁ R.H hD2
  have h0 : S.InDom 0 := by
    have := R.inDom_yhat (y := 0) (by
      have : S.unshiftU 0 = 0 := by simp [unshiftU]
      rw [this, norm_zero]; exact R.hpp)
    have e : yhat (0 : S.E) = (0 : S.EC) := by funext q; simp [yhat]
    rwa [e] at this
  have hP0 : P 0 = 0 := by
    rw [← (hPB2 0 h0).1, add_zero]
    exact S.VkC_psi0C R.ha₁ R.H (hD2.mono (thm73C2_le_thm73C1 d L N))
  have hβ := R.hβ
  obtain ⟨hPan, hBan⟩ := hPB1 0 h0
  obtain ⟨ε1, hε1, hball1⟩ := Metric.eventually_nhds_iff.1 hPan.eventually_analyticAt
  have hBev : ∀ᶠ w in 𝓝 (0 : S.EC), ∀ q, AnalyticAt ℂ (fun w => B w q) w := by
    rw [Filter.eventually_all]
    intro q
    exact (hBan q).eventually_analyticAt
  obtain ⟨ε2, hε2, hball2⟩ := Metric.eventually_nhds_iff.1 hBev
  have hcP := hPan.continuousAt
  obtain ⟨ε3, hε3, hsmallP⟩ := Metric.continuousAt_iff.1 hcP (T / (S.β + 1)) (by positivity)
  have hcB : ContinuousAt B 0 := continuousAt_pi.2 fun q => (hBan q).continuousAt
  obtain ⟨ε4, hε4, hsmallB⟩ := Metric.continuousAt_iff.1 hcB 1 one_pos
  set r := min (min ε1 ε2) (min ε3 ε4) / 2 with hr
  have hrpos : 0 < r := by positivity
  have hr1 : r < ε1 := by
    have : min (min ε1 ε2) (min ε3 ε4) ≤ ε1 := (min_le_left _ _).trans (min_le_left _ _)
    have h' : 0 < min (min ε1 ε2) (min ε3 ε4) := by positivity
    rw [hr]; linarith
  have hr2 : r < ε2 := by
    have : min (min ε1 ε2) (min ε3 ε4) ≤ ε2 := (min_le_left _ _).trans (min_le_right _ _)
    have h' : 0 < min (min ε1 ε2) (min ε3 ε4) := by positivity
    rw [hr]; linarith
  have hr3 : r < ε3 := by
    have : min (min ε1 ε2) (min ε3 ε4) ≤ ε3 := (min_le_right _ _).trans (min_le_left _ _)
    have h' : 0 < min (min ε1 ε2) (min ε3 ε4) := by positivity
    rw [hr]; linarith
  have hr4 : r < ε4 := by
    have : min (min ε1 ε2) (min ε3 ε4) ≤ ε4 := (min_le_right _ _).trans (min_le_right _ _)
    have h' : 0 < min (min ε1 ε2) (min ε3 ε4) := by positivity
    rw [hr]; linarith
  set Cs := ‖S.shiftL‖ with hCs
  have hCs0 : 0 ≤ Cs := norm_nonneg _
  have hCs1 : 0 < 2 * (Cs + 1) := by linarith
  refine ⟨P, B, r, min (pp / 2) (r / (2 * (Cs + 1))), hrpos,
    lt_min (by linarith [R.hpp]) (div_pos hrpos hCs1), ?_, fun w hw => (hPB2 w hw).1,
    fun w hw => (hPB2 w hw).2, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith [R.hpp])
  · intro v hv
    have hv1 : dist v 0 < ε1 := by rw [dist_zero_right]; linarith
    have hv2 : dist v 0 < ε2 := by rw [dist_zero_right]; linarith
    exact ⟨hball1 hv1, hball2 hv2⟩
  · intro v hv
    have hv3 : dist v 0 < ε3 := by rw [dist_zero_right]; linarith
    have hv4 : dist v 0 < ε4 := by rw [dist_zero_right]; linarith
    refine ⟨?_, ?_⟩
    · have h1 := hsmallP hv3
      rw [hP0, dist_zero_right] at h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
      have h2 : S.β * ‖P v‖ ≤ S.β * (T / (S.β + 1)) :=
        mul_le_mul_of_nonneg_left h1.le hβ.le
      have h3 : S.β * (T / (S.β + 1)) ≤ T := by
        rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    · intro y i
      have := hsmallB hv4
      rw [dist_eq_norm] at this
      exact (norm_svec_sub_le (B v) (B 0) y i).trans this.le
  · intro u hu x hx
    set p := min (pp / 2) (r / (2 * (Cs + 1))) with hp
    have hp1 : p ≤ r / (2 * (Cs + 1)) := min_le_right _ _
    have hsx : ‖S.shiftUC x‖ ≤ Cs * ‖x‖ := S.shiftL.le_opNorm x
    rw [norm_smul]
    have h1 : ‖u‖ * ‖S.shiftUC x‖ ≤ 2 * (Cs * p) :=
      mul_le_mul hu.le (hsx.trans (mul_le_mul_of_nonneg_left hx hCs0)) (norm_nonneg _)
        (by norm_num)
    have h2 : p * (2 * (Cs + 1)) ≤ r := (le_div_iff₀ hCs1).1 hp1
    have hp0 : 0 ≤ p := le_min (by linarith [R.hpp]) (div_pos hrpos hCs1).le
    nlinarith

end StepSetting

end Balaban.Fluctuation
