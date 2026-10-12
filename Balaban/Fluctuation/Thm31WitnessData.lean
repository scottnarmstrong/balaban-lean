/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31WitnessAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform bounds for the complex-analytic potential near the background

At a step with `RayData`, the analytic extension `P` of `w ↦ V^{(k)}(ψ^{(k)} + w)`
(`exists_analytic_ext`) is analytic at `w = 0` (the background, where `P 0 = 0`).  Hence, for a
fluctuation radius `p` small enough, for every complex interpolation parameter `u` in the disc
`|u| < 2` and every `‖ψ̂‖ ≤ p`, the point `u ψ'(ψ̂)` lies in a ball about `0` on which `P` is
analytic, `β P` is below any prescribed threshold, and `β DP[1_{B(z)}ψ']` is below any prescribed
threshold (`exists_tube_data`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix Filter Topology

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- `ψ̂ ↦ ψ'(ψ̂)`, the substitution (2.7) of the complex step, as a continuous `ℝ`-linear map. -/
noncomputable def shiftL : S.E →L[ℝ] S.EC :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => S.shiftUC x
      map_add' := fun x y => by
        simp only [shiftUC, S.yhat_add, map_add, smul_add]
      map_smul' := fun c x => by
        simp only [shiftUC, S.yhat_smul, map_smul, RingHom.id_apply]
        rw [← Complex.coe_smul, smul_comm] }

theorem shiftL_apply (x : S.E) : S.shiftL x = S.shiftUC x := rfl

/-- The restriction to the block `B(z)` as an `ℝ`-linear map. -/
noncomputable def maskLin (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : S.E →ₗ[ℝ] S.E where
  toFun := S.maskU z
  map_add' := fun x y => by
    funext b; simp only [maskU, Pi.add_apply]; split_ifs <;> simp
  map_smul' := fun c x => by
    funext b; simp only [maskU, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

/-- `ψ̂ ↦ yhat (1_{B(z)} ψ'(ψ̂))` as a continuous `ℝ`-linear map. -/
noncomputable def maskL (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) : S.E →L[ℝ] S.EC :=
  S.yhatL ∘L LinearMap.toContinuousLinearMap
    ((S.maskLin z).comp ((S.betaU ^ (-(1 / 2 : ℝ))) • S.K))

theorem maskL_apply (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E) :
    S.maskL z x = yhat (S.maskU z (S.shiftU x)) := rfl

/-- A ball about `0` on which an analytic function is analytic with a bounded derivative. -/
theorem exists_ball_analytic {P : S.EC → ℂ} (hP : AnalyticAt ℂ P 0) :
    ∃ r > 0, (∀ w : S.EC, ‖w‖ ≤ r → AnalyticAt ℂ P w) ∧
      ∃ M : ℝ, ∀ w : S.EC, ‖w‖ ≤ r → ‖fderiv ℂ P w‖ ≤ M := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hP.eventually_analyticAt
  have hr : 0 < ε / 2 := by positivity
  have hsub : ∀ w : S.EC, ‖w‖ ≤ ε / 2 → AnalyticAt ℂ P w := fun w hw =>
    hball (by rw [dist_zero_right]; linarith)
  refine ⟨ε / 2, hr, hsub, ?_⟩
  have hc : ContinuousOn (fderiv ℂ P) (Metric.closedBall (0 : S.EC) (ε / 2)) := fun w hw =>
    ((hsub w (by simpa using hw)).fderiv.continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : S.EC) (ε / 2)).exists_bound_of_continuousOn hc
  exact ⟨M, fun w hw => hM w (by simpa using hw)⟩

variable {S} {pp : ℝ}

theorem exists_tube_data (R : S.RayData pp) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    ∃ (P : S.EC → ℂ) (p : ℝ), 0 < p ∧ p < pp ∧
      (∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w) ∧ (∀ w, S.InDom w → AnalyticAt ℂ P w) ∧
      ∀ u : ℂ, ‖u‖ < 2 → ∀ x : S.E, ‖x‖ ≤ p →
        AnalyticAt ℂ P (u • S.shiftUC x) ∧ ‖(S.β : ℂ) * P (u • S.shiftUC x)‖ ≤ T ∧
        ‖(S.β : ℂ) * (fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x)‖ ≤ η := by
  obtain ⟨hD1, hD2⟩ := S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R
  obtain ⟨P, B, hPB1, hPB2⟩ := S.exists_analytic_ext R.ha₁ R.H hD2
  have hPa : ∀ w, S.InDom w → AnalyticAt ℂ P w := fun w hw => (hPB1 w hw).1
  have hP : ∀ w, S.InDom w → S.VkC (S.psi0C + w) = P w := fun w hw => (hPB2 w hw).1
  have h0 : S.InDom 0 := by
    have := R.inDom_yhat (y := 0) (by
      have : S.unshiftU 0 = 0 := by simp [unshiftU]
      rw [this, norm_zero]; exact R.hpp)
    have e : yhat (0 : S.E) = (0 : S.EC) := by funext q; simp [yhat]
    rwa [e] at this
  have hP0 : P 0 = 0 := by
    rw [← hP 0 h0, add_zero]
    exact S.VkC_psi0C R.ha₁ R.H (hD2.mono (thm73C2_le_thm73C1 d L N))
  have hβ := R.hβ
  obtain ⟨r, hr, hana, M, hM⟩ := S.exists_ball_analytic (hPa 0 h0)
  have hcont := (hPa 0 h0).continuousAt
  obtain ⟨r', hr', hsmall⟩ := Metric.continuousAt_iff.1 hcont (T / (S.β + 1)) (by positivity)
  set r2 := min r (r' / 2) with hr2
  have hr2pos : 0 < r2 := lt_min hr (by positivity)
  set Cs := ‖S.shiftL‖ with hCs
  set Cm := ‖S.maskL z‖ with hCm
  set M' := max M 0 with hM'
  have hCs0 : 0 ≤ Cs := norm_nonneg _
  have hCm0 : 0 ≤ Cm := norm_nonneg _
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set A := (S.β + 1) * (M' + 1) * (Cm + 1) with hA
  have hApos : 0 < A := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hCs1 : 0 < 2 * (Cs + 1) := by linarith
  refine ⟨P, min (pp / 2) (min (r2 / (2 * (Cs + 1))) (η / A)), lt_min (by linarith [R.hpp])
    (lt_min (div_pos hr2pos hCs1) (div_pos hη hApos)), ?_, hP, hPa, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith [R.hpp])
  intro u hu x hx
  set p := min (pp / 2) (min (r2 / (2 * (Cs + 1))) (η / A)) with hp
  have hp1 : p ≤ r2 / (2 * (Cs + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hp2 : p ≤ η / A := (min_le_right _ _).trans (min_le_right _ _)
  have hp0 : 0 ≤ p := le_min (by linarith [R.hpp]) (le_min (div_pos hr2pos hCs1).le
    (div_pos hη hApos).le)
  have hsx : ‖S.shiftUC x‖ ≤ Cs * ‖x‖ := S.shiftL.le_opNorm x
  have hw : ‖u • S.shiftUC x‖ ≤ r2 := by
    rw [norm_smul]
    have h1 : ‖u‖ * ‖S.shiftUC x‖ ≤ 2 * (Cs * p) :=
      mul_le_mul hu.le (hsx.trans (mul_le_mul_of_nonneg_left hx hCs0)) (norm_nonneg _)
        (by norm_num)
    have h2 : p * (2 * (Cs + 1)) ≤ r2 := by
      exact (le_div_iff₀ hCs1).1 hp1
    nlinarith
  refine ⟨hana _ (hw.trans (min_le_left _ _)), ?_, ?_⟩
  · have hwr : ‖u • S.shiftUC x‖ < r' := lt_of_le_of_lt (hw.trans (min_le_right _ _))
      (by linarith)
    have h1 := hsmall (x := u • S.shiftUC x) (by rwa [dist_zero_right])
    rw [hP0, dist_zero_right] at h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
    have h2 : S.β * ‖P (u • S.shiftUC x)‖ ≤ S.β * (T / (S.β + 1)) :=
      mul_le_mul_of_nonneg_left h1.le hβ.le
    have h3 : S.β * (T / (S.β + 1)) ≤ T := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
    have h1 : ‖(fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x)‖ ≤ M' * (Cm * p) := by
      calc ‖(fderiv ℂ P (u • S.shiftUC x)) (S.maskL z x)‖
          ≤ ‖fderiv ℂ P (u • S.shiftUC x)‖ * ‖S.maskL z x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M' * (Cm * p) := by
          refine mul_le_mul ((hM _ (hw.trans (min_le_left _ _))).trans (le_max_left _ _))
            ((S.maskL z).le_opNorm x |>.trans (mul_le_mul_of_nonneg_left hx hCm0))
            (norm_nonneg _) hM'0
    have h2 : S.β * (M' * (Cm * p)) ≤ A * p := by
      rw [hA]
      have : S.β * M' * Cm ≤ (S.β + 1) * (M' + 1) * (Cm + 1) := by
        have hb : 0 ≤ S.β := hβ.le
        nlinarith [mul_nonneg hb hM'0, mul_nonneg (mul_nonneg hb hM'0) hCm0,
          mul_nonneg hb hCm0, mul_nonneg hM'0 hCm0]
      nlinarith
    have h3 : A * p ≤ η := by
      have := (le_div_iff₀ hApos).1 hp2
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hβ.le]

end StepSetting

end Balaban.Fluctuation
