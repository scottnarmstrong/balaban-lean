/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityWitnessNe
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Smallness of the interaction and the background variation along the ray

For a step datum with `RayData` (margin radius `p⁺`), `N = 2`, mass `0` and the constant unit
background of `θ`: for every `ε > 0` there are a radius `0 < p < p⁺` (`p ≤ 1`) and a point `x₀` with
`‖x₀‖ < p` such that, for all `‖x‖ < p` and `s ∈ [0,1]`,

* `‖V^{(k)}(ψ^{(k)} + s ψ'(ψ̂))‖ < ε` (the interaction exponent is small, `V^{(k)}(ψ^{(k)}) = 0`);
* every component of `svec φ_k` along the ray differs from its value at `ψ^{(k)}` by less than `1`;

and, at `x₀`, some component of `svec φ_k(ψ^{(k)} + ψ'(x₀))` differs from the one at `ψ^{(k)}`
(`exists_small_radius`).  The radius is read off from the continuity of `y ↦ V^{(k)}(ψ^{(k)} + y)` and
of the components of `svec φ_k` at `y = 0` (landed `RayData.contDiffAt_Vk_shift`,
`RayData.contDiffAt_shift`) and the operator norm of the linear map `ψ̂ ↦ ψ'`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.SmallField.Def6 Finset Set Filter Topology

namespace StepSetting

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {S : StepSetting d L N₁ m₁ k 2 ϱ}
  {pp : ℝ}

theorem exists_shiftU_bound (S : StepSetting d L N₁ m₁ k 2 ϱ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : S.E, ‖S.shiftU x‖ ≤ C * ‖x‖ := by
  let f : S.E →ₗ[ℝ] S.E := (S.betaU ^ (-(1 / 2 : ℝ))) • S.K
  have hf : ∀ x, S.shiftU x = f x := fun _ => rfl
  refine ⟨‖LinearMap.toContinuousLinearMap f‖ + 1, by positivity, fun x => ?_⟩
  rw [hf]
  calc ‖f x‖ = ‖LinearMap.toContinuousLinearMap f x‖ := rfl
    _ ≤ ‖LinearMap.toContinuousLinearMap f‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖LinearMap.toContinuousLinearMap f‖ + 1) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem shiftU_smul (τ : ℝ) (u : S.E) : S.shiftU (τ • u) = τ • S.shiftU u := by
  unfold shiftU
  rw [map_smul, smul_comm]

/-- The constant field `e₁ = (0,1)` on the unit lattice. -/
noncomputable def cvec (S : StepSetting d L N₁ m₁ k 2 ϱ) : S.E :=
  fun _ => WithLp.toLp 2 (![0, 1] : Fin 2 → ℝ)

/-- **The radius of smallness.** -/
theorem exists_small_radius (R : S.RayData pp) (hν : S.ν = 0)
    (hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2) (hp : 0 < S.p₁) (hlt : S.p₁ < pp)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ, 0 < p ∧ p < pp ∧ (∀ x : S.E, ‖x‖ < p → ∀ s ∈ Icc (0 : ℝ) 1,
        ‖S.Vk (S.psiAt s x)‖ < ε ∧ ∀ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2),
          ‖S.bgComp y i (s, x) - S.bgComp y i (0, x)‖ < 1) ∧
      ∃ x₀ : S.E, ‖x₀‖ < p ∧ ∃ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2),
        S.bgComp y i (1, x₀) ≠ S.bgComp y i (0, x₀) := by
  classical
  have hV0 : S.Vk S.psi0 = 0 := S.Vk_psi0 R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R
  have hcV : ContinuousAt (fun y => S.Vk (S.psi0 + y)) 0 := by
    have h := R.contDiffAt_Vk_shift hlt (x := 0) (by simpa using hp.le) (s := 0)
      ⟨le_rfl, zero_le_one⟩
    rw [zero_smul] at h
    exact h.continuousAt
  have hEV : ∀ᶠ y in 𝓝 (0 : S.E), ‖S.Vk (S.psi0 + y)‖ < ε :=
    hcV.norm.eventually_lt continuousAt_const (by simpa [hV0] using hε)
  have hcB : ∀ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin 2), ContinuousAt
      (fun z : S.E => svec (stepG d L N₁ m₁ k ϱ) (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν
        (S.dataU (S.psi0 + z))) y i) 0 := by
    intro y i
    have hq : |((1 : ℝ), S.unshiftU 0).1| * ‖((1 : ℝ), S.unshiftU 0).2‖ < pp := by
      simp [unshiftU, R.hpp]
    have h := R.contDiffAt_bgComp y i hq
    exact (R.contDiffAt_shift (G := fun ψ => svec (stepG d L N₁ m₁ k ϱ)
      (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ)) y i) (y := 0) h).continuousAt
  have hEB : ∀ᶠ z in 𝓝 (0 : S.E), ∀ pr : CTorus d L N₁ m₁ (k + 1) × Fin 2,
      ‖svec (stepG d L N₁ m₁ k ϱ) (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν
        (S.dataU (S.psi0 + z))) pr.1 pr.2 - svec (stepG d L N₁ m₁ k ϱ)
        (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU S.psi0)) pr.1 pr.2‖ < 1 := by
    rw [Filter.eventually_all]
    intro pr
    have hk : ContinuousAt (fun _ : S.E => svec (stepG d L N₁ m₁ k ϱ)
      (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU S.psi0)) pr.1 pr.2) 0 := continuousAt_const
    have hc := ((hcB pr.1 pr.2).sub hk).norm
    exact hc.eventually_lt continuousAt_const (by simp)
  obtain ⟨r, hr, hrP⟩ := Metric.eventually_nhds_iff.1 (hEV.and hEB)
  obtain ⟨C, hC, hCb⟩ := exists_shiftU_bound S
  set p : ℝ := min (pp / 2) (r / (2 * C)) with hpdef
  have hpp0 : 0 < pp := R.hpp
  have hp0 : 0 < p := lt_min (by positivity) (by positivity)
  have hppp : p < pp := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hpr : C * p ≤ r / 2 := by
    calc C * p ≤ C * (r / (2 * C)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le
      _ = r / 2 := by field_simp
  have hsmall : ∀ x : S.E, ‖x‖ < p → ∀ s ∈ Icc (0 : ℝ) 1, dist (s • S.shiftU x) 0 < r := by
    intro x hx s hs
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖S.shiftU x‖ ≤ 1 * ‖S.shiftU x‖ :=
          mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ ≤ C * ‖x‖ := by rw [one_mul]; exact hCb x
      _ < C * p := mul_lt_mul_of_pos_left hx hC
      _ ≤ r / 2 := hpr
      _ < r := by linarith
  refine ⟨p, hp0, hppp, fun x hx s hs => ?_, ?_⟩
  · have h := hrP (hsmall x hx s hs)
    refine ⟨h.1, fun y i => ?_⟩
    have := h.2 (y, i)
    simpa [bgComp, psiAt, StepSetting.psiAt_zero] using this
  · set u : S.E := S.unshiftU S.cvec with hu
    set τ : ℝ := p / (2 * (‖u‖ + 1)) with hτ
    have hτ0 : 0 < τ := by positivity
    set x₀ : S.E := τ • u with hx₀
    have hx₀n : ‖x₀‖ < p := by
      rw [hx₀, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0, hτ]
      have : p / (2 * (‖u‖ + 1)) * ‖u‖ < p := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg u]
      exact this
    have hsh : S.shiftU x₀ = τ • S.cvec := by
      rw [hx₀, shiftU_smul, hu, R.shiftU_unshiftU]
    have hdom := R.dom (q := ((1 : ℝ), x₀)) (by
      simp only [abs_one, one_mul]
      exact hx₀n.trans hppp)
    have hψ : ∀ x, liftU S.hG' (S.psiAt 1 x₀) x 1 = liftU S.hG' S.psi0 x 1 + τ := by
      intro x
      have : S.psiAt 1 x₀ = S.psi0 + τ • S.cvec := by
        unfold psiAt; rw [one_smul, hsh]
      rw [this, liftU_add, liftU_smul]
      have h1 : liftU S.hG' S.cvec x 1 = 1 := by
        show (S.cvec (unitPt S.hG' x)) 1 = 1
        simp [cvec]
      rw [h1, mul_one]
    have hne := R.bgField_ne hν hbg0 hdom hτ0.ne' hψ
    refine ⟨x₀, hx₀n, ?_⟩
    by_contra hcon
    push Not at hcon
    apply hne
    funext pq
    obtain ⟨⟨z, hz⟩, i⟩ := pq
    have h := hcon z i
    unfold bgComp at h
    rw [svec_of_mem _ _ ⟨z, hz⟩ i, svec_of_mem _ _ ⟨z, hz⟩ i] at h
    simpa [psiAt_zero] using h

end StepSetting

end Balaban.Fluctuation
