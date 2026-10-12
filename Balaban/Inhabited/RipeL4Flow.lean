/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.JointL4
public import Balaban.Inhabited.RipeHistory

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `L = 4` flow with `k₀ = T` (ripe regime)

At `d = 3`, `L = M = 4` and the setting `JointL4.setting β`, let `T = t^*(Active(1,1,∅), s = 1)`
(`RipeHist.Tstar`).  The flow has `β_k = β 4^k`, `ν_k = ν 16^k` with the tiny mass
`ν = 1 / (β 64^T)`, so that `β_k ν_k = 64^(k-T)`: the regime index is `k₀ = T ≥ 1`, and
`k₀ < k_f`.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace RipeL4

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness

/-- The ripeness time of the book `Active(1,1,∅)`, clock `1`, for `JointL4.setting β`. -/
noncomputable def T (β : ℝ) : ℕ := RipeHist.Tstar (JointL4.setting β)

theorem one_le_T (β : ℝ) : 1 ≤ T β := RipeHist.one_le_Tstar _

/-- The mass `ν = 1 / (β 64^T)`. -/
noncomputable def nuT (β : ℝ) : ℝ := 1 / (β * 64 ^ T β)

theorem nuT_pos (β : ℝ) (hβ : 20 < β) : 0 < nuT β := by
  unfold nuT; have : 0 < β := by linarith
  positivity

theorem beta_mul_nuT (β : ℝ) (hβ : 20 < β) : β * nuT β = 1 / 64 ^ T β := by
  unfold nuT
  have : β ≠ 0 := by linarith
  field_simp

theorem nuT_le (β : ℝ) (hβ : 20 < β) : nuT β ≤ 1 / 1280 := by
  unfold nuT
  have h1 : (64 : ℝ) ≤ 64 ^ T β := by
    calc (64 : ℝ) = 64 ^ 1 := by norm_num
      _ ≤ 64 ^ T β := pow_le_pow_right₀ (by norm_num) (one_le_T β)
  rw [div_le_div_iff₀ (by have : 0 < β := by linarith
                          positivity) (by norm_num)]
  nlinarith

/-- The flow data: `ν = 1/(β 64^T)`. -/
noncomputable def flow (β : ℝ) (hβ : 20 < β) : FlowSeq where
  d := 3
  L := 4
  β := β
  ν := nuT β
  a := 5 / 4
  γ := fun _ => 1
  δ := fun _ => 1
  hd := le_rfl
  hL := by norm_num
  hβ := by linarith
  hν0 := nuT_pos β hβ
  hν1 := (nuT_le β hβ).trans (by norm_num)
  ha1 := by norm_num
  ha2 := by norm_num
  hγ := fun _ => by norm_num
  hδ := fun _ => by norm_num
  hγ0 := rfl
  hδ0 := rfl

theorem flow_matches (β : ℝ) (hβ : 20 < β) : (flow β hβ).Matches (JointL4.setting β) where
  d_eq := rfl
  L_eq := rfl
  lam_eq := fun j => by
    rw [JointL4.setting_lam]
    simp [FlowSeq.lamHat, flow, FlowSeq.e]
  cH_eq := by
    show 3 * Real.log 4 = ((3 : ℕ) + 3 : ℝ) * (((3 : ℕ) - 2 : ℕ) : ℝ) / 2 * Real.log ((4 : ℕ) : ℝ)
    norm_num

theorem flow_e (β : ℝ) (hβ : 20 < β) : (flow β hβ).e = 1 := rfl

theorem flow_beta (β : ℝ) (hβ : 20 < β) (k : ℕ) : (flow β hβ).beta k = β * 4 ^ k := by
  unfold FlowSeq.beta; rw [flow_e]; simp [flow]

theorem flow_nu (β : ℝ) (hβ : 20 < β) (k : ℕ) : (flow β hβ).nu k = nuT β * 16 ^ k := by
  unfold FlowSeq.nu
  simp only [flow, pow_mul, mul_one]
  norm_num

theorem flow_betanu (β : ℝ) (hβ : 20 < β) (k : ℕ) :
    (flow β hβ).beta k * (flow β hβ).nu k = 64 ^ k / 64 ^ T β := by
  rw [flow_beta, flow_nu]
  have h : β * 4 ^ k * (nuT β * 16 ^ k) = (β * nuT β) * (4 ^ k * 16 ^ k) := by ring
  rw [h, beta_mul_nuT β hβ, ← mul_pow]
  norm_num
  ring

/-- The regime index is exactly `T`. -/
theorem flow_k0 (β : ℝ) (hβ : 20 < β) : (flow β hβ).k0 = T β := by
  have hpos : (0 : ℝ) < 64 ^ T β := by positivity
  rcases (flow β hβ).k0_cases with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [flow_betanu, div_le_one hpos] at h1
    rw [flow_betanu, one_lt_div hpos] at h2
    have a1 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 64)).mp h1
    have a2 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 64)).mp h2
    omega
  · exfalso
    have h1' : 1 < β * nuT β := h1
    rw [beta_mul_nuT β hβ] at h1'
    have h3 : 1 / (64 : ℝ) ^ T β ≤ 1 := by
      rw [div_le_one hpos]; exact one_le_pow₀ (by norm_num)
    linarith

theorem flow_one_le_kf (β : ℝ) (hβ : 20 < β) : 1 ≤ (flow β hβ).kf := by
  by_contra h
  have h0 : (flow β hβ).kf = 0 := by omega
  have hk := (flow β hβ).kf_spec
  rw [h0] at hk
  have : (flow β hβ).nu 0 = nuT β := by rw [flow_nu]; simp
  rw [this] at hk
  have h2 : ((flow β hβ).L : ℝ) = 4 := by simp [flow]
  rw [h2] at hk
  have := nuT_le β hβ
  norm_num at hk
  linarith

theorem flow_hgen (β : ℝ) (hβ : 20 < β) :
    (flow β hβ).beta (flow β hβ).k0 * (flow β hβ).nu (flow β hβ).k0 ≤ 1 →
      2 * ((flow β hβ).L : ℝ) ^ 2 ≤ (flow β hβ).beta (flow β hβ).k0 := by
  intro _
  rw [flow_k0]
  have h1 : (4 : ℝ) ≤ 4 ^ T β := by
    calc (4 : ℝ) = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ T β := pow_le_pow_right₀ (by norm_num) (one_le_T β)
  have h2 : (flow β hβ).beta (T β) = β * 4 ^ T β := flow_beta β hβ _
  have h3 : ((flow β hβ).L : ℝ) = 4 := by simp [flow]
  rw [h2, h3]
  nlinarith

theorem flow_k0_lt_kf (β : ℝ) (hβ : 20 < β) : T β < (flow β hβ).kf := by
  have := (flow β hβ).k0_lt_kf (flow_one_le_kf β hβ) (flow_hgen β hβ)
  rwa [flow_k0] at this

theorem flow_hΛ12 (β : ℝ) (hβ : 20 < β) (h12 : 12 ≤ Real.log (β * (5 / 4)) + 1) :
    (((flow β hβ).d : ℝ) + 3) / 2 ≤
      (JointL4.setting β).lam (flow β hβ).k0 * (1 - 1 / (2 * Real.log (flow β hβ).L)) := by
  have hlam : 12 ≤ (JointL4.setting β).lam (flow β hβ).k0 := by
    rw [JointL4.setting_lam]
    have := JointL4.log_four_pos
    have : (0 : ℝ) ≤ ((flow β hβ).k0 : ℝ) * Real.log 4 := by positivity
    linarith
  have hd : (((flow β hβ).d : ℝ) + 3) / 2 = 3 := by simp [flow]
  have hL : Real.log ((flow β hβ).L : ℝ) = Real.log 4 := by simp [flow]
  rw [hd, hL]
  have h6 := JointL4.log_four_gt
  have hc : 1 / 4 ≤ 1 - 1 / (2 * Real.log 4) := by
    have : 1 / (2 * Real.log 4) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  nlinarith

/-- The budget setup with the flow's mass `ν = 1/(β 64^T)`. -/
noncomputable def budgetSetup (β : ℝ) (hβ : 20 < β)
    (ha : JointL4.anaThreshold ≤ Real.log (β * (5 / 4)) + 1) :
    BudgetSetup (JointL4.setting β) (JointL4.budgetConsts β) where
  β := β
  ν := nuT β
  a := 5 / 4
  ε := 0
  nuRun := fun k => nuT β * 16 ^ k
  K := JointL4.anaK
  run :=
    { hd := by show 2 ≤ 3; norm_num
      hL := by show 2 ≤ 4; norm_num
      hβ := by linarith
      hν := nuT_pos β hβ
      ha1 := by norm_num
      ha2 := by norm_num
      hε0 := le_rfl
      hε := by norm_num
      beta_eq := fun k => ⟨1, one_pos, by simp, by
        show β * 4 ^ k = β * ((4 : ℕ) : ℝ) ^ (k * (3 - 2)) * 1
        simp⟩
      nu_eq := fun k => ⟨1, one_pos, by simp, by
        show nuT β * 16 ^ k = nuT β * ((4 : ℕ) : ℝ) ^ (2 * k) * 1
        rw [pow_mul]; norm_num⟩ }
  lam_eq := fun j => by
    rw [JointL4.setting_lam]
    simp [lamHat, thetaOf, JointL4.setting, JointL4.typing, JointL4.typing0]
  Kd := rfl
  KL := rfl
  Kp0 := rfl
  KH0 := rfl
  Kc2 := rfl
  lam_cond := fun j => JointL4.anaK_at (by
    rw [JointL4.setting_lam]
    have := JointL4.log_four_pos
    have : (0 : ℝ) ≤ (j : ℝ) * Real.log 4 := by positivity
    linarith)
  H0_nonneg := by show (0 : ℝ) ≤ 2; norm_num
  c1_nonneg := le_rfl
  L_le_M := by show 4 ≤ 4; exact le_rfl
  cv_ge := by
    show ((4 : ℕ) : ℝ) ^ 3 * (2 + 0 + 3) ≤ 320
    norm_num

end RipeL4
end Balaban.Inhabited
