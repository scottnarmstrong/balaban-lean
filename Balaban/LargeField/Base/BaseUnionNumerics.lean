/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseLabelSum
public import Balaban.LargeField.Base.BaseChartTerms
import Mathlib.Tactic.Linarith

/-!
# The numerical hypotheses of the cluster expansion for the chart and defect activities

`union_numerics`: with `κ0 = a_ent + 1`, `Kc = K₀ + 1` and `T = κ' + 3 κ0 + c₁ + 3/2`, for `κ` at
least `1 + 2 log Δ + 4 d L 20^d T` the rate `labelRate` is at least `T` (`hκ` of
`marked_cubes_explicit`, `labelRate_ge`), and for `β ≥ β₀ = max 1 (4 coef C_c / ε_max)²` and a
defect amplitude at most `ε_max / 2` the amplitude of the union is at most
`ε_max = 1 / (8 Kc³ c₁ e^{(κH - 2κ0) c_G + c₁ + κ' c_G})` (`hε`).  The chart bound decays like
`β^{-1/2}` (`chartBound_le`, `chartBoundConst`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Fluctuation Balaban.Polymer

/-- The constant of the `β^{-1/2}` decay of `chartBound`. -/
noncomputable def chartBoundConst (d L N : ℕ) (a1 ν Aα Ee BW p₁ Gg : ℝ) : ℝ :=
  let H : ℝ := 4 * d + |ν| + |a1| / (L : ℝ) ^ 2 + Aα
  let q : ℝ := (1 + N * Ee ^ 2) * BW * p₁
  let u : ℝ := 3 / 2 * N * q ^ 2 * Ee
  H * N * q * u + 1 / 2 * H * N * u ^ 2 + 3 / 4 * N * q ^ 2 + Gg * (q + u)

theorem chartBound_le (d L N : ℕ) (a1 ν β Aα Ee BW p₁ Gg : ℝ) (hβ : 1 ≤ β) (hA : 0 ≤ Aα)
    (hE : 0 ≤ Ee) (hBW : 0 ≤ BW) (hp : 0 ≤ p₁) (hG : 0 ≤ Gg) :
    chartBound d L N a1 ν β Aα Ee BW p₁ Gg ≤
      chartBoundConst d L N a1 ν Aα Ee BW p₁ Gg / Real.sqrt β := by
  set s := Real.sqrt β with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.2 hβ
  have hs0 : 0 < s := by linarith
  have hβs : β = s ^ 2 := by rw [hs, Real.sq_sqrt (by linarith)]
  set H : ℝ := 4 * d + |ν| + |a1| / (L : ℝ) ^ 2 + Aα with hH
  set q : ℝ := (1 + N * Ee ^ 2) * BW * p₁ with hq
  set u : ℝ := 3 / 2 * N * q ^ 2 * Ee with hu
  have hH0 : 0 ≤ H := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hu0 : 0 ≤ u := by positivity
  have heq : chartBound d L N a1 ν β Aα Ee BW p₁ Gg =
      H * N * q * u / s + 1 / 2 * H * N * u ^ 2 / s ^ 2 + 3 / 4 * N * q ^ 2 / s ^ 2 +
        Gg * (q + u / s) / s := by
    unfold chartBound
    rw [hβs]
    rw [Real.sqrt_sq hs0.le]
    field_simp
    ring
  rw [heq]
  unfold chartBoundConst
  have h2 : 1 / s ^ 2 ≤ 1 / s := by
    apply one_div_le_one_div_of_le hs0; nlinarith
  have h3 : 1 / s ≤ 1 := by rw [div_le_one hs0]; exact hs1
  have hT2 : 1 / 2 * H * N * u ^ 2 / s ^ 2 ≤ 1 / 2 * H * N * u ^ 2 / s := by
    rw [div_eq_mul_one_div _ (s ^ 2), div_eq_mul_one_div _ s]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hT3 : 3 / 4 * N * q ^ 2 / s ^ 2 ≤ 3 / 4 * N * q ^ 2 / s := by
    rw [div_eq_mul_one_div _ (s ^ 2), div_eq_mul_one_div _ s]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hT4 : Gg * (q + u / s) / s ≤ Gg * (q + u) / s := by
    apply div_le_div_of_nonneg_right _ hs0.le
    exact mul_le_mul_of_nonneg_left (by
      have : u / s ≤ u := by rw [div_le_iff₀ hs0]; nlinarith
      linarith) hG
  calc _ ≤ H * N * q * u / s + 1 / 2 * H * N * u ^ 2 / s + 3 / 4 * N * q ^ 2 / s + Gg * (q + u) / s := by
        linarith
    _ = _ := by ring

/-- The largest amplitude permitted by `marked_cubes_explicit`. -/
noncomputable def epsMax (d L : ℕ) (Kc κH κ0 κ' : ℝ) : ℝ :=
  1 / (8 * Kc ^ 3 * c1 d L * Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))

theorem epsMax_pos (d L : ℕ) [NeZero L] {Kc : ℝ} (hKc : 0 < Kc) (κH κ0 κ' : ℝ) : 0 < epsMax d L Kc κH κ0 κ' := by
  unfold epsMax
  have : 0 < c1 d L := lt_of_lt_of_le one_pos (one_le_c1 d L)
  positivity

theorem labelAmp_eq (d L m₀ m₁ k ρs : ℕ) (κ B : ℝ) :
    labelAmp d L m₀ m₁ k ρs κ B = labelAmp d L m₀ m₁ k ρs κ 1 * B := by
  unfold labelAmp; ring

/-- The numerical condition `hε` of `marked_cubes_explicit` for the union family: for
`β ≥ β₀ = max 1 (4 coef Cc / ε_max)²`, if the amplitude of the defect is at most `ε_max / 2`. -/
theorem amp_le_epsMax {coef Cc B' Dm eps β : ℝ} (hcoef : 0 ≤ coef) (heps : 0 < eps)
    (hβ : 1 ≤ β) (hβ' : (4 * coef * Cc / eps) ^ 2 ≤ β) (hB : B' ≤ Cc / Real.sqrt β)
    (hD : Dm ≤ eps / 2) : coef * (2 * B') + Dm ≤ eps := by
  have hs0 : 0 < Real.sqrt β := Real.sqrt_pos.2 (by linarith)
  have h1 : 4 * coef * Cc / eps ≤ Real.sqrt β := by
    have := Real.abs_le_sqrt hβ'
    exact (le_abs_self _).trans this
  have h2 : coef * (2 * B') ≤ eps / 2 := by
    have hB2 : coef * (2 * B') ≤ coef * (2 * (Cc / Real.sqrt β)) :=
      mul_le_mul_of_nonneg_left (by linarith) hcoef
    refine hB2.trans ?_
    have : 2 * coef * Cc / Real.sqrt β ≤ eps / 2 := by
      rw [div_le_iff₀ hs0]
      have := (div_le_iff₀ heps).1 h1
      nlinarith
    calc coef * (2 * (Cc / Real.sqrt β)) = 2 * coef * Cc / Real.sqrt β := by ring
      _ ≤ _ := this
  linarith

/-- **The rate and the ratio for large `κ`.**  If `κ ≥ 1 + 2 log Δ + 4 d L 20^d T` with `T > 0`, then
`labelZ < 1` and `T ≤ labelRate`. -/
theorem labelRate_ge (d L k ρs : ℕ) (hd : 0 < d) [NeZero L] {κ T : ℝ} (hT : 0 < T)
    (hκ : 1 + 2 * Real.log (labelDelta d L k ρs : ℕ) + 4 * d * L * 20 ^ d * T ≤ κ) :
    labelZ d L k ρs κ < 1 ∧ T ≤ labelRate d L k ρs κ := by
  have hΔ : (1 : ℝ) ≤ (labelDelta d L k ρs : ℕ) := by
    unfold labelDelta
    exact_mod_cast (le_trans (Nat.succ_le_succ (Nat.zero_le _)) (le_max_left _ _))
  have hlogΔ : 0 ≤ Real.log (labelDelta d L k ρs : ℕ) := Real.log_nonneg hΔ
  have hz0 := labelZ_pos d L k ρs κ
  have hlog : Real.log (labelZ d L k ρs κ) = 2 * Real.log (labelDelta d L k ρs : ℕ) - (κ - 1) := by
    unfold labelZ
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    push_cast; ring
  have hD : (0 : ℝ) < 4 * d * L * 20 ^ d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hneg : Real.log (labelZ d L k ρs κ) < 0 := by
    rw [hlog]; nlinarith [mul_pos hD hT]
  refine ⟨?_, ?_⟩
  · have := Real.exp_lt_one_iff.2 hneg  -- exp(log z) < 1
    rwa [Real.exp_log hz0] at this
  · unfold labelRate
    have hP : (0 : ℝ) < (2 * d * L : ℝ) * 20 ^ d := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [div_div, le_div_iff₀ (by positivity)]
    have : 2 * ((2 * d * L : ℝ) * 20 ^ d) * T ≤ -Real.log (labelZ d L k ρs κ) := by
      rw [hlog]; nlinarith
    linarith


/-- **The numerical hypotheses of `marked_cubes_explicit` for the union family.**  Let
`κ0 = a_ent + 1`, `Kc = K₀(d, L, κ0) + 1`, `κ' ≥ 0`, `T = κ' + 3 κ0 + c₁ + 3/2`.  If `κ` is at least
`1 + 2 log Δ + 4 d L 20^d T`, then `labelZ < 1` and `T ≤ labelRate` (`hκ`).  If moreover
`β ≥ β₀ = max 1 (4 coef C_c / ε_max)²` (`coef = labelAmp 1`, `C_c = chartBoundConst`, `ε_max` the bound of
`hε` at the rate `labelRate`) and the defect amplitude is at most `ε_max / 2`, then the amplitude
`labelAmp (2 chartBound) + defAmp` of the union is at most `ε_max` (`hε`). -/
theorem union_numerics (d L N m₀ m₁ ρs : ℕ) [NeZero L] (hd : 0 < d) {κ' κ β : ℝ} (hκ' : 0 ≤ κ')
    (a1 ν Aα Ee BW p₁ Gg DefA : ℝ) (hA : 0 ≤ Aα) (hE : 0 ≤ Ee) (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (hG : 0 ≤ Gg)
    (hκ : 1 + 2 * Real.log (labelDelta d L 0 ρs : ℕ) +
      4 * d * L * 20 ^ d * (κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2) ≤ κ) (hβ1 : 1 ≤ β)
    (hβ : (4 * labelAmp d L m₀ m₁ 0 ρs κ 1 * chartBoundConst d L N a1 ν Aα Ee BW p₁ Gg /
      epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 ρs κ) (aEnt d L + 1) κ') ^ 2 ≤ β)
    (hDef : DefA ≤ epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 ρs κ) (aEnt d L + 1) κ' / 2) :
    labelZ d L 0 ρs κ < 1 ∧
    κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 ≤ labelRate d L 0 ρs κ ∧
    labelAmp d L m₀ m₁ 0 ρs κ (2 * chartBound d L N a1 ν β Aα Ee BW p₁ Gg) + DefA ≤
      epsMax d L (K0 d L (aEnt d L + 1) + 1) (labelRate d L 0 ρs κ) (aEnt d L + 1) κ' := by
  have hc1 := one_le_c1 d L
  have haent := aEnt_nonneg d L
  have hT : 0 < κ' + 3 * (aEnt d L + 1) + c1 d L + 3 / 2 := by linarith
  obtain ⟨hz, hrate⟩ := labelRate_ge d L 0 ρs hd hT hκ
  refine ⟨hz, hrate, ?_⟩
  have hK0 : 0 < K0 d L (aEnt d L + 1) + 1 := by
    have : 0 ≤ K0 d L (aEnt d L + 1) := by
      unfold K0
      have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
      exact (div_pos (Real.exp_pos _) (by linarith)).le
    linarith
  have heps := epsMax_pos d L hK0 (labelRate d L 0 ρs κ) (aEnt d L + 1) κ'
  have hcoef := labelAmp_nonneg d L m₀ m₁ 0 ρs κ (B := 1) zero_le_one hz
  rw [labelAmp_eq]
  exact amp_le_epsMax hcoef heps hβ1 hβ (chartBound_le d L N a1 ν β Aα Ee BW p₁ Gg hβ1 hA hE hBW hp hG)
    hDef

end Balaban.LargeField.Base
