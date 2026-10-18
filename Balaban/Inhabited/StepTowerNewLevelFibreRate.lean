/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelFibreSum
public import Balaban.Inhabited.StepTower

/-!
# The rate condition of the entropy count at the tower (`StepTowerNewLevelFibreRate`)

At `d = L = 3` the rate condition `κ < (ρ - a_ent - 1)/α` of `newLabels_hsum_of_chain_bound'`
holds for `ρ = κ′` of a `StepTower` and every `κ ≤ 1/5`:
`κ′ - a_ent - 1 = 150 (a_ent + 12 + c₁) + 2` with `c₁ = 3375`, `a_ent ≥ 131000`
(`131000 ≤ a_ent 3 3`), `α = 1 + 729 · 3375 · 36 = 88573501`, and `(κ′ - a_ent - 1)/α > 0.2275`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation

/-- `a_ent 3 3 ≥ 131000`. -/
theorem aEnt_three_ge : (131000 : ℝ) ≤ aEnt 3 3 := by
  have h1 : (2 : ℝ) ^ (3500 * 54) ≤ entQ 3 3 := by
    unfold entQ
    have hA : (1 : ℝ) ≤ (((2 * (3 - 1) + 1) ^ 3 : ℕ) : ℝ) := by norm_num
    have hB : (2 : ℝ) ^ 3500 ≤ 2 * (((3 ^ 3) ^ 2 : ℕ) : ℝ) *
        2 ^ (((2 * (3 - 1) + 1) ^ 3 * (1 + 3 ^ 3) : ℕ)) := by
      have : ((2 * (3 - 1) + 1) ^ 3 * (1 + 3 ^ 3) : ℕ) = 3500 := by norm_num
      rw [this]
      have : (1 : ℝ) ≤ 2 * (((3 ^ 3) ^ 2 : ℕ) : ℝ) := by norm_num
      exact le_mul_of_one_le_left (by positivity) this
    have hC : (2 : ℝ) ^ (3500 * 54) ≤ (2 * (((3 ^ 3) ^ 2 : ℕ) : ℝ) *
        2 ^ (((2 * (3 - 1) + 1) ^ 3 * (1 + 3 ^ 3) : ℕ))) ^ (2 * 3 ^ 3) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hB _
    calc (2 : ℝ) ^ (3500 * 54) ≤ _ := hC
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hA
  have h2 : Real.log ((2 : ℝ) ^ (3500 * 54)) ≤ aEnt 3 3 :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have := Real.log_two_gt_d9
  push_cast at h2
  nlinarith

/-- **The rate of the entropy count at the tower.**  For `d = L = 3` and `κ′` of a `StepTower`,
`1/5 < (κ′ - a_ent - 1)/α`, `α = 1 + (3^3 · 3^3) c₁ (4 · 3 · 3)`. -/
theorem tower_entropy_rate {κmin : ℝ} (T : StepTower κmin) :
    aEnt 3 3 + 1 ≤ T.κ' ∧ (1 : ℝ) / 5 < (T.κ' - (aEnt 3 3 + 1)) /
      (1 + ((3 ^ 3 * 3 ^ 3 : ℕ) : ℝ) * c1 3 3 * (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) := by
  have hc : c1 3 3 = 3375 := by unfold c1; norm_num
  have hge := aEnt_three_ge
  have e1 := T.κ'_eq
  have e2 := T.κdec_eq
  have e3 := T.κ0_eq
  have hα : (1 + ((3 ^ 3 * 3 ^ 3 : ℕ) : ℝ) * c1 3 3 * (4 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))) =
      88573501 := by rw [hc]; norm_num
  rw [hα]
  refine ⟨by rw [e1, e2, e3, hc]; nlinarith, ?_⟩
  rw [lt_div_iff₀ (by norm_num)]
  rw [e1, e2, e3, hc]
  nlinarith

end Balaban.Inhabited
