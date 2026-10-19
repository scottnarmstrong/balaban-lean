/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerGProducers
public import Balaban.Inhabited.BgSettingDataNum
import Mathlib.Tactic.Linarith

/-!
# Towers whose step size satisfies the numerical smallness conditions

`exists_stepTower_pred`: the fixed tower of `exists_stepTower` can be taken with any predicate on
`(m₁, BG, BG₂, κ, t)` that holds for all small `t > 0` and every choice of the other parameters.
`exists_stepTower_base` applies it to the smallness conditions `ChainNum`, `FlNum` of
`joint_num_eventually` at `r₀ = 324`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Filter Topology

/-- **The general tower record with an eventual predicate on its step size**, with `κ₀ = a_Ent + 2`
and cover index `m₀ = 1`. -/
theorem StepTowerG.exists_pred (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (κmin : ℝ) (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T : StepTowerG d L N κmin, Pr T.m₁ T.BG T.BG₂ T.κ T.t ∧ T.m₀ = 1 ∧ T.κ0 = aEnt d L + 2 := by
  obtain ⟨T, hPT, hm, -, h0⟩ := exists_stepTowerThetaG_pred d L N hd hL hN 1 le_rfl 0 0 κmin Pr hP
  have := aEnt_nonneg d L
  exact ⟨T.toStepTowerRenSolG.toStepTowerRenEndG.toStepTowerRenG.toStepTowerG, hPT, hm,
    h0 (by simp; linarith)⟩

/-- **General towers with the smallness conditions `ChainNum`, `FlNum`** at any collar `r₀`. -/
theorem StepTowerG.exists_base (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (κmin r₀ : ℝ) :
    ∃ (T : StepTowerG d L N κmin) (δ₃ δfl : ℝ), T.m₀ = 1 ∧ T.κ0 = aEnt d L + 2 ∧
      ChainNum d L N T.m₁ T.BG T.κ r₀ T.t δ₃ ∧ FlNum d L N T.BG T.BG₂ T.κ T.t δ₃ T.t δfl := by
  obtain ⟨T, hT, hm, h0⟩ := StepTowerG.exists_pred d L N hd hL hN κmin
    (fun m₁ BG BG₂ κ t => 0 ≤ BG → 0 ≤ BG₂ → ∃ δ₃ δfl : ℝ,
      ChainNum d L N m₁ BG κ r₀ t δ₃ ∧ FlNum d L N BG BG₂ κ t δ₃ t δfl)
    (fun m₁ BG BG₂ κ => by
      by_cases h : 0 ≤ BG ∧ 0 ≤ BG₂
      · exact (BgSettingData.joint_num_eventually d L N m₁ (by omega) h.1 h.2 κ r₀).mono
          fun t ht _ _ => ht
      · exact Eventually.of_forall fun t h1 h2 => absurd ⟨h1, h2⟩ h)
  obtain ⟨hC⟩ := T.core
  obtain ⟨δ₃, δfl, h1, h2⟩ := hT hC.hS.fam.2.1 hC.hS2.fam.2.1
  exact ⟨T, δ₃, δfl, hm, h0, h1, h2⟩

/-- **The tower record with an eventual predicate on its step size.** -/
theorem exists_stepTower_pred (κmin : ℝ) (Pr : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hP : ∀ m₁ BG BG₂ κ, ∀ᶠ t in 𝓝[>] (0 : ℝ), Pr m₁ BG BG₂ κ t) :
    ∃ T : StepTower κmin, Pr T.m₁ T.BG T.BG₂ T.κ T.t := by
  obtain ⟨T, hPT, hm, -, h0⟩ :=
    exists_stepTowerThetaG_pred 3 3 2 le_rfl le_rfl le_rfl 1 le_rfl 0 0 κmin Pr hP
  have := aEnt_nonneg 3 3
  exact ⟨T.toStepTowerRenSolG.toStepTowerRenEndG.toStepTowerRenG.toStepTowerG.ofThree
    (h0 (by simp; linarith)) hm, hPT⟩

/-- **Towers with the smallness conditions `ChainNum`, `FlNum`.** For every `κmin` there is a tower
`T` and constants `δ₃`, `δ_fl` with `ChainNum` and `FlNum` at the tower's own `m₁, BG, BG₂, κ, t`
and `r₀ = 324`. -/
theorem exists_stepTower_base (κmin : ℝ) :
    ∃ (T : StepTower κmin) (δ₃ δfl : ℝ),
      ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl := by
  obtain ⟨T, δ₃, δfl, hm, h0, h1, h2⟩ := StepTowerG.exists_base 3 3 2 le_rfl le_rfl le_rfl κmin 324
  exact ⟨T.ofThree h0 hm, δ₃, δfl, h1, h2⟩

/-- **The label rate of the class chain at a general tower.**  For every cover index `m₀` there is a
lower bound `κmin` such that every tower `T : StepTowerG d L N κmin` with `κ₀ = a_Ent + 2` admits a
label rate `κdec` with `4 d (2L+1)^d κdec ≤ T.κ` and `(2 T.κdec - 1) A_{m₀} + 1 ≤ 2 κdec`, where
`A_{m₀} = L^{m₀-1} + 2 d L^{m₀} (L^{m₀-1})^d c₁`. -/
theorem StepTowerG.exists_labelRate (d L N : ℕ) [NeZero L] (m₀ : ℕ) (κlo : ℝ) :
    ∃ κmin : ℝ, κlo ≤ κmin ∧ ∀ T : StepTowerG d L N κmin, T.κ0 = aEnt d L + 2 → ∃ κdec : ℝ,
      4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * ((L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
        (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec := by
  set K : ℝ := 100 * (aEnt d L + 2 + c1 d L + 10) with hK
  set A : ℝ := (L : ℝ) ^ (m₀ - 1) + 2 * (d : ℝ) *
        (L : ℝ) ^ m₀ * ((((L ^ (m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L with hA
  refine ⟨max κlo (2 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * ((2 * K - 1) * A + 1)),
    le_max_left _ _, fun T h0 => ?_⟩
  have hTK : T.κdec = K := by rw [T.κdec_eq, h0, hK]
  refine ⟨((2 * T.κdec - 1) * A + 1) / 2, ?_, by linarith⟩
  have := (le_max_right _ _).trans T.κmin_le
  rw [hTK]
  linarith

/-- **The label rate of the class chain at a tower.**  For every cover index `m₀` there is a lower
bound `κmin` such that every tower `T : StepTower κmin` admits a label rate `κdec` with
`4·3·7³ κdec ≤ T.κ` and `(2 T.κdec - 1) A_{m₀} + 1 ≤ 2 κdec`, where
`A_{m₀} = 3^{m₀-1} + 2·3·3^{m₀}·(3^{m₀-1})³ c₁`.  (The tower rate `T.κdec` is a fixed number.) -/
theorem exists_stepTower_labelRate (m₀ : ℕ) (κlo : ℝ) :
    ∃ κmin : ℝ, κlo ≤ κmin ∧ ∀ T : StepTower κmin, ∃ κdec : ℝ,
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec := by
  obtain ⟨κmin, hlo, hk⟩ := StepTowerG.exists_labelRate 3 3 2 m₀ κlo
  exact ⟨κmin, hlo, fun T => hk T.toG T.κ0_eq⟩

/-- **The numerical premises at one tower.**  For every cover index `m₀` and floor `κlo` there are
`κmin ≥ κlo`, a tower `T : StepTower κmin` and constants `δ₃`, `δ_fl`, `κ_dec` with `ChainNum`,
`FlNum` at the tower's own parameters and the two label-rate inequalities at `m₀`. -/
theorem exists_stepTower_base_rate (m₀ : ℕ) (κlo : ℝ) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ),
      ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec := by
  obtain ⟨κmin, hlo, hk⟩ := exists_stepTower_labelRate m₀ κlo
  obtain ⟨T, δ₃, δfl, h1, h2⟩ := exists_stepTower_base κmin
  obtain ⟨κdec, h3, h4⟩ := hk T
  exact ⟨κmin, hlo, T, δ₃, δfl, κdec, h1, h2, h3, h4⟩

end Balaban.Inhabited
