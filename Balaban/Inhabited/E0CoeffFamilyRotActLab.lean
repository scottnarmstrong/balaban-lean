/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1ParamRawLocal

/-!
# Spin covariance of the zero-source activity on the common labels

`commonAct_zeroSourceAct_H_rot`: the activity of a label of the zero-source common family at the
parameter `θ'` and a block configuration `Φ'` is the activity at `(θ, Φ)` as soon as the term map
`I.T` of the direct terms takes the same value at the corresponding hat variables and data.
-/

@[expose] public section

namespace Balaban.Inhabited

open MeasureTheory Metric Balaban Balaban.Fluctuation Balaban.Localization Balaban.Polymer
  Balaban.SmallField Balaban.Multiscale Balaban.Background Balaban.Analysis

section ActivityRot

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {F' : Type} {hp : 0 < S.p₁}
  {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a a₁ ν eps q : ℝ}
  {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
  {SΛ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
  {XW : Set (F' × F')}
  {val : F' → F' → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N ×
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (c : ℂ)
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val (physAgΘ S) AgF}
  (hF : DirectTermsFamilyOn S m₀ (physInclScaled N S c) I (physVq S a₁ ν eps q))
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)
  {β : Type*} [Fintype β]
  (reads : β → Set (CTorus d L N₁ m₁ (k + 1)))
  (dom : β → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
  (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ (k + 1) Y) (hL : 2 ≤ L)
  (hεH : 0 ≤ (2 : ℝ) ^ 2 * (Rσ * εU)) (hκ0' : aEnt d L + 2 ≤ κ0)

/-- **Spin covariance of the zero-source activity on the common labels.** -/
theorem commonAct_zeroSourceAct_H_rot (hq : 0 < q) (hR2 : 2 ≤ Rσ)
    {θ θ' : physParam N S} (hθ : θ ∈ physV S a₁ ν eps) (hθ' : θ' ∈ physV S a₁ ν eps) (u : ℂ)
    (y : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb m₀ reads dom) (Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    (hT : ∀ z : {Y // Y ∈ I.𝒴}, y = Sum.inl z → ‖u‖ < 2 →
      I.T z.1 (emb (S.hatOf m₀ ρ hp Φ')) (emb (S.hatOf m₀ ρ hp Φ')) u
        ((θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), 0) =
      I.T z.1 (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), 0)) :
    (commonAct (zeroSourceAct
      (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) 2 zero_le_two)
      hN hL reads dom hdom hεH hκ0' θ' u).H y Φ' =
    (commonAct (zeroSourceAct
      (labelActFamilyOn S m₀ (physInclScaled N S c) I hF hN hρ hRσ hεU hκ0 hKc) 2 zero_le_two)
      hN hL reads dom hdom hεH hκ0' θ u).H y Φ := by
  rcases y with z | z
  · rw [commonAct_H_inl, commonAct_H_inl, zeroSourceAct_H, zeroSourceAct_H]
    by_cases hu : ‖u‖ < 2
    · rw [sqFactor_of_lt hu]
      have hu' : ‖u‖ < Rσ := lt_of_lt_of_le hu hR2
      rw [labelActFamilyOn_H S m₀ (physInclScaled N S c) hF hN hρ hRσ hεU hκ0 hKc
          (zeroSource_mem_physVq S hq hθ') hu' z,
        labelActFamilyOn_H S m₀ (physInclScaled N S c) hF hN hρ hRσ hεU hκ0 hKc
          (zeroSource_mem_physVq S hq hθ) hu' z]
      simp only [physInclScaled_apply, Pi.zero_apply, mul_zero]
      exact congrArg (fun w => u ^ 2 * w) (hT z rfl hu)
    · have : sqFactor 2 u = 0 := by simp [sqFactor, hu]
      rw [this, zero_mul, zero_mul]
  · rw [commonAct_H_inr, commonAct_H_inr]

end ActivityRot

end Balaban.Inhabited
