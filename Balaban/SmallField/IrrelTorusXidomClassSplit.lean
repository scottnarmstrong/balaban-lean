/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelBase

/-!
# Assemble the irrelevant label coefficients for the class chain

The four input estimates are the non-special and filed-defect labels, each in the far and near
scale regimes. The output is exactly the `Bτ`, `hBτ`, `hEbd`, `hEbI`, `hEbL` telescope consumed by
`e0CoeffFamily_class_fromTower_of_irrelBounds_base`. The predicate `special` is to be set to
`X = □(y)`; this keeps the filed-defect theorem independent of the non-special proof.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Localization Balaban.Background
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
  (C : StepClass 3 3 N₁ m₁ k 2 ϱ)
  (𝒯E : Finset (ℕ × CTorus 3 3 N₁ m₁ (k + 1) ×
    Set (CTorus 3 3 N₁ m₁ (k + 1))))
  (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ m₁) (k + 1) ϱ)
  (special : {τ // τ ∈ 𝒯E} → Prop)
  {P : Consts} {bL δ₃ δfl t κdec CI KL α₃ : ℝ} {n₁ : ℕ}
  (i₀ i₁ : Fin 2)

/-- The four per-label estimates assemble into the exact coefficient-family inputs of the
class chain. A birth-mass domain can be used upstream: this statement does not select a mass. -/
theorem irrelTorus_class_coefficients_of_split
    (hE₀ : 0 ≤ P.E₀) (hCI : 0 ≤ CI) (hKL : 0 ≤ KL)
    (hFarNonSpecial : ∀ τ : {τ // τ ∈ 𝒯E}, ¬special τ → τ.1.1 + n₁ ≤ k →
      ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
        (bL ^ 2 * t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
        (CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((3 : ℝ) + α₃))) *
          Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
    (hFarSpecial : ∀ τ : {τ // τ ∈ 𝒯E}, special τ → τ.1.1 + n₁ ≤ k →
      ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
        (bL ^ 2 * t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
        (CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((3 : ℝ) + α₃))) *
          Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
    (hNearNonSpecial : ∀ τ : {τ // τ ∈ 𝒯E}, ¬special τ → k < τ.1.1 + n₁ →
      ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
        (bL ^ 2 * t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
        (KL * P.E₀) *
          Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
    (hNearSpecial : ∀ τ : {τ // τ ∈ 𝒯E}, special τ → k < τ.1.1 + n₁ →
      ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
        (bL ^ 2 * t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
        (KL * P.E₀) *
          Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)) :
    ∃ Bτ : {τ // τ ∈ 𝒯E} → ℝ,
      (∀ τ, 0 ≤ Bτ τ) ∧
      (∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
        (bL ^ 2 * t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
        ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
          Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)) ∧
      (∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
        Bτ τ ≤ CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((3 : ℝ) + α₃))) ∧
      (∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀) := by
  classical
  let Bτ : {τ // τ ∈ 𝒯E} → ℝ := fun τ =>
    if τ.1.1 + n₁ ≤ k then
      CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((3 : ℝ) + α₃))
    else KL * P.E₀
  refine ⟨Bτ, ?_, ?_, ?_, ?_⟩
  · intro τ
    by_cases hfar : τ.1.1 + n₁ ≤ k
    · simp only [Bτ, hfar, ↓reduceIte]
      exact mul_nonneg (mul_nonneg hCI hE₀) (Real.rpow_nonneg (by positivity) _)
    · simp only [Bτ, hfar, ↓reduceIte]
      exact mul_nonneg hKL hE₀
  · intro τ r hr
    by_cases hfar : τ.1.1 + n₁ ≤ k
    · simp only [Bτ, hfar, ↓reduceIte]
      by_cases hspec : special τ
      · exact hFarSpecial τ hspec hfar r hr
      · exact hFarNonSpecial τ hspec hfar r hr
    · have hnear : k < τ.1.1 + n₁ := Nat.lt_of_not_ge hfar
      simp only [Bτ, hfar, ↓reduceIte]
      by_cases hspec : special τ
      · exact hNearSpecial τ hspec hnear r hr
      · exact hNearNonSpecial τ hspec hnear r hr
  · intro τ hfar
    simp only [Bτ, hfar, ↓reduceIte, le_refl]
  · intro τ hnear
    have hfar : ¬ τ.1.1 + n₁ ≤ k := Nat.not_le_of_gt hnear
    simp only [Bτ, hfar, ↓reduceIte, le_refl]

end Balaban.SmallField
