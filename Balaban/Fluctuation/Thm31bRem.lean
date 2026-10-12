/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31bFirst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): the remainder marks, and the algebra of `avgPi`

The remainder of P6 (4.58)-(4.60) is an interpolation average of a sum of marks
(`avg_integral_expansion`); here we add its integrability in `t` and the vanishing of its local
terms away from the point `x`.  We also prove the linearity of `avgPi` used to split the
integrand into the first-order part and the remainder.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Algebra

variable {Lb : Type*} [Fintype Lb] {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)]

theorem avgPi_add (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {H : Lb → (∀ b, Ωb b) → ℂ} {εH : ℝ} (hHm : ∀ y, Measurable (H y))
    (hHb : ∀ y Φ, ‖H y Φ‖ ≤ εH) {a b : (∀ b, Ωb b) → ℂ} (ha : Measurable a) (hb : Measurable b)
    {Fa Fb : ℝ} (hFa : ∀ Φ, ‖a Φ‖ ≤ Fa) (hFb : ∀ Φ, ‖b Φ‖ ≤ Fb) :
    avgPi μ H (fun Φ => a Φ + b Φ) = avgPi μ H a + avgPi μ H b := by
  unfold avgPi
  rw [← add_div]
  congr 1
  rw [← integral_add (integrable_mark_mul_exp μ hHm hHb ha hFa)
    (integrable_mark_mul_exp μ hHm hHb hb hFb)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun Φ => by simp [add_mul])

theorem avgPi_const_mul (μ : ∀ b, Measure (Ωb b)) (H : Lb → (∀ b, Ωb b) → ℂ) (c : ℂ)
    (G : (∀ b, Ωb b) → ℂ) :
    avgPi μ H (fun Φ => c * G Φ) = c * avgPi μ H G := by
  unfold avgPi
  rw [← mul_div_assoc, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun Φ => by simp [mul_assoc])

end Algebra

section Rem

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

open Classical in
/-- **The remainder, integrated over `t`** (§3.5 (b), "Remainder"): integrability of
`t ↦ ⟨∑ Gᵢ(t)⟩_t`, the expansion `∫₀¹ ⟨∑ Gᵢ(t)⟩_t dt = ∑_S E(S)`, `E(S) = ∫₀¹ ∑ᵢ G*ᵢ(t,S) dt`. -/
theorem rem_integral_expansion {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    {𝒰 : Set ℂ} (h𝒰 : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb) (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ i u, Measurable (G i u))
    (hGdep : ∀ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i u))
    (hG : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hAhol : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰)
    (hGhol : ∀ i Φ, DifferentiableOn ℂ (fun u => G i u Φ) 𝒰)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    IntervalIntegrable (fun s : ℝ => avgPi μ (A (s : ℂ)).H (fun Φ => ∑ i, G i (s : ℂ) Φ))
      MeasureTheory.volume 0 1 ∧
    (∫ s in (0 : ℝ)..1, avgPi μ (A (s : ℂ)).H (fun Φ => ∑ i, G i (s : ℂ) Φ)) =
      ∑ S : Finset 𝔅, ∫ s in (0 : ℝ)..1,
        Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) S := by
  obtain ⟨hhol, -, -⟩ := avg_integral_expansion μ hN hj hΩ h𝒰 hseg A y0 G hGm hGdep hG hAhol hGhol
    hκ0 hKc hεpos hι hF0 hκ' hκG hκ hε
  have hint : ∀ S : Finset 𝔅, IntervalIntegrable
      (fun s : ℝ => Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) S)
      MeasureTheory.volume 0 1 := fun S => by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact (hhol S).continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun s hs => hseg s hs)
  have hpt := fun u => avg_marks_expansion μ hN hj hΩ (A u) y0 (fun i => G i u)
    (fun i => hGm i u) (fun i => hGdep i u) (fun i => hG i u) hκ0 hKc hεpos hι hF0 hκ' hκG hκ hε
  exact intervalIntegral_sum_aux (fun S s => Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) S)
    (fun s => avgPi μ (A (s : ℂ)).H (fun Φ => ∑ i, G i (s : ℂ) Φ)) hint
    (fun s _ => (hpt (s : ℂ)).2.1)

open Classical in
/-- The local terms of the remainder vanish away from a block contained in every label. -/
theorem rem_support {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb) (G : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ i u, Measurable (G i u))
    (hGdep : ∀ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i u))
    (hG : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {bx : 𝔅} (hbx : ∀ i, bx ∈ blocksOf m₀ j Ω (Lab.ysite (y0 i))) (S : Finset 𝔅) (hS : bx ∉ S)
    (u : ℂ) : Gsum μ Lab (A u).H y0 (fun i => G i u) S = 0 := by
  unfold Gsum
  refine Finset.sum_eq_zero fun i _ => ?_
  exact (marked_cubes_explicit μ hN hj hΩ (A u) (y0 i) (G i u) (hGm i u) (hGdep i u) (hG i u) hκ0
    hKc hεpos (hF0 i) hκ' hκG hκ hε).2.2.2.1 S (fun hsub => hS (hsub (hbx i)))

end Rem

end Balaban.Fluctuation
