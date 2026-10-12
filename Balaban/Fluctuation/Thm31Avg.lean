/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedCubesLocal
public import Balaban.Polymer.MarkedCubesHolo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (a)-(e), the core: integrated marked expansions (FLUCTUATION.md §3.5)

Theorem 3.4 (`marked_cubes_explicit`) is a statement for one mark `G`.  The contributions of
Theorem 3.1 are averages of a *sum* of marks (the labels `Y₀ ∋ z` of the expansion of the
integrand), integrated over the interpolation parameter `s ∈ [0,1]` (§3.5, (a)).  This file proves
the two bookkeeping steps, with no assumption beyond the hypotheses of Theorem 3.4:

* `avg_marks_expansion`: `⟨∑ᵢ Gᵢ⟩ = ∑_S ∑ᵢ G*(Y₀ᵢ, S)` with
  `|∑ᵢ G*(Y₀ᵢ,S)| ≤ C_PE (∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) e^{-κ' d_Ω(S)}`;
* `avg_integral_expansion`: for a family `u ↦ (A u, Gᵢ u)` holomorphic on an open set `𝒰`
  containing `[0,1]`, `∫₀¹ ⟨∑ᵢ Gᵢ(s)⟩_s ds = ∑_S E(S)` with `E(S) = ∫₀¹ ∑ᵢ G*ᵢ(s,S) ds`
  satisfying the same bound, and `u ↦ ∑ᵢ G*ᵢ(u,S)` holomorphic on `𝒰`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Avg

variable {Lb : Type*} [Fintype Lb]

/-- **The expectation of `G`** for the measure `Z⁻¹ e^{∑_Y H(Y)} d(⊗ μ_b)`. -/
noncomputable def avgPi {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b))
    (H : Lb → (∀ b, Ωb b) → ℂ) (G : (∀ b, Ωb b) → ℂ) : ℂ :=
  (∫ Φ, G Φ * Complex.exp (∑ y, H y Φ) ∂(Measure.pi μ)) /
    ∫ Φ, Complex.exp (∑ y, H y Φ) ∂(Measure.pi μ)

theorem integrable_mark_mul_exp {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {H : Lb → (∀ b, Ωb b) → ℂ} {εH : ℝ} (hHm : ∀ y, Measurable (H y))
    (hHb : ∀ y Φ, ‖H y Φ‖ ≤ εH) {G : (∀ b, Ωb b) → ℂ} (hGm : Measurable G) {F0 : ℝ}
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0) :
    Integrable (fun Φ => G Φ * Complex.exp (∑ y, H y Φ)) (Measure.pi μ) := by
  have hm : Measurable (fun Φ => G Φ * Complex.exp (∑ y, H y Φ)) :=
    hGm.mul (Complex.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hHm y))
  refine Integrable.of_bound hm.aestronglyMeasurable (F0 * Real.exp (∑ _y : Lb, εH))
    (Filter.Eventually.of_forall fun Φ => ?_)
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul (hG Φ) ?_ (Real.exp_pos _).le ((norm_nonneg _).trans (hG Φ))
  refine Real.exp_le_exp.2 ?_
  exact (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hHb y Φ))

theorem avgPi_sum {ι : Type*} [Fintype ι] {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    {H : Lb → (∀ b, Ωb b) → ℂ} {εH : ℝ} (hHm : ∀ y, Measurable (H y))
    (hHb : ∀ y Φ, ‖H y Φ‖ ≤ εH) (G : ι → (∀ b, Ωb b) → ℂ) (hGm : ∀ i, Measurable (G i))
    (F0 : ι → ℝ) (hG : ∀ i Φ, ‖G i Φ‖ ≤ F0 i) :
    avgPi μ H (fun Φ => ∑ i, G i Φ) = ∑ i, avgPi μ H (G i) := by
  unfold avgPi
  rw [← Finset.sum_div]
  congr 1
  rw [← integral_finsetSum _ fun i _ => integrable_mark_mul_exp μ hHm hHb (hGm i) (hG i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  simp [Finset.sum_mul]

end Avg


section Marks

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

open Classical in
/-- **The local term of `⟨∑ᵢ Gᵢ⟩`**: `∑ᵢ G*(Y₀ᵢ, S)`. -/
noncomputable def Gsum {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    (H : Lb → (∀ b, Ωb b) → ℂ) (y0 : ι → Lb) (G : ι → (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) : ℂ :=
  ∑ i, Gst μ Lab H (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i) S

open Classical in
/-- **Theorem 3.4 for a sum of marks.**  `⟨∑ᵢ Gᵢ⟩ = ∑_S ∑ᵢ G*(Y₀ᵢ,S)` and
`|∑ᵢ G*(Y₀ᵢ,S)| ≤ C_PE (∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) e^{-κ' d_Ω(S)}`. -/
theorem avg_marks_expansion {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc : ℝ} {F0 : ι → ℝ}
    (A : LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb) (G : ι → (∀ b, Ωb b) → ℂ)
    (hGm : ∀ i, Measurable (G i))
    (hGdep : ∀ i, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i))
    (hG : ∀ i Φ, ‖G i Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i)))
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hι : Nonempty ι) (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))) :
    (∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0) ∧
    avgPi μ A.H (fun Φ => ∑ i, G i Φ) = ∑ S : Finset 𝔅, Gsum μ Lab A.H y0 G S ∧
    ∀ S : Finset 𝔅, ‖Gsum μ Lab A.H y0 G S‖ ≤
      CPE d L Kc κH κ0 κ' * (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) *
        Real.exp (-κ' * dExt S) := by
  have hκH : 0 ≤ κH := by linarith [aEnt_nonneg d L, one_le_c1 d L]
  have hone : ∀ i, _ := fun i => marked_cubes_explicit μ hN hj hΩ A (y0 i) (G i) (hGm i)
    (hGdep i) (hG i) hκ0 hKc hεpos (hF0 i) hκ' hκG hκ hε
  have hne : ∫ Φ, Complex.exp (∑ y, A.H y Φ) ∂(Measure.pi μ) ≠ 0 := (hone hι.some).1
  have hAb : ∀ y Φ, ‖A.H y Φ‖ ≤ εH := fun y Φ => (A.bound y Φ).trans (by
    have : Real.exp (-κH * Lab.dl y) ≤ 1 := Real.exp_le_one_iff.2 (by
      nlinarith [Lab.dl_nonneg y, hκH])
    nlinarith)
  have hGF : ∀ i Φ, ‖G i Φ‖ ≤ F0 i := fun i Φ => (hG i Φ).trans (by
    have hκG0 : 0 ≤ κG := by linarith
    have : Real.exp (-κG * Lab.dl (y0 i)) ≤ 1 := Real.exp_le_one_iff.2 (by
      nlinarith [Lab.dl_nonneg (y0 i), hκG0])
    nlinarith [hF0 i])
  refine ⟨hne, ?_, fun S => ?_⟩
  · rw [avgPi_sum μ A.meas hAb G hGm F0 hGF]
    unfold Gsum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (hone i).2.2.1
  · unfold Gsum
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖Gst μ Lab A.H (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i) S‖
        ≤ ∑ i, CPE d L Kc κH κ0 κ' * F0 i * Real.exp (-κ0 * Lab.dl (y0 i)) *
            Real.exp (-κ' * dExt S) := Finset.sum_le_sum fun i _ => (hone i).2.2.2.2 S
      _ = _ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

end Marks


section Integral

variable {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

open Classical in
/-- **The interpolation integral of a sum of marks** (§3.5 (a)): for a family `u ↦ (A u, Gᵢ u)`
holomorphic on an open set `𝒰 ⊃ [0,1]`,
`∫₀¹ ⟨∑ᵢ Gᵢ(s)⟩_s ds = ∑_S E(S)`, `E(S) = ∫₀¹ ∑ᵢ G*(Y₀ᵢ,S)(s) ds`, with
`|E(S)| ≤ C_PE (∑ᵢ F₀ᵢ e^{-κ₀ 𝗱(Y₀ᵢ)}) e^{-κ' d_Ω(S)}`; each `u ↦ ∑ᵢ G*(Y₀ᵢ,S)(u)` is holomorphic
on `𝒰`. -/
theorem avg_integral_expansion {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
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
    (∀ S : Finset 𝔅, DifferentiableOn ℂ
      (fun u => Gsum μ Lab (A u).H y0 (fun i => G i u) S) 𝒰) ∧
    (∫ s in (0 : ℝ)..1, avgPi μ (A (s : ℂ)).H (fun Φ => ∑ i, G i (s : ℂ) Φ)) =
      ∑ S : Finset 𝔅, ∫ s in (0 : ℝ)..1, Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) S ∧
    ∀ S : Finset 𝔅, ‖∫ s in (0 : ℝ)..1, Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) S‖ ≤
      CPE d L Kc κH κ0 κ' * (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) *
        Real.exp (-κ' * dExt S) := by
  have hhol : ∀ S : Finset 𝔅, DifferentiableOn ℂ
      (fun u => Gsum μ Lab (A u).H y0 (fun i => G i u) S) 𝒰 := fun S => by
    unfold Gsum
    exact DifferentiableOn.fun_sum fun i _ =>
      (Pst_Gst_differentiableOn μ hN hj hΩ h𝒰 A (y0 i) (fun u => G i u) (hGm i)
        (hG i) hAhol (hGhol i) hκ0 hKc hεpos (hF0 i) hκ' hκG hκ hε S).2
  have hint : ∀ S : Finset 𝔅, IntervalIntegrable
      (fun s : ℝ => Gsum μ Lab (A (s : ℂ)).H y0 (fun i => G i (s : ℂ)) S)
      MeasureTheory.volume 0 1 := fun S => by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact (hhol S).continuousOn.comp Complex.continuous_ofReal.continuousOn
      (fun s hs => hseg s hs)
  have hpt := fun u => avg_marks_expansion μ hN hj hΩ (A u) y0 (fun i => G i u)
    (fun i => hGm i u) (fun i => hGdep i u) (fun i => hG i u) hκ0 hKc hεpos hι hF0 hκ' hκG hκ hε
  refine ⟨hhol, ?_, fun S => ?_⟩
  · rw [← intervalIntegral.integral_finsetSum fun S _ => hint S]
    exact intervalIntegral.integral_congr fun s _ => (hpt (s : ℂ)).2.1
  · refine (intervalIntegral.norm_integral_le_of_norm_le_const (C :=
      CPE d L Kc κH κ0 κ' * (∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) *
        Real.exp (-κ' * dExt S)) fun s _ => (hpt (s : ℂ)).2.2 S).trans ?_
    simp

end Integral

end Balaban.Fluctuation
