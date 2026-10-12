/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31bSchwarz
public import Balaban.Fluctuation.Thm31Avg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): the first-order marks, integrated over `t`, with the gain `1 / R_σ`

For a mark `G = ψ̂(y)` of mean zero and a family of label activities `A t σ`, holomorphic in `t` on
an open set containing `[0,1]` (at `σ = 1`) and in `σ` on the disc of radius `R_σ > 1` (for real
`t ∈ [0,1]`), vanishing at `σ = 0`:
`∫₀¹ ⟨G⟩_{t,σ=1} dt = ∑_S E(S)`, `E(S) = ∫₀¹ G*(Y₀,S)(t,1) dt`, `|E(S)| ≤ C_PE F₀ e^{-κ₀𝗱(Y₀)}
e^{-κ' d_Ω(S)} / R_σ`, and `E(S) = 0` unless `S ⊇ Y₀ ∩ Ω`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section First

variable {Lb : Type*} [Fintype Lb]

/-- **The `t`-integrated local term** `E(S) = ∫₀¹ G*(Y₀,S)(t, σ = 1) dt`. -/
noncomputable def markIntTerm {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] {Lab : CubeLabels m₀ j Ω Lb}
    {εH κH κ0 Kc : ℝ} (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb)
    (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅) : ℂ :=
  ∫ s in (0 : ℝ)..1, Gst μ Lab (A (s : ℂ) 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S

omit [NeZero N₁] [NeZero L] in
theorem intervalIntegral_sum_aux {α : Type*} [Fintype α] (f : α → ℝ → ℂ) (g : ℝ → ℂ)
    (hint : ∀ a, IntervalIntegrable (f a) MeasureTheory.volume 0 1)
    (hpt : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → g s = ∑ a, f a s) :
    IntervalIntegrable g MeasureTheory.volume 0 1 ∧
      (∫ s in (0 : ℝ)..1, g s) = ∑ a, ∫ s in (0 : ℝ)..1, f a s := by
  have hsum : IntervalIntegrable (fun s => ∑ a, f a s) MeasureTheory.volume 0 1 := by
    have := IntervalIntegrable.sum (Finset.univ) (fun a _ => hint a)
    convert this using 1
    ext s
    simp [Finset.sum_apply]
  refine ⟨hsum.congr ?_, ?_⟩
  · intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    exact (hpt s ⟨hs.1.le, hs.2⟩).symm
  · rw [intervalIntegral.integral_congr (g := fun s => ∑ a, f a s) (fun s hs => by
      rw [Set.uIcc_of_le zero_le_one] at hs; exact hpt s hs)]
    exact intervalIntegral.integral_finsetSum fun a _ => hint a

open Classical

variable {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 R : ℝ}
    {𝒰 : Set ℂ} (h𝒰 : IsOpen 𝒰) (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰)
    (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (holt : ∀ y Φ, DifferentiableOn ℂ (fun t => (A t 1).H y Φ) 𝒰)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))

include h𝒰 hseg holt hGm hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε hN hj hΩ in
theorem markInt_integrable (S : Finset 𝔅) : IntervalIntegrable
    (fun s : ℝ => Gst μ Lab (A (s : ℂ) 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S)
    MeasureTheory.volume 0 1 := by
  have hhol : DifferentiableOn ℂ
      (fun u => Gst μ Lab (A u 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S) 𝒰 :=
    (Pst_Gst_differentiableOn μ hN hj hΩ h𝒰 (fun u => A u 1) y0 (fun _ => G) (fun _ => hGm)
      (fun _ => hG) holt (fun Φ => differentiableOn_const _) hκ0 hKc hεpos hF0 hκ' hκG hκ hε S).2
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le zero_le_one]
  exact hhol.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun s hs => hseg s hs)

include hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε hN hj hΩ in
theorem markInt_pointwise (s : ℝ) :
    avgPi μ (A (s : ℂ) 1).H G =
      ∑ S : Finset 𝔅, Gst μ Lab (A (s : ℂ) 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S :=
  (marked_cubes_explicit μ hN hj hΩ (A (s : ℂ) 1) y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG
    hκ hε).2.2.1

include hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε hN hj hΩ in
theorem markInt_support (s : ℝ) (S : Finset 𝔅)
    (hS : ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S) :
    Gst μ Lab (A (s : ℂ) 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S = 0 :=
  (marked_cubes_explicit μ hN hj hΩ (A (s : ℂ) 1) y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG
    hκ hε).2.2.2.1 S hS

include hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε hN hj hΩ in
theorem markInt_bound (hR : 1 < R)
    (holσ : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ,
      DifferentiableOn ℂ (fun σ => (A (s : ℂ) σ).H y Φ) (ball (0 : ℂ) R))
    (hzero : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y Φ, (A (s : ℂ) 0).H y Φ = 0)
    (hmean : ∫ Φ, G Φ ∂(Measure.pi μ) = 0) (S : Finset 𝔅) :
    ‖markIntTerm μ A y0 G S‖ ≤
      CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S) / R := by
  have hbd : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖Gst μ Lab (A (s : ℂ) 1).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S‖ ≤
        CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S) / R := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have := Gst_schwarz μ hN hj hΩ (A := A (s : ℂ)) y0 G hGm hGdep hG (holσ s hs')
      (hzero s hs') hmean hκ0 hKc hεpos hF0 hκ' hκG hκ hε S (σ := 1) (by simpa using hR)
    simpa only [norm_one, mul_one_div] using this
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hbd).trans ?_
  simp

include hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε hN hj hΩ in
theorem markIntTerm_support (S : Finset 𝔅) (hS : ¬ blocksOf m₀ j Ω (Lab.ysite y0) ⊆ S) :
    markIntTerm μ A y0 G S = 0 := by
  unfold markIntTerm
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℂ)) (fun s _ =>
    markInt_support μ hN hj hΩ A y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε s S hS)]
  simp

include h𝒰 hseg holt hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε hN hj hΩ in
/-- **Theorem 3.1 (b), first-order marks, expansion**: `∫₀¹ ⟨G⟩_{t,σ=1} dt = ∑_S E(S)`. -/
theorem markInt_expansion :
    IntervalIntegrable (fun s : ℝ => avgPi μ (A (s : ℂ) 1).H G) MeasureTheory.volume 0 1 ∧
    (∫ s in (0 : ℝ)..1, avgPi μ (A (s : ℂ) 1).H G) =
      ∑ S : Finset 𝔅, markIntTerm μ A y0 G S := by
  have hint := markInt_integrable μ hN hj hΩ h𝒰 hseg A y0 G hGm hG holt hκ0 hKc hεpos hF0
    hκ' hκG hκ hε
  have hpt := markInt_pointwise μ hN hj hΩ A y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε
  exact intervalIntegral_sum_aux (fun S s => Gst μ Lab (A (s : ℂ) 1).H
    (blocksOf m₀ j Ω (Lab.ysite y0)) G S) (fun s => avgPi μ (A (s : ℂ) 1).H G) hint
    (fun s _ => hpt s)

end First

end Balaban.Fluctuation
