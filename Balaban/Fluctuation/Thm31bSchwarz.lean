/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31bVanish
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (b): the Schwarz lemma in `σ` (FLUCTUATION.md §3.5 (b))

"By the Schwarz lemma in `σ` (P6 (4.63)): `|G*(y,S)|_{σ=1} ≤ R_σ^{-1} C_PE p₁ e^{-κ_a d_Ω(S)}`."
For a family of label activities `A σ`, holomorphic in `σ` on the disc `|σ| < R_σ`, vanishing at
`σ = 0`, and a mean-zero mark, every local term `G*(Y₀, S)` is bounded by the bound of Theorem 3.4
times `|σ| / R_σ`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

section Schwarz

variable {Lb : Type*} [Fintype Lb]

open Classical in
/-- **Theorem 3.1 (b), the `σ`-Schwarz step.**  For `A : ℂ → LabelAct …` holomorphic in `σ` on
the disc of radius `R`, vanishing at `σ = 0`, and a mean-zero mark `G`, for `|σ| < R`:
`|G*(Y₀, S)(σ)| ≤ C_PE F₀ e^{-κ₀ 𝗱(Y₀)} e^{-κ' d_Ω(S)} · |σ| / R`. -/
theorem Gst_schwarz {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (hΩ : IsPiUnion m₀ j Ω)
    {Lab : CubeLabels m₀ j Ω Lb} {εH κH κG κ0 κ' Kc F0 R : ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ)
    (hGm : Measurable G) (hGdep : DepOn (blocksOf m₀ j Ω (Lab.ysite y0)) G)
    (hG : ∀ Φ, ‖G Φ‖ ≤ F0 * Real.exp (-κG * Lab.dl y0))
    (hAhol : ∀ y Φ, DifferentiableOn ℂ (fun σ => (A σ).H y Φ) (ball (0 : ℂ) R))
    (hA0 : ∀ y Φ, (A 0).H y Φ = 0) (hmean : ∫ Φ, G Φ ∂(Measure.pi μ) = 0)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH) (hF0 : 0 < F0)
    (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (S : Finset 𝔅) {σ : ℂ} (hσ : ‖σ‖ < R) :
    ‖Gst μ Lab (A σ).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S‖ ≤
      CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S) *
        (‖σ‖ / R) := by
  set M := CPE d L Kc κH κ0 κ' * F0 * Real.exp (-κ0 * Lab.dl y0) * Real.exp (-κ' * dExt S)
    with hM
  have hdiff := (Pst_Gst_differentiableOn μ hN hj hΩ (isOpen_ball (x := (0 : ℂ)) (ε := R)) A y0
    (fun _ => G) (fun _ => hGm) (fun _ => hG) hAhol (fun Φ => differentiableOn_const _) hκ0 hKc
    hεpos hF0 hκ' hκG hκ hε S).2
  have hbd : ∀ u, ‖Gst μ Lab (A u).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S‖ ≤ M := fun u =>
    (marked_cubes_explicit μ hN hj hΩ (A u) y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG hκ hε).2.2.2.2 S
  have h0 : Gst μ Lab (A 0).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S = 0 :=
    Gst_eq_zero_of_zero_interaction μ hN hj hΩ (A 0) y0 G hGm hGdep hG hκ0 hKc hεpos hF0 hκ' hκG
      hκ hε (hA0) hmean S
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball (c := (0 : ℂ)) (R₁ := R) (R₂ := M)
    (f := fun u => Gst μ Lab (A u).H (blocksOf m₀ j Ω (Lab.ysite y0)) G S) hdiff
    (fun u _ => by simpa [h0] using hbd u) (mem_ball_zero_iff.2 hσ)
  simpa [h0, dist_eq_norm, div_mul_eq_mul_div, mul_div_assoc] using this

end Schwarz

end Balaban.Fluctuation
