/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.AbstractExpansion
import Mathlib.Analysis.Complex.Schwarz

/-!
# A Schwarz-lemma bound for the coefficients of a family vanishing at `t = 0` (W804)

If `G t s` is analytic in `(t, s)` on `{|t| < T} × {|s_i| < R}`, bounded by `B`, and vanishes at
`t = 0` for all `s`, then each `s ↦ G t s` is bounded by `B |t| / T` on the polydisc, so by the
Cauchy bound `norm_coef_le` its coefficients satisfy
`‖coef (G t) C‖ ≤ (B |t| / T) / (R - 1)^{|C|}`.

This is the mechanism by which a perturbation of size `η` (here `t = η/η₀`) produces a factor
`η/η₀` in front of the coefficients of the determinant-ratio logarithm.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis Metric

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

omit [DecidableEq ι] in
/-- Schwarz lemma in the parameter `t`, uniformly in `s`: `‖G t s‖ ≤ B |t| / T`. -/
theorem norm_le_of_vanishing_zero {R T B : ℝ} (G : ℂ → (ι → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ (fun p : ℂ × (ι → ℂ) => G p.1 p.2)
      (ball (0 : ℂ) T ×ˢ polydisc (0 : ι → ℂ) (fun _ => R)))
    (h0 : ∀ s, G 0 s = 0)
    (hB : ∀ t ∈ ball (0 : ℂ) T, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), ‖G t s‖ ≤ B)
    {t : ℂ} (ht : ‖t‖ < T) {s : ι → ℂ} (hs : s ∈ polydisc (0 : ι → ℂ) (fun _ => R)) :
    ‖G t s‖ ≤ B * (‖t‖ / T) := by
  have htb : t ∈ ball (0 : ℂ) T := by simpa using ht
  have hd : DifferentiableOn ℂ (fun τ => G τ s) (ball (0 : ℂ) T) := by
    intro τ hτ
    have hp : AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => G p.1 p.2) (τ, s) := hG (τ, s) ⟨hτ, hs⟩
    have hc : AnalyticAt ℂ (fun τ' : ℂ => (τ', s)) τ :=
      AnalyticAt.prod (analyticAt_id (𝕜 := ℂ)) (analyticAt_const (𝕜 := ℂ))
    exact (AnalyticAt.comp (g := fun p : ℂ × (ι → ℂ) => G p.1 p.2) (f := fun τ' : ℂ => (τ', s)) hp hc).differentiableAt.differentiableWithinAt
  have hm : Set.MapsTo (fun τ => G τ s) (ball (0 : ℂ) T) (closedBall (G 0 s) B) := by
    intro τ hτ
    rw [mem_closedBall, h0, dist_zero_right]
    exact hB τ hτ s hs
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm htb
  rw [h0, dist_zero_right, dist_zero_right] at this
  simpa [div_mul_eq_mul_div, mul_div_assoc] using this

/-- **Schwarz coefficient bound.**  For `G` analytic on `{|t| < T} × polydisc`, bounded by `B`,
with `G 0 = 0`, and `|t| < T`:
`‖coef (G t) C‖ ≤ B (|t|/T) / (R - 1)^{|C|}`. -/
theorem norm_coef_le_of_vanishing_zero {R T B : ℝ} (hR : 1 < R) (G : ℂ → (ι → ℂ) → ℂ)
    (hG : AnalyticOnNhd ℂ (fun p : ℂ × (ι → ℂ) => G p.1 p.2)
      (ball (0 : ℂ) T ×ˢ polydisc (0 : ι → ℂ) (fun _ => R)))
    (h0 : ∀ s, G 0 s = 0)
    (hB : ∀ t ∈ ball (0 : ℂ) T, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => R), ‖G t s‖ ≤ B)
    {t : ℂ} (ht : ‖t‖ < T) (C : Finset ι) :
    ‖coef (G t) C‖ ≤ B * (‖t‖ / T) / (R - 1) ^ C.card := by
  have htb : t ∈ ball (0 : ℂ) T := by simpa using ht
  have hf : AnalyticOnNhd ℂ (G t) (polydisc (0 : ι → ℂ) (fun _ => R)) := by
    intro s hs
    have hp : AnalyticAt ℂ (fun p : ℂ × (ι → ℂ) => G p.1 p.2) (t, s) := hG (t, s) ⟨htb, hs⟩
    have hc : AnalyticAt ℂ (fun s' : ι → ℂ => (t, s')) s :=
      AnalyticAt.prod (analyticAt_const (𝕜 := ℂ)) (analyticAt_id (𝕜 := ℂ))
    exact hp.comp hc
  exact norm_coef_le hR hf (fun s hs => norm_le_of_vanishing_zero G hG h0 hB ht hs) C

end Balaban.Localization
