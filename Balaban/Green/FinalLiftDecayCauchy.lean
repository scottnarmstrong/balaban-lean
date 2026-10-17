/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A Cauchy estimate along a line (blocker 5, the lipschitz bound of the terms)

If a complex function `f` is analytic on a set containing the discs `x + t v`, `|t| < ρ`, and
bounded by `B` there, then `‖f (x + z v) - f x‖ ≤ (2 B / ρ) |z|` for `|z| < ρ` (Schwarz lemma for
`t ↦ f (x + t v)`).  In particular, `‖f (x + v) - f x‖ ≤ 2 B / ρ` for `ρ > 1`: the variation of `f` in
a direction `v` is at most `2 B ‖v‖ / r` if `f` is analytic and bounded by `B` on the ball of radius
`r` in the direction of `v` (`ρ = r / ‖v‖`).
-/

@[expose] public section

open Metric Set

namespace Balaban.Green

/-- **Schwarz estimate for a disc**: `f` differentiable on the disc of radius `ρ` and bounded by
`B` there satisfies `‖f z - f 0‖ ≤ (2 B / ρ) |z|`. -/
theorem norm_sub_le_of_differentiableOn_ball {f : ℂ → ℂ} {ρ B : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ f (ball 0 ρ)) (hB : ∀ z ∈ ball (0 : ℂ) ρ, ‖f z‖ ≤ B) {z : ℂ}
    (hz : ‖z‖ < ρ) : ‖f z - f 0‖ ≤ 2 * B / ρ * ‖z‖ := by
  have hz' : z ∈ ball (0 : ℂ) ρ := by simpa using hz
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) ρ := mem_ball_self hρ
  have hmaps : MapsTo f (ball 0 ρ) (closedBall (f 0) (2 * B)) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f 0‖ ≤ ‖f w‖ + ‖f 0‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hB w hw) (hB 0 h0)
      _ = 2 * B := by ring
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hz'
  simpa [dist_eq_norm] using this

/-- **Variation along a line from analyticity and a bound**: let `f` be analytic on a set `s` of a
complex normed space and bounded by `B` on `s`, and let `x + t v ∈ s` for `‖t‖ < ρ`.  Then
`‖f (x + z v) - f x‖ ≤ (2 B / ρ) ‖z‖` for `‖z‖ < ρ`. -/
theorem norm_sub_le_of_analytic_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {s : Set E} {B ρ : ℝ} (hρ : 0 < ρ) (hf : AnalyticOnNhd ℂ f s)
    (hB : ∀ y ∈ s, ‖f y‖ ≤ B) {x v : E} (hs : ∀ t : ℂ, ‖t‖ < ρ → x + t • v ∈ s) {z : ℂ}
    (hz : ‖z‖ < ρ) : ‖f (x + z • v) - f x‖ ≤ 2 * B / ρ * ‖z‖ := by
  have hg : DifferentiableOn ℂ (fun t : ℂ => f (x + t • v)) (ball 0 ρ) := by
    intro t ht
    have ht' : ‖t‖ < ρ := by simpa using ht
    have h1 : AnalyticAt ℂ f (x + t • v) := hf _ (hs t ht')
    have h2 : DifferentiableAt ℂ f (x + t • v) := h1.differentiableAt
    have h3 : DifferentiableAt ℂ (fun t : ℂ => x + t • v) t :=
      (differentiableAt_const _).add ((differentiableAt_id).smul_const v)
    exact (h2.comp t h3).differentiableWithinAt
  have := norm_sub_le_of_differentiableOn_ball (f := fun t : ℂ => f (x + t • v)) hρ hg
    (fun t ht => hB _ (hs t (by simpa using ht))) hz
  simpa using this

/-- **Unit step**: if `ρ > 1`, `‖f (x + v) - f x‖ ≤ 2 B / ρ`. -/
theorem norm_sub_le_of_analytic_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {s : Set E} {B ρ : ℝ} (hρ : 1 < ρ) (hf : AnalyticOnNhd ℂ f s)
    (hB : ∀ y ∈ s, ‖f y‖ ≤ B) {x v : E} (hs : ∀ t : ℂ, ‖t‖ < ρ → x + t • v ∈ s) :
    ‖f (x + v) - f x‖ ≤ 2 * B / ρ := by
  have := norm_sub_le_of_analytic_line (z := 1) (by linarith) hf hB hs (by simpa using hρ)
  simpa using this

end Balaban.Green
