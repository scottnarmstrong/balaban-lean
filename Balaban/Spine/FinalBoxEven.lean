/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Even analytic functions vanishing at the origin are of second order

A6-3, gas layer, the parity argument for the increments of the last-scale activities. An analytic
function `f` on the disc `|t| < R` that is even and vanishes at `0` has `f'(0) = 0`, so
`f(t) - f(0) = o(|t|)` and the Schwarz lemma of order two gives `|f(1)| ≤ S / R²` when `|f| ≤ S` on
the disc (`norm_le_div_sq_of_even`). `norm_le_div_sq_of_even_param` is the form for a function of the
dilation and a parameter.
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.RootFSpine

/-- The derivative at `0` of a function even near `0` vanishes. -/
theorem deriv_eq_zero_of_even {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (heven : ∀ t ∈ ball (0 : ℂ) R, f (-t) = f t) : deriv f 0 = 0 := by
  have heq : (fun t => f (-t)) =ᶠ[𝓝 0] f :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hR)) fun t ht => heven t ht
  have h1 : deriv (fun t => f (-t)) 0 = deriv f 0 := heq.deriv_eq
  rw [deriv_comp_neg, neg_zero] at h1
  linear_combination (-1 / 2 : ℂ) * h1

/-- **Even analytic functions vanishing at `0` are of second order**: if `f` is differentiable on
`|t| < R`, `R > 1`, even, `f(0) = 0` and `|f| ≤ S` on the disc, then `|f(1)| ≤ S / R²`. -/
theorem norm_le_div_sq_of_even {f : ℂ → ℂ} {R S : ℝ} (hR : 1 < R)
    (hd : DifferentiableOn ℂ f (ball 0 R)) (h0 : f 0 = 0)
    (heven : ∀ t ∈ ball (0 : ℂ) R, f (-t) = f t) (hS : ∀ t ∈ ball (0 : ℂ) R, ‖f t‖ ≤ S) :
    ‖f 1‖ ≤ S / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hmem0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR0
  have hD : HasDerivAt f 0 0 := by
    have := ((hd 0 hmem0).differentiableAt (isOpen_ball.mem_nhds hmem0)).hasDerivAt
    rwa [deriv_eq_zero_of_even hR0 heven] at this
  have hmaps : MapsTo f (ball 0 R) (closedBall (f 0) S) := fun t ht => by
    rw [mem_closedBall, dist_eq_norm, h0, sub_zero]; exact hS t ht
  have hn : (fun w => f w - f 0) =o[𝓝 (0 : ℂ)] fun w => ‖w - 0‖ ^ 1 := by
    have h1 := hasDerivAt_iff_isLittleO.1 hD
    simp only [smul_zero, sub_zero] at h1
    simpa [pow_one] using h1.norm_right
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by simpa using hR
  have := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hd hmaps hn h1
  rw [h0, dist_zero_right, dist_zero_right, norm_one] at this
  calc ‖f 1‖ ≤ S * (1 / R) ^ (1 + 1) := this
    _ = S / R ^ 2 := by rw [div_pow, one_pow, mul_one_div]

/-- **The parity bound for a function of the dilation and a parameter**: if `F` is analytic on
`{|t| < R} × U`, even in `t`, vanishes at `t = 0` and is bounded by `S`, then `|F(1, u)| ≤ S / R²`
for `u ∈ U`. -/
theorem norm_le_div_sq_of_even_param {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ × E → ℂ} {R S : ℝ} {U : Set E} (hR : 1 < R)
    (hF : AnalyticOnNhd ℂ F (ball (0 : ℂ) R ×ˢ U)) (h0 : ∀ u ∈ U, F (0, u) = 0)
    (heven : ∀ t ∈ ball (0 : ℂ) R, ∀ u ∈ U, F (-t, u) = F (t, u))
    (hS : ∀ t ∈ ball (0 : ℂ) R, ∀ u ∈ U, ‖F (t, u)‖ ≤ S) {u : E} (hu : u ∈ U) :
    ‖F (1, u)‖ ≤ S / R ^ 2 := by
  have hd : DifferentiableOn ℂ (fun t => F (t, u)) (ball 0 R) := by
    intro t ht
    have hA : AnalyticAt ℂ F (t, u) := hF _ ⟨ht, hu⟩
    have hL : AnalyticAt ℂ (fun t : ℂ => (t, u)) t := analyticAt_id.prod analyticAt_const
    exact (AnalyticAt.comp (f := fun t : ℂ => (t, u)) hA hL).differentiableAt.differentiableWithinAt
  exact norm_le_div_sq_of_even hR hd (h0 u hu) (fun t ht => heven t ht u hu) (fun t ht => hS t ht u hu)

end Balaban.RootFSpine
