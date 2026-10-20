/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Increments of analytic functions on an `ℓ¹` ball (Schwarz)

If `F` is analytic on the `ℓ¹` ball `{g : ∑ |g_{x,i}| < G}` of sources, `G > 1`, and bounded there
by `B`, then on the unit `ℓ¹` ball `|F(g) - F(0)| ≤ 2B/G` (`norm_sub_le_of_l1Ball`): the Schwarz
lemma on the complex line `λ ↦ F(λ g)`, `|λ| < G`.
-/

@[expose] public section

open Metric Set

namespace Balaban.Analysis

/-- **The increment on the unit `ℓ¹` ball.** -/
theorem norm_sub_le_of_l1Ball {ι J : Type*} [Fintype ι] [Fintype J] {F : (ι → J → ℂ) → ℂ}
    {G B : ℝ} (hG : 1 < G)
    (hF : AnalyticOnNhd ℂ F {g | ∑ x, ∑ i, ‖g x i‖ < G})
    (hFB : ∀ g : ι → J → ℂ, ∑ x, ∑ i, ‖g x i‖ < G → ‖F g‖ ≤ B)
    {g : ι → J → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < 1) :
    ‖F g - F 0‖ ≤ 2 * B / G := by
  set n := ∑ x, ∑ i, ‖g x i‖ with hn
  have hn0 : 0 ≤ n := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hline : ∀ c : ℂ, ‖c‖ < G → ∑ x, ∑ i, ‖(c • g) x i‖ < G := by
    intro c hc
    have : ∑ x, ∑ i, ‖(c • g) x i‖ = ‖c‖ * n := by
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hn, Finset.mul_sum]
    rw [this]
    calc ‖c‖ * n ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left hg.le (norm_nonneg _)
      _ < G := by rw [mul_one]; exact hc
  set φ : ℂ → ℂ := fun c => F (c • g) with hφ
  have hd : DifferentiableOn ℂ φ (ball 0 G) := by
    intro c hc
    have hc' : ‖c‖ < G := by simpa using hc
    have hA : AnalyticAt ℂ F (c • g) := hF _ (hline c hc')
    have hL : AnalyticAt ℂ (fun c : ℂ => c • g) c :=
      (analyticAt_id.smul analyticAt_const)
    exact (AnalyticAt.comp (f := fun c : ℂ => c • g) hA hL).differentiableAt
      |>.differentiableWithinAt
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hFB 0 (by simp; linarith))
  have hmaps : MapsTo φ (ball 0 G) (closedBall (φ 0) (2 * B)) := by
    intro c hc
    have hc' : ‖c‖ < G := by simpa using hc
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hFB _ (hline c hc')
    have h2 := hFB _ (hline 0 (by simp; linarith))
    calc ‖φ c - φ 0‖ ≤ ‖φ c‖ + ‖φ 0‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add h1 h2
      _ = 2 * B := by ring
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) G := by simpa using hG
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1
  simp only [hφ, one_smul, zero_smul, dist_zero_right, norm_one, mul_one] at this
  rw [dist_eq_norm] at this
  exact this

end Balaban.Analysis
