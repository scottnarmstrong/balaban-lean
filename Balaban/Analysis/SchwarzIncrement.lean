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

If `F` is analytic on the `ℓ¹` ball `{g : ∑ |g_{x,i}| < G}` of sources and bounded there by `B`,
then `|F(g) - F(0)| ≤ 2B ‖g‖₁/G` on that ball (`norm_sub_le_mul_l1_of_l1Ball`): the Schwarz lemma on
the complex line `λ ↦ F(λ g)`, `|λ| < G/‖g‖₁`. For `G > 1` and the unit ball this gives
`|F(g) - F(0)| ≤ 2B/G` (`norm_sub_le_of_l1Ball`).
-/

@[expose] public section

open Metric Set

namespace Balaban.Analysis

/-- **The increment on an `ℓ¹` ball** (the Schwarz lemma on the complex line `λ ↦ F(λ g)`): if `F` is
analytic on the `ℓ¹` ball `{g : ∑ |g_{x,i}| < G}` and bounded there by `B`, then
`|F(g) - F(0)| ≤ 2B ‖g‖₁ / G` on that ball. -/
theorem norm_sub_le_mul_l1_of_l1Ball {ι J : Type*} [Fintype ι] [Fintype J] {F : (ι → J → ℂ) → ℂ}
    {G B : ℝ}
    (hF : AnalyticOnNhd ℂ F {g | ∑ x, ∑ i, ‖g x i‖ < G})
    (hFB : ∀ g : ι → J → ℂ, ∑ x, ∑ i, ‖g x i‖ < G → ‖F g‖ ≤ B)
    {g : ι → J → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < G) :
    ‖F g - F 0‖ ≤ 2 * B * (∑ x, ∑ i, ‖g x i‖) / G := by
  set n := ∑ x, ∑ i, ‖g x i‖ with hn
  have hn0 : 0 ≤ n := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hG : 0 < G := lt_of_le_of_lt hn0 hg
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hFB 0 (by simp; linarith))
  rcases eq_or_lt_of_le hn0 with h0 | hpos
  · have hg0 : g = 0 := by
      funext x i
      have h1 : ∀ x ∈ Finset.univ, ∑ i, ‖g x i‖ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          norm_nonneg _).1 h0.symm
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => norm_nonneg _).1
        (h1 x (Finset.mem_univ x)) i (Finset.mem_univ i)
      simpa using h2
    rw [hg0, sub_self, norm_zero]
    positivity
  set R := G / n with hR
  have hRpos : 0 < R := div_pos hG hpos
  have hline : ∀ c : ℂ, ‖c‖ < R → ∑ x, ∑ i, ‖(c • g) x i‖ < G := by
    intro c hc
    have : ∑ x, ∑ i, ‖(c • g) x i‖ = ‖c‖ * n := by
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hn, Finset.mul_sum]
    rw [this]
    calc ‖c‖ * n < R * n := mul_lt_mul_of_pos_right hc hpos
      _ = G := by rw [hR]; field_simp
  set φ : ℂ → ℂ := fun c => F (c • g) with hφ
  have hd : DifferentiableOn ℂ φ (ball 0 R) := by
    intro c hc
    have hc' : ‖c‖ < R := by simpa using hc
    have hA : AnalyticAt ℂ F (c • g) := hF _ (hline c hc')
    have hL : AnalyticAt ℂ (fun c : ℂ => c • g) c :=
      (analyticAt_id.smul analyticAt_const)
    exact (AnalyticAt.comp (f := fun c : ℂ => c • g) hA hL).differentiableAt
      |>.differentiableWithinAt
  have hmaps : MapsTo φ (ball 0 R) (closedBall (φ 0) (2 * B)) := by
    intro c hc
    have hc' : ‖c‖ < R := by simpa using hc
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hFB _ (hline c hc')
    have h2 := hFB _ (hline 0 (by simp; exact hRpos))
    calc ‖φ c - φ 0‖ ≤ ‖φ c‖ + ‖φ 0‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add h1 h2
      _ = 2 * B := by ring
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    have : 1 < R := by rw [hR, lt_div_iff₀ hpos]; linarith
    simpa using this
  have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1
  simp only [hφ, one_smul, zero_smul, dist_zero_right, norm_one, mul_one] at this
  rw [dist_eq_norm] at this
  calc ‖F g - F 0‖ ≤ 2 * B / R := this
    _ = 2 * B * n / G := by rw [hR]; field_simp

/-- **The increment on the unit `ℓ¹` ball** (the case `‖g‖₁ < 1` of
`norm_sub_le_mul_l1_of_l1Ball`). -/
theorem norm_sub_le_of_l1Ball {ι J : Type*} [Fintype ι] [Fintype J] {F : (ι → J → ℂ) → ℂ}
    {G B : ℝ} (hG : 1 < G)
    (hF : AnalyticOnNhd ℂ F {g | ∑ x, ∑ i, ‖g x i‖ < G})
    (hFB : ∀ g : ι → J → ℂ, ∑ x, ∑ i, ‖g x i‖ < G → ‖F g‖ ≤ B)
    {g : ι → J → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < 1) :
    ‖F g - F 0‖ ≤ 2 * B / G := by
  have hn0 : 0 ≤ ∑ x, ∑ i, ‖g x i‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hFB 0 (by simp; linarith))
  refine (norm_sub_le_mul_l1_of_l1Ball hF hFB (hg.trans hG)).trans ?_
  have hG0 : 0 < G := by linarith
  rw [div_le_div_iff_of_pos_right hG0]
  nlinarith

end Balaban.Analysis
