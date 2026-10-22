/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Schwarz lemma on the ball of a gauge

Let `N` be a nonnegative absolutely homogeneous function on a complex normed space `E`
(`N (c • g) = ‖c‖ N g`: the norm of `E`, or the `ℓ¹` sum of the components of a source on a finite
set of sites), and `F` complex differentiable on the gauge ball `{g : N g < r}`.  If the oscillation
`‖F g - F 0‖` is at most `S` on the ball, then `‖F g - F 0‖ ≤ S N(g) / r` there: the Schwarz lemma
on the complex line `c ↦ F (c • g)`, `|c| < r / N(g)` (Liouville when `N g = 0`).

* `norm_sub_le_mul_gauge`: the core, with the oscillation bound `S`;
* `norm_sub_le_mul_gauge_of_bound`: for `‖F‖ ≤ B` on the ball, `‖F g - F 0‖ ≤ 2 B N(g) / r`;
* `norm_le_mul_gauge_of_vanish`: for `F 0 = 0` and `‖F‖ ≤ M` on the ball, `‖F g‖ ≤ M N(g) / r`;
* `norm_sub_sub_le_of_gauge`, `norm_sub_sub_le_of_norm_sub_le`: **the radial Schwarz difference
  lemma** for two families `F₁ F₂ : E × W → ℂ` over an arbitrary parameter set `W`, differentiable in
  the source on the ball of radius `r₂` for every parameter, whose difference is at most `S(w)`:
  for `N g ≤ r₁ < r₂`, `‖(F₁ - F₂)(g, w) - (F₁ - F₂)(0, w)‖ ≤ 2 S(w) r₁ / r₂` (the gauge and the
  norm versions; one family is the case `F₂ = 0`).  A coupling `F_i(g, w) = G_i(σ g, w)` with `G_i`
  differentiable on the radius `ρ` is the instance `r₂ = ρ / σ`.
-/

@[expose] public section

open Metric Set

namespace Balaban.Analysis

section Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : E → ℝ}

/-- **The Schwarz lemma on the ball of a gauge**: for `N ≥ 0` absolutely homogeneous and `F`
differentiable on `{g : N g < r}` with `‖F g - F 0‖ ≤ S` there, `‖F g - F 0‖ ≤ S N(g) / r`. -/
theorem norm_sub_le_mul_gauge (hN0 : ∀ g, 0 ≤ N g) (hN : ∀ (c : ℂ) (g : E), N (c • g) = ‖c‖ * N g)
    {F : E → ℂ} {r S : ℝ} (hF : DifferentiableOn ℂ F {g | N g < r})
    (hS : ∀ g, N g < r → ‖F g - F 0‖ ≤ S) {g : E} (hg : N g < r) :
    ‖F g - F 0‖ ≤ S * N g / r := by
  have hr : 0 < r := lt_of_le_of_lt (hN0 g) hg
  have hline : ∀ c : ℂ, ‖c‖ * N g < r → N (c • g) < r := fun c hc => by rwa [hN]
  -- the line through `g`
  set φ : ℂ → ℂ := fun c => F (c • g) with hφ
  have hφ0 : φ 0 = F 0 := by simp [hφ]
  have hφ1 : φ 1 = F g := by simp [hφ]
  have hdφ : ∀ c : ℂ, ‖c‖ * N g < r → DifferentiableAt ℂ φ c := fun c hc => by
    have hA : DifferentiableWithinAt ℂ F {g | N g < r} (c • g) := hF _ (hline c hc)
    have hL : DifferentiableAt ℂ (fun c : ℂ => c • g) c := (differentiableAt_id.smul_const g)
    have hopen : {c : ℂ | ‖c‖ * N g < r} ∈ nhds c :=
      (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds hc
    have hw := hA.comp (s := {c : ℂ | ‖c‖ * N g < r}) c hL.differentiableWithinAt
      (fun c' hc' => hline c' hc')
    exact (hw.differentiableAt hopen)
  rcases eq_or_lt_of_le (hN0 g) with h0 | hpos
  · -- `N g = 0`: the line is entire and bounded, hence constant (Liouville)
    have hent : Differentiable ℂ φ := fun c => hdφ c (by rw [← h0, mul_zero]; exact hr)
    have hbd : Bornology.IsBounded (range φ) := by
      refine (isBounded_iff_forall_norm_le).2 ⟨S + ‖F 0‖, ?_⟩
      rintro _ ⟨c, rfl⟩
      have h1 := hS (c • g) (hline c (by rw [← h0, mul_zero]; exact hr))
      calc ‖φ c‖ = ‖(F (c • g) - F 0) + F 0‖ := by simp [hφ]
        _ ≤ ‖F (c • g) - F 0‖ + ‖F 0‖ := norm_add_le _ _
        _ ≤ S + ‖F 0‖ := by linarith
    have heq := hent.apply_eq_apply_of_bounded hbd 1 0
    rw [hφ1, hφ0] at heq
    rw [heq, sub_self, norm_zero, ← h0, mul_zero, zero_div]
  · -- `N g > 0`: the Schwarz lemma on the disc of radius `r / N g > 1`
    set R : ℝ := r / N g with hR
    have hRpos : 0 < R := div_pos hr hpos
    have hball : ∀ c ∈ ball (0 : ℂ) R, ‖c‖ * N g < r := fun c hc => by
      have hc' : ‖c‖ < R := by simpa using hc
      calc ‖c‖ * N g < R * N g := mul_lt_mul_of_pos_right hc' hpos
        _ = r := by rw [hR]; exact div_mul_cancel₀ r hpos.ne'
    have hd : DifferentiableOn ℂ φ (ball 0 R) := fun c hc =>
      (hdφ c (hball c hc)).differentiableWithinAt
    have hmaps : MapsTo φ (ball 0 R) (closedBall (φ 0) S) := fun c hc => by
      rw [mem_closedBall, dist_eq_norm, hφ0]
      exact hS _ (hline c (hball c hc))
    have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
      have : 1 < R := by rw [hR, lt_div_iff₀ hpos]; linarith
      simpa using this
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps h1
    rw [dist_eq_norm, dist_eq_norm, hφ1, hφ0, sub_zero, norm_one, mul_one] at this
    calc ‖F g - F 0‖ ≤ S / R := this
      _ = S * N g / r := by rw [hR, div_div_eq_mul_div]

/-- **The increment on the ball of a gauge** from a bound of the function: for `‖F‖ ≤ B` on
`{g : N g < r}`, `‖F g - F 0‖ ≤ 2 B N(g) / r`. -/
theorem norm_sub_le_mul_gauge_of_bound (hN0 : ∀ g, 0 ≤ N g)
    (hN : ∀ (c : ℂ) (g : E), N (c • g) = ‖c‖ * N g) {F : E → ℂ} {r B : ℝ}
    (hF : DifferentiableOn ℂ F {g | N g < r}) (hB : ∀ g, N g < r → ‖F g‖ ≤ B) {g : E}
    (hg : N g < r) : ‖F g - F 0‖ ≤ 2 * B * N g / r := by
  have hr : 0 < r := lt_of_le_of_lt (hN0 g) hg
  have hN00 : N 0 = 0 := by simpa using hN 0 0
  have hB0 := hB 0 (by rw [hN00]; exact hr)
  refine norm_sub_le_mul_gauge hN0 hN hF (fun g' hg' => ?_) hg
  calc ‖F g' - F 0‖ ≤ ‖F g'‖ + ‖F 0‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hB g' hg') hB0
    _ = 2 * B := by ring

/-- **The Schwarz lemma for a function vanishing at the origin**: for `F 0 = 0` and `‖F‖ ≤ M` on
`{g : N g < r}`, `‖F g‖ ≤ M N(g) / r`. -/
theorem norm_le_mul_gauge_of_vanish (hN0 : ∀ g, 0 ≤ N g)
    (hN : ∀ (c : ℂ) (g : E), N (c • g) = ‖c‖ * N g) {F : E → ℂ} {r M : ℝ}
    (hF : DifferentiableOn ℂ F {g | N g < r}) (hF0 : F 0 = 0) (hM : ∀ g, N g < r → ‖F g‖ ≤ M)
    {g : E} (hg : N g < r) : ‖F g‖ ≤ M * N g / r := by
  have h := norm_sub_le_mul_gauge hN0 hN hF (fun g' hg' => by rw [hF0, sub_zero]; exact hM g' hg')
    hg
  rwa [hF0, sub_zero] at h

/-- **The radial Schwarz difference lemma** (gauge form): for two families `F₁ F₂ : E × W → ℂ`,
differentiable in the source on `{g : N g < r₂}` at the parameter `w`, with
`‖F₁(g, w) - F₂(g, w)‖ ≤ S(w)` there, and `N g ≤ r₁ < r₂`,
`‖(F₁ - F₂)(g, w) - (F₁ - F₂)(0, w)‖ ≤ 2 S(w) r₁ / r₂`. -/
theorem norm_sub_sub_le_of_gauge {W : Type*} (hN0 : ∀ g, 0 ≤ N g)
    (hN : ∀ (c : ℂ) (g : E), N (c • g) = ‖c‖ * N g) {F₁ F₂ : E × W → ℂ} {r₁ r₂ : ℝ}
    {S : W → ℝ} (w : W) (hF₁ : DifferentiableOn ℂ (fun g => F₁ (g, w)) {g | N g < r₂})
    (hF₂ : DifferentiableOn ℂ (fun g => F₂ (g, w)) {g | N g < r₂})
    (hS : ∀ g, N g < r₂ → ‖F₁ (g, w) - F₂ (g, w)‖ ≤ S w) {g : E} (hg : N g ≤ r₁)
    (hr : r₁ < r₂) :
    ‖(F₁ (g, w) - F₂ (g, w)) - (F₁ (0, w) - F₂ (0, w))‖ ≤ 2 * S w * r₁ / r₂ := by
  have hg2 : N g < r₂ := lt_of_le_of_lt hg hr
  have hr₂ : 0 < r₂ := lt_of_le_of_lt (hN0 g) hg2
  have hN00 : N 0 = 0 := by simpa using hN 0 0
  have hS0 : 0 ≤ S w := (norm_nonneg _).trans (hS 0 (by rw [hN00]; exact hr₂))
  have h := norm_sub_le_mul_gauge_of_bound (F := fun g => F₁ (g, w) - F₂ (g, w)) hN0 hN
    (hF₁.sub hF₂) hS hg2
  refine h.trans ?_
  rw [div_le_div_iff_of_pos_right hr₂]
  exact mul_le_mul_of_nonneg_left hg (mul_nonneg (by norm_num) hS0)

/-- **The radial Schwarz difference lemma** (norm form, the gauge `N = ‖·‖`): for two families
`F₁ F₂ : E × W → ℂ` differentiable in the source on the ball of radius `r₂` at the parameter `w`,
with `‖F₁(g, w) - F₂(g, w)‖ ≤ S(w)` there, and `‖g‖ ≤ r₁ < r₂`,
`‖(F₁ - F₂)(g, w) - (F₁ - F₂)(0, w)‖ ≤ 2 S(w) r₁ / r₂`. -/
theorem norm_sub_sub_le_of_norm_sub_le {W : Type*} {F₁ F₂ : E × W → ℂ} {r₁ r₂ : ℝ}
    {S : W → ℝ} (w : W) (hF₁ : DifferentiableOn ℂ (fun g => F₁ (g, w)) (ball (0 : E) r₂))
    (hF₂ : DifferentiableOn ℂ (fun g => F₂ (g, w)) (ball (0 : E) r₂))
    (hS : ∀ g ∈ ball (0 : E) r₂, ‖F₁ (g, w) - F₂ (g, w)‖ ≤ S w) {g : E} (hg : ‖g‖ ≤ r₁)
    (hr : r₁ < r₂) :
    ‖(F₁ (g, w) - F₂ (g, w)) - (F₁ (0, w) - F₂ (0, w))‖ ≤ 2 * S w * r₁ / r₂ := by
  have hb : ball (0 : E) r₂ = {g | ‖g‖ < r₂} := by ext g; simp
  rw [hb] at hF₁ hF₂
  exact norm_sub_sub_le_of_gauge (N := fun g => ‖g‖) (fun g => norm_nonneg g)
    (fun c g => norm_smul c g) w hF₁ hF₂ (fun g hg => hS g (by simpa using hg)) hg hr

end Gauge

end Balaban.Analysis
