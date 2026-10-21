/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.Cauchy
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Cauchy bounds for the Taylor remainders of a term at a general centre (A6-3, PHYS-CUBIC route)

`notes/phase1/PHYSCUBIC.md` §2 (the Cauchy route).  For a function `τ` on a normed space `E`
(the space of fields with the sup norm), analytic and bounded by `M` on the ball of radius `r`
around a centre `φ₀` (the constant saddle `h`, or any other centre in the analytic domain), let
`g(λ) = τ(φ₀ + λ v)` be its restriction to the complex line through `v`.  The Taylor polynomial of
order `n` of `τ` at `φ₀` in the direction `v` is `∑_{j<n} g^{(j)}(0)/j!` (`taylorLine`).

* `norm_sub_taylorLine_le`: `‖τ(φ₀ + v) - ∑_{j<n} g^{(j)}(0)/j!‖ ≤ M q^n / (1 - q)`,
  `q = ‖v‖ / r < 1` (the Taylor series of `g` at `0`, `Complex.hasSum_taylorSeries_on_ball`, and
  the Cauchy estimate `norm_iteratedDeriv_line_le`);
* `norm_cubicRemainder_le`: the case `n = 3`, the cubic remainder
  `τ(φ₀ + v) - τ(φ₀) - g'(0) - g''(0)/2`, bounded by `M q³ / (1 - q)`;
* `norm_linRemainder_le`: the case `n = 2` (remainder of the linear part).

At the last scale the displacement is `v = β_k^{-1/2} C(s) w` with `‖v‖ ≤ B(κ) β_k^{-1/2} p₁` on the
box, so the cubic remainder of a term bounded by `M` on a ball of radius `r` is
`≤ 2 M (B(κ) β_k^{-1/2} p₁ / r)³` once `q ≤ 1/2`.
-/

@[expose] public section

namespace Balaban.Green

open Metric Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Taylor polynomial of order `n` of `τ` at `φ₀` in the direction `v`:
`∑_{j<n} g^{(j)}(0)/j!`, `g(λ) = τ(φ₀ + λ v)`. -/
noncomputable def taylorLine (n : ℕ) (τ : E → ℂ) (φ₀ v : E) : ℂ :=
  ∑ j ∈ Finset.range n, ((j ! : ℂ))⁻¹ * iteratedDeriv j (fun l : ℂ => τ (φ₀ + l • v)) 0

/-- **The Cauchy bound for the Taylor remainder of order `n` at a general centre.** -/
theorem norm_sub_taylorLine_le {τ : E → ℂ} {φ₀ : E} {r M : ℝ} (hr : 0 < r)
    (hτ : DifferentiableOn ℂ τ (ball φ₀ r)) (hM : ∀ u ∈ ball φ₀ r, ‖τ u‖ ≤ M) {v : E}
    (hv : ‖v‖ < r) (n : ℕ) :
    ‖τ (φ₀ + v) - taylorLine n τ φ₀ v‖ ≤ M * (‖v‖ / r) ^ n / (1 - ‖v‖ / r) := by
  set q := ‖v‖ / r with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq, div_lt_one hr]; exact hv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM φ₀ (mem_ball_self hr))
  set g : ℂ → ℂ := fun l => τ (φ₀ + l • v) with hg
  -- the coefficient bound
  have hcoef : ∀ j : ℕ, ‖((j ! : ℂ))⁻¹ * iteratedDeriv j g 0‖ ≤ M * q ^ j := by
    intro j
    have h := Balaban.Analysis.norm_iteratedDeriv_line_le hr hτ hM v j
    have hf : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (j ! : ℝ)⁻¹ * ‖iteratedDeriv j g 0‖ ≤ (j ! : ℝ)⁻¹ * (j ! * M * ‖v‖ ^ j / r ^ j) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = M * q ^ j := by rw [hq, div_pow]; field_simp
  -- the Taylor series of `g` at `0`, evaluated at `1`
  have hsum : HasSum (fun j : ℕ => ((j ! : ℂ))⁻¹ * iteratedDeriv j g 0) (τ (φ₀ + v)) := by
    by_cases hv0 : v = 0
    · subst hv0
      have hgc : g = fun _ => τ φ₀ := by funext l; simp [hg]
      have : (fun j : ℕ => ((j ! : ℂ))⁻¹ * iteratedDeriv j g 0) =
          fun j => if j = 0 then τ φ₀ else 0 := by
        funext j
        rw [hgc]
        by_cases hj : j = 0
        · subst hj; simp
        · simp [hj, iteratedDeriv_const]
      rw [this, add_zero]
      exact hasSum_ite_eq 0 (τ φ₀)
    · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have hgd : DifferentiableOn ℂ g (ball (0 : ℂ) (r / ‖v‖)) := by
        intro l hl
        have hl' : φ₀ + l • v ∈ ball φ₀ r := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
          have := mem_ball_zero_iff.1 hl
          rwa [lt_div_iff₀ hvn] at this
        have h1 : DifferentiableAt ℂ (fun l : ℂ => φ₀ + l • v) l := by fun_prop
        exact ((hτ.differentiableAt (isOpen_ball.mem_nhds hl')).comp l h1).differentiableWithinAt
      have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (r / ‖v‖) := by
        rw [mem_ball_zero_iff, norm_one, one_lt_div hvn]; exact hv
      have H := Complex.hasSum_taylorSeries_on_ball hgd h1
      have e : g 1 = τ (φ₀ + v) := by simp [hg]
      rw [e] at H
      convert H using 1
      funext j
      simp [smul_eq_mul]
  -- the remainder is the tail of the series
  have htail := (hasSum_nat_add_iff' n).2 hsum
  have hgeo : HasSum (fun j : ℕ => M * q ^ (j + n)) (M * q ^ n / (1 - q)) := by
    have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q ^ n)
    convert this using 1
    · funext j; ring
    · field_simp
  have hle := htail.norm_le_of_bounded hgeo fun j => hcoef (j + n)
  unfold taylorLine
  exact hle

/-- **The cubic remainder at a general centre**: `τ(φ₀ + v) - τ(φ₀) - g'(0) - g''(0)/2` is bounded
by `M q³ / (1 - q)`, `q = ‖v‖ / r`. -/
theorem norm_cubicRemainder_le {τ : E → ℂ} {φ₀ : E} {r M : ℝ} (hr : 0 < r)
    (hτ : DifferentiableOn ℂ τ (ball φ₀ r)) (hM : ∀ u ∈ ball φ₀ r, ‖τ u‖ ≤ M) {v : E}
    (hv : ‖v‖ < r) :
    ‖τ (φ₀ + v) - τ φ₀ - deriv (fun l : ℂ => τ (φ₀ + l • v)) 0 -
        (1 / 2 : ℂ) * iteratedDeriv 2 (fun l : ℂ => τ (φ₀ + l • v)) 0‖ ≤
      M * (‖v‖ / r) ^ 3 / (1 - ‖v‖ / r) := by
  have h := norm_sub_taylorLine_le hr hτ hM hv 3
  have e : taylorLine 3 τ φ₀ v = τ φ₀ + deriv (fun l : ℂ => τ (φ₀ + l • v)) 0 +
      (1 / 2 : ℂ) * iteratedDeriv 2 (fun l : ℂ => τ (φ₀ + l • v)) 0 := by
    unfold taylorLine
    simp [Finset.sum_range_succ, iteratedDeriv_one]
  rw [e] at h
  convert h using 2
  ring

/-- **The remainder of the linear part at a general centre**: `τ(φ₀ + v) - τ(φ₀) - g'(0)` is
bounded by `M q² / (1 - q)`. -/
theorem norm_linRemainder_le {τ : E → ℂ} {φ₀ : E} {r M : ℝ} (hr : 0 < r)
    (hτ : DifferentiableOn ℂ τ (ball φ₀ r)) (hM : ∀ u ∈ ball φ₀ r, ‖τ u‖ ≤ M) {v : E}
    (hv : ‖v‖ < r) :
    ‖τ (φ₀ + v) - τ φ₀ - deriv (fun l : ℂ => τ (φ₀ + l • v)) 0‖ ≤
      M * (‖v‖ / r) ^ 2 / (1 - ‖v‖ / r) := by
  have h := norm_sub_taylorLine_le hr hτ hM hv 2
  have e : taylorLine 2 τ φ₀ v = τ φ₀ + deriv (fun l : ℂ => τ (φ₀ + l • v)) 0 := by
    unfold taylorLine
    simp [Finset.sum_range_succ, iteratedDeriv_one]
  rw [e] at h
  convert h using 2
  ring

end Balaban.Green
