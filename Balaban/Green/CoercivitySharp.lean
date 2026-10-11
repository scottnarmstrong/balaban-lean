/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BlockPoincareSharp
public import Balaban.Green.Coercivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# `d`-free single-scale coercivity of `-Δ + ν + a Q* Q`

Brief W2d, item 2 (single-scale part). The versions of `Balaban/Green/Coercivity.lean` with the
sharp block Poincaré inequality `Balaban.blockPoincare_latticeEnergy_sharp` (constant `N² / 2`,
independent of `d`); no hypothesis `0 < d` is needed.

* `Balaban.blockHamiltonian_coercive_real_sharp`:
  `φᵀ H φ ≥ (min (2 / N²) a + ν) ‖φ‖²`;
* `Balaban.blockHamiltonianC_isCoercive_sharp`: for `‖α x‖ ≤ θ`, the complex matrix `H + diag α`
  is `(min (2 / N²) a + ν - θ)`-coercive;
* `Balaban.coercivity_const_ge_sharp`: `min 1 (a N²) / N² ≤ min (2 / N²) a`.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

omit [NeZero m] in
/-- `d`-free single-scale coercivity of `-Δ + ν + a Q* Q` on the torus (real fields, unit lattice
spacing, blocks of side `N`): the form dominates `(min (2 / N²) a + ν) ‖φ‖²`. -/
theorem blockHamiltonian_coercive_real_sharp [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (ν a : ℝ) (φ : Torus d ℓ → ℝ) :
    (min (2 / (N : ℝ) ^ 2) a + ν) * ∑ x, φ x ^ 2 ≤
      φ ⬝ᵥ blockHamiltonian d ℓ N m ν a *ᵥ φ := by
  rw [blockHamiltonian_quadratic hℓ hN, sum_sq_eq_sum_sq_sub_add hℓ hN φ]
  have hP := blockPoincare_latticeEnergy_sharp hℓ hN φ
  have hV : 0 ≤ ∑ x, (φ x - blockProjection N m φ x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0 ≤ ∑ x, (blockProjection N m φ x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hE : 2 / (N : ℝ) ^ 2 * ∑ x, (φ x - blockProjection N m φ x) ^ 2 ≤ latticeEnergy φ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN2]
    nlinarith
  have h1 : min (2 / (N : ℝ) ^ 2) a ≤ 2 / (N : ℝ) ^ 2 := min_le_left _ _
  have h2 : min (2 / (N : ℝ) ^ 2) a ≤ a := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_right h1 hV, mul_le_mul_of_nonneg_right h2 hW]

omit [NeZero m] in
/-- `d`-free single-scale coercivity with a complex perturbation `α`, `‖α x‖ ≤ θ`. -/
theorem blockHamiltonianC_isCoercive_sharp [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (ν a θ : ℝ) (α : Torus d ℓ → ℂ) (hα : ∀ x, ‖α x‖ ≤ θ) :
    Green.IsCoercive (blockHamiltonianC d ℓ N m ν a α) (min (2 / (N : ℝ) ^ 2) a + ν - θ) := by
  intro v
  unfold blockHamiltonianC
  rw [Green.reQuad_add, reQuad_map_ofReal, reQuad_diagonal]
  have h1 := blockHamiltonian_coercive_real_sharp hℓ hN ν a (fun i => (v i).re)
  have h2 := blockHamiltonian_coercive_real_sharp hℓ hN ν a (fun i => (v i).im)
  have h3 : ∑ i, (α i).re * ‖v i‖ ^ 2 ≥ -θ * Green.sqNorm v := by
    unfold Green.sqNorm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have : -θ ≤ (α i).re := by
      have := Complex.abs_re_le_norm (α i)
      have := hα i
      linarith [neg_abs_le (α i).re]
    nlinarith [sq_nonneg ‖v i‖]
  rw [sqNorm_eq_re_im] at h3 ⊢
  nlinarith [h1, h2, h3]

/-- The constant of `blockHamiltonian_coercive_real_sharp` in the form of GREEN.md:
`min (2 / N²) a ≥ min 1 (a N²) / N²` (no dependence on `d`, no sign condition on `a`). -/
theorem coercivity_const_ge_sharp (hN : 0 < N) {a : ℝ} :
    min 1 (a * (N : ℝ) ^ 2) / (N : ℝ) ^ 2 ≤ min (2 / (N : ℝ) ^ 2) a := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  refine le_min ?_ ?_
  · rw [div_le_div_iff_of_pos_right hN2]
    exact (min_le_left _ _).trans (by norm_num)
  · rw [div_le_iff₀ hN2]
    exact min_le_right _ _

end Balaban
