/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BlockPoincare
public import Balaban.Green.Coercive
public import Balaban.Lattice.Laplacian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Single-scale coercivity of `-Δ + ν + a Q* Q` on the torus

Item 2 of brief W2b; GREEN.md G-1(a) at one scale and its proof (§4.1).

Conventions. Fields are functions on `Torus d ℓ`, `ℓ = N * m`, with *unit lattice spacing*; all
sums are unweighted. The operator of GREEN.md with fine spacing `η = 1/N` (so that the block has
side `1`) is `η^{-2}` times the unit-spacing operator `-Δ + ν' + a' Q* Q` with `ν' = ν η²`,
`a' = a η²`: a statement `H ≥ c` below for the unit-spacing `H` is `H_GREEN ≥ N² c`.

* `Balaban.blockProjMatrix`: the matrix of `P = Q* Q` (`blockProjection`);
* `Balaban.blockHamiltonian`: the real matrix `-Δ + ν + a P` (`latticeLaplacian d ℓ ν + a • P`);
* `Balaban.blockHamiltonianC`: the complex matrix `-Δ + ν + a P + diag α`;
* `Balaban.blockHamiltonian_quadratic`: `φᵀ H φ = E(φ) + ν ‖φ‖² + a ‖P φ‖²`;
* `Balaban.blockHamiltonian_coercive_real`:
  `φᵀ H φ ≥ (min (2 / (d N²)) a + ν) ‖φ‖²` for `d > 0` (block Poincaré with constant `d/2`);
* `Balaban.blockHamiltonianC_isCoercive`: for `‖α x‖ ≤ θ`, the complex matrix `H + diag α` is
  `(min (2 / (d N²)) a + ν - θ)`-coercive in the sense of `Balaban.Green.IsCoercive`;
* `Balaban.coercivity_const_ge`: `min (2 / (d N²)) a ≥ min 1 (2 / d) · min 1 (a N²) / N²`
  (the form `c(d) min(1, a N²) N^{-2}` of the brief) for `a ≥ 0`.
-/

@[expose] public section

namespace Balaban

open Matrix Finset

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

/-- The matrix of the block projection `P = Q* Q`: `P x x' = N^{-d}` if `x, x'` lie in the same
block, `0` otherwise. -/
noncomputable def blockProjMatrix (d ℓ N m : ℕ) [NeZero ℓ] :
    Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  fun x x' => if blockMap N m x = blockMap N m x' then ((N : ℝ) ^ d)⁻¹ else 0

omit [NeZero m] in
theorem blockProjMatrix_mulVec (φ : Torus d ℓ → ℝ) (x : Torus d ℓ) :
    (blockProjMatrix d ℓ N m *ᵥ φ) x = blockProjection N m φ x := by
  simp only [Matrix.mulVec, dotProduct, blockProjMatrix, ite_mul, zero_mul, blockProjection_apply,
    blockAverage_apply]
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x'
  simp [mem_blockFibre, eq_comm]

section Quad

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem reQuad_map_ofReal (B : Matrix ι ι ℝ) (v : ι → ℂ) :
    Green.reQuad (B.map (algebraMap ℝ ℂ)) v =
      (fun i => (v i).re) ⬝ᵥ B *ᵥ (fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ B *ᵥ (fun i => (v i).im) := by
  unfold Green.reQuad
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]

theorem reQuad_diagonal (α : ι → ℂ) (v : ι → ℂ) :
    Green.reQuad (Matrix.diagonal α) v = ∑ i, (α i).re * ‖v i‖ ^ 2 := by
  unfold Green.reQuad
  simp only [Matrix.mulVec_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]; rfl
  have : star (v i) * (α i * v i) = ((α i) * ((‖v i‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← h]; ring
  rw [this, Complex.re_mul_ofReal]

omit [DecidableEq ι] in
theorem sqNorm_eq_re_im (v : ι → ℂ) :
    Green.sqNorm v = ∑ i, (v i).re ^ 2 + ∑ i, (v i).im ^ 2 := by
  unfold Green.sqNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

end Quad

section Hamiltonian

/-- The single-scale operator `H = -Δ + ν + a Q* Q` on the torus (unit lattice spacing). -/
noncomputable def blockHamiltonian (d ℓ N m : ℕ) [NeZero ℓ] (ν a : ℝ) :
    Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  latticeLaplacian d ℓ ν + a • blockProjMatrix d ℓ N m

/-- The complex operator `H + α` with a multiplication operator `α`. -/
noncomputable def blockHamiltonianC (d ℓ N m : ℕ) [NeZero ℓ] (ν a : ℝ) (α : Torus d ℓ → ℂ) :
    Matrix (Torus d ℓ) (Torus d ℓ) ℂ :=
  (blockHamiltonian d ℓ N m ν a).map (algebraMap ℝ ℂ) + Matrix.diagonal α

omit [NeZero m] in
theorem blockHamiltonian_quadratic (hℓ : ℓ = N * m) (hN : 0 < N) [NeZero m] (ν a : ℝ)
    (φ : Torus d ℓ → ℝ) :
    φ ⬝ᵥ blockHamiltonian d ℓ N m ν a *ᵥ φ =
      latticeEnergy φ + ν * ∑ x, φ x ^ 2 + a * ∑ x, (blockProjection N m φ x) ^ 2 := by
  unfold blockHamiltonian
  rw [Matrix.add_mulVec, dotProduct_add, latticeLaplacian_quadratic, Matrix.smul_mulVec,
    dotProduct_smul]
  have : φ ⬝ᵥ blockProjMatrix d ℓ N m *ᵥ φ = ∑ x, (blockProjection N m φ x) ^ 2 := by
    simp only [dotProduct, blockProjMatrix_mulVec]
    exact sum_mul_blockProjection hℓ hN φ
  rw [this]
  simp only [smul_eq_mul, latticeEnergy]

omit [NeZero m] in
/-- Single-scale coercivity of `-Δ + ν + a Q* Q` on the torus (real fields, unit lattice spacing,
blocks of side `N`): the form dominates `(min (2 / (d N²)) a + ν) ‖φ‖²`. -/
theorem blockHamiltonian_coercive_real [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d)
    (ν a : ℝ) (φ : Torus d ℓ → ℝ) :
    (min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a + ν) * ∑ x, φ x ^ 2 ≤
      φ ⬝ᵥ blockHamiltonian d ℓ N m ν a *ᵥ φ := by
  rw [blockHamiltonian_quadratic hℓ hN, sum_sq_eq_sum_sq_sub_add hℓ hN φ]
  have hP := blockPoincare_latticeEnergy hℓ hN φ
  have hV : 0 ≤ ∑ x, (φ x - blockProjection N m φ x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hW : 0 ≤ ∑ x, (blockProjection N m φ x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdN : (0 : ℝ) < (d : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hE : 2 / ((d : ℝ) * (N : ℝ) ^ 2) * ∑ x, (φ x - blockProjection N m φ x) ^ 2 ≤ latticeEnergy φ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hdN]
    nlinarith
  have h1 : min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a ≤ 2 / ((d : ℝ) * (N : ℝ) ^ 2) := min_le_left _ _
  have h2 : min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a ≤ a := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_right h1 hV, mul_le_mul_of_nonneg_right h2 hW]

omit [NeZero m] in
/-- Single-scale coercivity with a complex perturbation `α`, `‖α x‖ ≤ θ`: the matrix
`H + α` is `(min (2 / (d N²)) a + ν - θ)`-coercive in the sense of `Balaban.Green.IsCoercive`. -/
theorem blockHamiltonianC_isCoercive [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (hd : 0 < d)
    (ν a θ : ℝ) (α : Torus d ℓ → ℂ) (hα : ∀ x, ‖α x‖ ≤ θ) :
    Green.IsCoercive (blockHamiltonianC d ℓ N m ν a α)
      (min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a + ν - θ) := by
  intro v
  unfold blockHamiltonianC
  rw [Green.reQuad_add, reQuad_map_ofReal, reQuad_diagonal]
  have h1 := blockHamiltonian_coercive_real hℓ hN hd ν a (fun i => (v i).re)
  have h2 := blockHamiltonian_coercive_real hℓ hN hd ν a (fun i => (v i).im)
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

/-- The constant of `blockHamiltonian_coercive_real` in the form of GREEN.md:
`min (2 / (d N²)) a ≥ c(d) · min 1 (a N²) / N²` with `c(d) = min 1 (2 / d)`. -/
theorem coercivity_const_ge (hN : 0 < N) (hd : 0 < d) {a : ℝ} (ha : 0 ≤ a) :
    min 1 (2 / (d : ℝ)) * min 1 (a * (N : ℝ) ^ 2) / (N : ℝ) ^ 2 ≤
      min (2 / ((d : ℝ) * (N : ℝ) ^ 2)) a := by
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set c := min 1 (2 / (d : ℝ)) with hc
  set t := min 1 (a * (N : ℝ) ^ 2) with ht
  have hc0 : 0 < c := lt_min one_pos (by positivity)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hc2 : c ≤ 2 / (d : ℝ) := min_le_right _ _
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ a * (N : ℝ) ^ 2 := min_le_right _ _
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ hN2 (by positivity)]
    have : c * t * ((d : ℝ) * (N : ℝ) ^ 2) ≤ 2 * (N : ℝ) ^ 2 := by
      have e : c * (d : ℝ) ≤ 2 := by
        have := mul_le_mul_of_nonneg_right hc2 hdpos.le
        rwa [div_mul_cancel₀ _ hdpos.ne'] at this
      nlinarith [mul_nonneg ht0 hN2.le, mul_le_mul_of_nonneg_right e (mul_nonneg ht0 hN2.le)]
    linarith
  · rw [div_le_iff₀ hN2]
    nlinarith [mul_le_mul hc1 ht2 ht0 zero_le_one, mul_nonneg ha hN2.le]

end Hamiltonian

end Balaban
