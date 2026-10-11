module

public import Balaban.Gaussian.BlockSpin
public import Balaban.Lattice.BlockAverage
public import Balaban.Lattice.Laplacian

/-!
# The exact multiscale decomposition of the covariance

Iteration of the Gaussian block-spin step (P9 (4.12)-(4.17); E3 (3.8)). Conventions: Euclidean
matrices (plain sums); a weighted lattice inner product is absorbed into the scale parameters
`a_j` (see `integral_blockSpin_weighted`), and the effective operator `A_{j+1} = Δ_j` is written on
the coarse torus without rescaling.

## One step

For `A` positive definite, `Q : Matrix κ ι ℝ`, `a > 0`, `M = A + a QᵀQ`, `Δ = a - a² Q M⁻¹ Qᵀ`,
`H = a M⁻¹ Qᵀ`:
`A⁻¹ = M⁻¹ + H Δ⁻¹ Hᵀ` (`inv_eq_blockSpin_decomposition`), with `M⁻¹` the fluctuation covariance
and `H Δ⁻¹ Hᵀ` the covariance of the minimizer `Hψ`.

## Iteration

On the tori `Level d L m k = Torus d (L ^ k * m)` with block factor `L` and scales
`a : ℕ → ℝ` (`a 0` for the first step from the finest level, then `a 1`, ...):
* `effOp k A a` is the effective operator on the coarsest level `Level 0` after `k` steps,
  `A_{j+1} = Δ_j`;
* `prolong k A a = H_0 H_1 ⋯ H_{k-1}` (`H_j = a_j M_j⁻¹ Q_jᵀ`);
* `fluct k A a = ∑_{j<k} H_0⋯H_{j-1} M_j⁻¹ (H_0⋯H_{j-1})ᵀ` (defined by the recursion
  `fluct (k+1) A a = M_0⁻¹ + H_0 · fluct k Δ_0 (a ∘ succ) · H_0ᵀ`, which unfolds to the sum).

Main results: `inv_eq_multiscale` (`A⁻¹ = fluct + P (effOp)⁻¹ Pᵀ`), `effOp_posDef`,
`fluct_posSemidef`, `fluct_succ_posDef`.
-/

@[expose] public section

namespace Balaban

open Matrix

section Abstract

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `H = a M⁻¹ Qᵀ`: the minimizer map `ψ ↦ H ψ` of the block-spin step. -/
noncomputable def blockSpinProlong (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) :
    Matrix ι κ ℝ :=
  a • ((blockSpinPrecision A Q a)⁻¹ * Qᵀ)

/-- One step: `A⁻¹ = M⁻¹ + H Δ⁻¹ Hᵀ`. -/
theorem inv_eq_blockSpin_decomposition {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ)
    {a : ℝ} (ha : 0 < a) :
    A⁻¹ = (blockSpinPrecision A Q a)⁻¹ +
      blockSpinProlong A Q a * (blockSpinOperator A Q a)⁻¹ * (blockSpinProlong A Q a)ᵀ := by
  have hM := blockSpinPrecision_posDef hA Q ha
  have hMu : IsUnit (blockSpinPrecision A Q a).det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  have hΔ : (blockSpinOperator A Q a)⁻¹ = a⁻¹ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ := by
    rw [blockSpinOperator_eq_inv hA Q ha]
    exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (woodbury_posDef hA Q ha).det_pos.ne')
  have hNt : ((blockSpinPrecision A Q a)⁻¹)ᵀ = (blockSpinPrecision A Q a)⁻¹ := by
    have := hM.isHermitian.inv
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  set M := blockSpinPrecision A Q a with hMdef
  set N := M⁻¹ with hN
  set B := A⁻¹ with hB
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul _ hMu
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv _ hMu
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv _ hAu
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul _ hAu
  have hMA : M = A + a • (Qᵀ * Q) := rfl
  have e2 : B - N = a • (B * (Qᵀ * Q) * N) := by
    have : B * (M - A) * N = B - N := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hMN, Matrix.mul_one, Matrix.mul_assoc,
        ← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
    rw [← this, hMA, add_sub_cancel_left]
    simp
  unfold blockSpinProlong
  rw [hΔ]
  simp only [← hMdef, ← hN]
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hNt]
  set P := Qᵀ * Q with hP
  have key : (a • (N * Qᵀ)) * (a⁻¹ • (1 : Matrix κ κ ℝ) + Q * B * Qᵀ) * (a • (Q * N)) =
      a • (N * P * N) + a • (N * P * (a • (B * P * N))) := by
    simp only [hP, Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add,
      smul_smul, Matrix.mul_one, Matrix.mul_assoc]
    have : a * (a⁻¹ * a) = a := by field_simp
    rw [this]
  have e1 : B - N = a • (N * P * B) := by
    have : N * (M - A) * B = B - N := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hNM, Matrix.one_mul, Matrix.mul_assoc N A B, hAB,
        Matrix.mul_one]
    rw [← this, hMA, add_sub_cancel_left]
    simp [hP, Matrix.mul_assoc]
  rw [key, ← e2, Matrix.mul_sub, smul_sub, ← e1]
  abel

omit [DecidableEq ι] [DecidableEq κ] in
/-- The covariance of the minimizer, `H Δ⁻¹ Hᵀ`, is positive semidefinite. -/
theorem prolong_conj_posSemidef (H : Matrix ι κ ℝ) {X : Matrix κ κ ℝ}
    (hX : X.PosSemidef) : (H * X * Hᵀ).PosSemidef := by
  simpa using hX.mul_mul_conjTranspose_same H

omit [DecidableEq κ] in
/-- Symmetric positive definite inverse: the fluctuation covariance `M⁻¹` is positive definite. -/
theorem blockSpinPrecision_inv_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ)
    {a : ℝ} (ha : 0 < a) : (blockSpinPrecision A Q a)⁻¹.PosDef :=
  (blockSpinPrecision_posDef hA Q ha).inv

end Abstract

section Iteration

variable (d L m : ℕ) [NeZero L] [NeZero m]

/-- The torus at level `k`: side `L ^ k * m`. Level `0` is the coarsest. -/
abbrev Level (k : ℕ) : Type := Torus d (L ^ k * m)

/-- The block averaging matrix from level `k + 1` to level `k`. -/
noncomputable def stepMatrix (k : ℕ) : Matrix (Level d L m k) (Level d L m (k + 1)) ℝ :=
  blockAverageMatrix L (L ^ k * m)

variable {d L m}

/-- The fluctuation covariance of the first step, `M₀⁻¹`, from level `k + 1`. -/
noncomputable def stepCov (k : ℕ) (A : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ)
    (a₀ : ℝ) : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ :=
  (blockSpinPrecision A (stepMatrix d L m k) a₀)⁻¹

/-- The effective operator on level `k` after one step from level `k + 1`: `Δ`. -/
noncomputable def stepOp (k : ℕ) (A : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ)
    (a₀ : ℝ) : Matrix (Level d L m k) (Level d L m k) ℝ :=
  blockSpinOperator A (stepMatrix d L m k) a₀

/-- The minimizer map `H = a M⁻¹ Qᵀ` of one step. -/
noncomputable def stepProlong (k : ℕ)
    (A : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ) (a₀ : ℝ) :
    Matrix (Level d L m (k + 1)) (Level d L m k) ℝ :=
  blockSpinProlong A (stepMatrix d L m k) a₀

/-- The total fluctuation covariance after `k` steps from level `k`:
`∑_{j<k} H_0⋯H_{j-1} M_j⁻¹ (H_0⋯H_{j-1})ᵀ`, by the recursion
`fluct (k+1) A a = M₀⁻¹ + H₀ · fluct k Δ₀ (a ∘ succ) · H₀ᵀ`. -/
noncomputable def fluct :
    (k : ℕ) → Matrix (Level d L m k) (Level d L m k) ℝ → (ℕ → ℝ) →
      Matrix (Level d L m k) (Level d L m k) ℝ
  | 0, _, _ => 0
  | k + 1, A, a =>
    stepCov k A (a 0) + stepProlong k A (a 0) * fluct k (stepOp k A (a 0)) (fun j => a (j + 1)) *
      (stepProlong k A (a 0))ᵀ

/-- The effective operator on the coarsest level `0` after `k` steps. -/
noncomputable def effOp :
    (k : ℕ) → Matrix (Level d L m k) (Level d L m k) ℝ → (ℕ → ℝ) →
      Matrix (Level d L m 0) (Level d L m 0) ℝ
  | 0, A, _ => A
  | k + 1, A, a => effOp k (stepOp k A (a 0)) (fun j => a (j + 1))

/-- The composite `H_0 H_1 ⋯ H_{k-1}` from level `0` to level `k`. -/
noncomputable def prolong :
    (k : ℕ) → Matrix (Level d L m k) (Level d L m k) ℝ → (ℕ → ℝ) →
      Matrix (Level d L m k) (Level d L m 0) ℝ
  | 0, _, _ => 1
  | k + 1, A, a =>
    stepProlong k A (a 0) * prolong k (stepOp k A (a 0)) (fun j => a (j + 1))

/-- The effective operators are positive definite. -/
theorem effOp_posDef : ∀ (k : ℕ) {A : Matrix (Level d L m k) (Level d L m k) ℝ} {a : ℕ → ℝ},
    A.PosDef → (∀ j, 0 < a j) → (effOp k A a).PosDef
  | 0, _, _, hA, _ => hA
  | k + 1, _, _, hA, ha =>
    effOp_posDef k (blockSpinOperator_posDef hA (stepMatrix d L m k) (ha 0)) (fun j => ha (j + 1))

/-- The multiscale decomposition: `A⁻¹ = fluct + P (effOp)⁻¹ Pᵀ`, `P = H_0 ⋯ H_{k-1}`. -/
theorem inv_eq_multiscale : ∀ (k : ℕ) {A : Matrix (Level d L m k) (Level d L m k) ℝ}
    {a : ℕ → ℝ}, A.PosDef → (∀ j, 0 < a j) →
    A⁻¹ = fluct k A a + prolong k A a * (effOp k A a)⁻¹ * (prolong k A a)ᵀ
  | 0, A, a, _, _ => by simp [fluct, effOp, prolong]
  | k + 1, A, a, hA, ha => by
    have h1 := inv_eq_blockSpin_decomposition hA (stepMatrix d L m k) (ha 0)
    have h2 := inv_eq_multiscale k (blockSpinOperator_posDef hA (stepMatrix d L m k) (ha 0))
      (fun j => ha (j + 1))
    change A⁻¹ = stepCov k A (a 0) + stepProlong k A (a 0) * fluct k (stepOp k A (a 0))
        (fun j => a (j + 1)) * (stepProlong k A (a 0))ᵀ + _
    have h1' : A⁻¹ = stepCov k A (a 0) + stepProlong k A (a 0) * (stepOp k A (a 0))⁻¹ *
        (stepProlong k A (a 0))ᵀ := h1
    rw [h1']
    have h2' : (stepOp k A (a 0))⁻¹ = fluct k (stepOp k A (a 0)) (fun j => a (j + 1)) +
        prolong k (stepOp k A (a 0)) (fun j => a (j + 1)) *
          (effOp k (stepOp k A (a 0)) (fun j => a (j + 1)))⁻¹ *
          (prolong k (stepOp k A (a 0)) (fun j => a (j + 1)))ᵀ := h2
    rw [h2']
    simp only [prolong, effOp, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, add_assoc]

/-- The total fluctuation covariance is positive semidefinite. -/
theorem fluct_posSemidef : ∀ (k : ℕ) {A : Matrix (Level d L m k) (Level d L m k) ℝ}
    {a : ℕ → ℝ}, A.PosDef → (∀ j, 0 < a j) → (fluct k A a).PosSemidef
  | 0, _, _, _, _ => by simpa [fluct] using Matrix.PosSemidef.zero
  | k + 1, A, a, hA, ha => by
    have h1 : (stepCov k A (a 0)).PosDef := blockSpinPrecision_inv_posDef hA _ (ha 0)
    have h2 := fluct_posSemidef k (blockSpinOperator_posDef hA (stepMatrix d L m k) (ha 0))
      (fun j => ha (j + 1))
    exact h1.posSemidef.add (prolong_conj_posSemidef _ h2)

/-- For `k ≥ 1` the total fluctuation covariance is positive definite. -/
theorem fluct_succ_posDef (k : ℕ) {A : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ}
    {a : ℕ → ℝ} (hA : A.PosDef) (ha : ∀ j, 0 < a j) : (fluct (k + 1) A a).PosDef := by
  have h1 : (stepCov k A (a 0)).PosDef := blockSpinPrecision_inv_posDef hA _ (ha 0)
  have h2 := fluct_posSemidef k (blockSpinOperator_posDef hA (stepMatrix d L m k) (ha 0))
    (fun j => ha (j + 1))
  exact h1.add_posSemidef (prolong_conj_posSemidef _ h2)

/-- The multiscale decomposition of the torus covariance `(-Δ + ν)⁻¹` on `Torus d (L ^ k * m)`. -/
theorem laplacian_inv_eq_multiscale (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ}
    (ha : ∀ j, 0 < a j) :
    (latticeLaplacian d (L ^ k * m) ν)⁻¹ =
      fluct k (latticeLaplacian d (L ^ k * m) ν) a +
        prolong k (latticeLaplacian d (L ^ k * m) ν) a *
          (effOp k (latticeLaplacian d (L ^ k * m) ν) a)⁻¹ *
          (prolong k (latticeLaplacian d (L ^ k * m) ν) a)ᵀ :=
  inv_eq_multiscale k (latticeLaplacian_posDef hν) ha

/-- The effective operators of the torus Laplacian are positive definite. -/
theorem laplacian_effOp_posDef (k : ℕ) {ν : ℝ} (hν : 0 < ν) {a : ℕ → ℝ}
    (ha : ∀ j, 0 < a j) : (effOp k (latticeLaplacian d (L ^ k * m) ν) a).PosDef :=
  effOp_posDef k (latticeLaplacian_posDef hν) ha

end Iteration

end Balaban
