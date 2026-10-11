module

public import Balaban.Gaussian.Prolongation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The terms of the multiscale decomposition: composition of steps and the dictionary

Abstract part (matrices on arbitrary finite index types). Write
`schurOp A Q s = (s + Q A⁻¹ Qᵀ)⁻¹` and `schurProlong A Q s = A⁻¹ Qᵀ (s + Q A⁻¹ Qᵀ)⁻¹`; for
`s = a⁻¹` these are the effective operator `Δ` and the minimizer map `H` of the block-spin step
(`blockSpinOperator_eq_schurOp`, `blockSpinProlong_eq_schurProlong`). Composition of two steps
(`Q`, then `R` with `R Rᵀ = r`) is one step with the composite `R Q`:
* `schurOp_comp` : `schurOp (schurOp A Q s₀) R s = schurOp A (R Q) (s + r s₀)`;
* `schurProlong_comp` : `schurProlong A Q s₀ · schurProlong (schurOp A Q s₀) R s
  = schurProlong A (R Q) (s + r s₀)` (iterated prolongation = one-shot prolongation).

Level part. `termDirect d L j ℓ ℓ₁ m₂ A a` is the `j`-th term in one-shot form,
`T_j = H (Δ + a_j Q₁ᵀ Q₁)⁻¹ Hᵀ`, written with the explicit side lengths `ℓ`, `ℓ₁`, `m₂` (no
dependence on the number of further steps). `fluctTerm_eq_termDirect` identifies it with the
`j`-th term `fluctTerm k A a j` of the `k`-step decomposition on `Torus d (L ^ k * m)`, for every
`k = n + 1 + j`, with `ℓ₁ = L ^ (n+1) m` (the torus on which the `j`-th step operator lives).
-/

@[expose] public section

namespace Balaban

open Matrix


section Abstract
variable {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ρ] [DecidableEq ρ]

/-- `(s + Q A⁻¹ Qᵀ)⁻¹`: the effective operator of a block-spin step with inverse penalty `s`
(`s = a⁻¹` is `blockSpinOperator`). -/
noncomputable def schurOp (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (s : ℝ) : Matrix κ κ ℝ :=
  (s • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ)⁻¹

/-- `A⁻¹ Qᵀ (s + Q A⁻¹ Qᵀ)⁻¹`: the prolongation of a block-spin step with inverse penalty `s`. -/
noncomputable def schurProlong (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (s : ℝ) : Matrix ι κ ℝ :=
  A⁻¹ * Qᵀ * schurOp A Q s

theorem blockSpinOperator_eq_schurOp {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ)
    {a : ℝ} (ha : 0 < a) : blockSpinOperator A Q a = schurOp A Q a⁻¹ :=
  blockSpinOperator_eq_inv hA Q ha

theorem blockSpinProlong_eq_schurProlong {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ)
    {a : ℝ} (ha : 0 < a) : blockSpinProlong A Q a = schurProlong A Q a⁻¹ := by
  rw [blockSpinProlong_eq hA Q ha, schurProlong, blockSpinOperator_eq_schurOp hA Q ha,
    Matrix.mul_assoc]

theorem schurOp_one {A : Matrix ι ι ℝ} (hA : A.PosDef) : schurOp A (1 : Matrix ι ι ℝ) 0 = A := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  simp [schurOp, Matrix.nonsing_inv_nonsing_inv _ hu]

theorem schurProlong_one {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    schurProlong A (1 : Matrix ι ι ℝ) 0 = 1 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  rw [schurProlong, schurOp_one hA]
  simp [Matrix.nonsing_inv_mul _ hu]

theorem schurOp_comp {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (R : Matrix ρ κ ℝ) {r : ℝ} (hR : R * Rᵀ = r • (1 : Matrix ρ ρ ℝ)) (s : ℝ) :
    schurOp (schurOp A Q s₀) R s = schurOp A (R * Q) (s + r * s₀) := by
  have hX := woodbury_posDef hA Q (inv_pos.mpr hs₀)
  rw [inv_inv] at hX
  have hXu : IsUnit (s₀ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ).det :=
    isUnit_iff_ne_zero.mpr hX.det_pos.ne'
  unfold schurOp
  rw [Matrix.nonsing_inv_nonsing_inv _ hXu]
  congr 1
  have : R * (s₀ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ) * Rᵀ =
      (r * s₀) • (1 : Matrix ρ ρ ℝ) + (R * Q) * A⁻¹ * (R * Q)ᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hR, smul_smul, mul_comm]
  rw [this, ← add_assoc, ← add_smul]


theorem schurProlong_comp {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (R : Matrix ρ κ ℝ) {r : ℝ} (hR : R * Rᵀ = r • (1 : Matrix ρ ρ ℝ)) (s : ℝ) :
    schurProlong A Q s₀ * schurProlong (schurOp A Q s₀) R s =
      schurProlong A (R * Q) (s + r * s₀) := by
  have hX := woodbury_posDef hA Q (inv_pos.mpr hs₀)
  rw [inv_inv] at hX
  have hXu : IsUnit (s₀ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ).det :=
    isUnit_iff_ne_zero.mpr hX.det_pos.ne'
  have hD : IsUnit (schurOp A Q s₀).det := by
    unfold schurOp; exact Matrix.isUnit_nonsing_inv_det _ hXu
  have hinv : (schurOp A Q s₀)⁻¹ = s₀ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ := by
    unfold schurOp; exact Matrix.nonsing_inv_nonsing_inv _ hXu
  have hmul : schurOp A Q s₀ * (schurOp A Q s₀)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
  have hcomp := schurOp_comp hA Q hs₀ R hR s
  calc schurProlong A Q s₀ * schurProlong (schurOp A Q s₀) R s
      = A⁻¹ * Qᵀ * (schurOp A Q s₀ * (schurOp A Q s₀)⁻¹) * Rᵀ *
          schurOp (schurOp A Q s₀) R s := by
        simp only [schurProlong, Matrix.mul_assoc]
    _ = A⁻¹ * (R * Q)ᵀ * schurOp A (R * Q) (s + r * s₀) := by
        rw [hmul, Matrix.mul_one, hcomp, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := rfl

end Abstract

section Levels

variable {d L m : ℕ} [NeZero L] [NeZero m]

/-- The `j`-th term of the multiscale decomposition on `Torus d ℓ`, in one-shot form:
`T_j = H (Δ + a_j Q₁ᵀ Q₁)⁻¹ Hᵀ`, where `C = Q_{(j)}` is the composite average over `L ^ j`-blocks
from `Torus d ℓ` to `Torus d ℓ₁` (`ℓ = L ^ j ℓ₁`), `Δ = (b_j⁻¹ + C A⁻¹ Cᵀ)⁻¹` is the effective
operator after `j` steps, `H = A⁻¹ Cᵀ Δ` the composite prolongation (`b_j⁻¹ = invScale d L j a`),
and `Q₁` the last block average from `Torus d ℓ₁` to `Torus d m₂` (`ℓ₁ = L m₂`). -/
noncomputable def termDirect (d L j : ℕ) (ℓ ℓ₁ m₂ : ℕ) [NeZero ℓ] [NeZero ℓ₁] [NeZero m₂] (A : Matrix (Torus d ℓ) (Torus d ℓ) ℝ)
    (a : ℕ → ℝ) : Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  let C : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ := blockAverageMatrix (L ^ j) ℓ₁
  let Q : Matrix (Torus d m₂) (Torus d ℓ₁) ℝ := blockAverageMatrix L m₂
  schurProlong A C (invScale d L j a) *
    (schurOp A C (invScale d L j a) + a j • (Qᵀ * Q))⁻¹ * (schurProlong A C (invScale d L j a))ᵀ

theorem blockAverageMatrix_pow_mul_transpose {ℓ ℓ₁ : ℕ} [NeZero ℓ] [NeZero ℓ₁] (j : ℕ)
    (h : ℓ = L ^ j * ℓ₁) :
    (blockAverageMatrix (L ^ j) ℓ₁ : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ) *
        (blockAverageMatrix (L ^ j) ℓ₁ : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ)ᵀ =
      (((L : ℝ) ^ d)⁻¹) ^ j • (1 : Matrix (Torus d ℓ₁) (Torus d ℓ₁) ℝ) := by
  rw [blockAverageMatrix_mul_transpose h (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) j)]
  congr 1
  rw [Nat.cast_pow, ← pow_mul, mul_comm, pow_mul, inv_pow]

theorem fluctTerm_eq_termDirect (j : ℕ) :
    ∀ (n k : ℕ), k = n + 1 + j → ∀ (A : Matrix (Level d L m k) (Level d L m k) ℝ) (a : ℕ → ℝ),
      A.PosDef → (∀ i, 0 < a i) →
      fluctTerm k A a j = termDirect d L j (L ^ k * m) (L ^ (n + 1) * m) (L ^ n * m) A a := by
  induction j with
  | zero =>
    intro n k hk A a hA ha
    subst hk
    have hC : (blockAverageMatrix (L ^ 0) (L ^ (n + 1) * m) :
        Matrix (Torus d (L ^ (n + 1) * m)) (Torus d (L ^ (n + 1 + 0) * m)) ℝ) = 1 :=
      blockAverageMatrix_of_eq_one (pow_zero L)
    show stepCov n A (a 0) = _
    unfold termDirect
    simp only [hC]
    have h1 : invScale d L 0 a = 0 := rfl
    rw [h1, schurProlong_one hA, schurOp_one hA]
    simp only [Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    rfl
  | succ j ih =>
    intro n k hk A a hA ha
    subst hk
    have hΔ := blockSpinOperator_posDef hA (stepMatrix d L m (n + 1 + j)) (ha 0)
    have hIH := ih n (n + 1 + j) rfl (stepOp (n + 1 + j) A (a 0)) (fun i => a (i + 1)) hΔ
      (fun i => ha (i + 1))
    show stepProlong (n + 1 + j) A (a 0) * fluctTerm (n + 1 + j) (stepOp (n + 1 + j) A (a 0))
      (fun i => a (i + 1)) j * (stepProlong (n + 1 + j) A (a 0))ᵀ = _
    rw [hIH]
    have hQ : stepProlong (n + 1 + j) A (a 0) =
        schurProlong A (stepMatrix d L m (n + 1 + j)) (a 0)⁻¹ :=
      blockSpinProlong_eq_schurProlong hA _ (ha 0)
    have hO : stepOp (n + 1 + j) A (a 0) = schurOp A (stepMatrix d L m (n + 1 + j)) (a 0)⁻¹ :=
      blockSpinOperator_eq_schurOp hA _ (ha 0)
    have hCQ : (blockAverageMatrix (L ^ (j + 1)) (L ^ (n + 1) * m) :
        Matrix (Torus d (L ^ (n + 1) * m)) (Torus d (L ^ (n + 1 + (j + 1)) * m)) ℝ) =
        (blockAverageMatrix (L ^ j) (L ^ (n + 1) * m) :
          Matrix (Torus d (L ^ (n + 1) * m)) (Torus d (L ^ (n + 1 + j) * m)) ℝ) *
        stepMatrix d L m (n + 1 + j) := by
      unfold stepMatrix
      rw [blockAverageMatrix_mul (by ring) (by ring)]
      exact congrArg (fun N => (blockAverageMatrix N (L ^ (n + 1) * m) :
        Matrix (Torus d (L ^ (n + 1) * m)) (Torus d (L ^ (n + 1 + (j + 1)) * m)) ℝ))
        (pow_succ' L j)
    have hR := blockAverageMatrix_pow_mul_transpose (d := d) (L := L)
      (ℓ := L ^ (n + 1 + j) * m) (ℓ₁ := L ^ (n + 1) * m) j (by ring)
    have hcomp1 := schurProlong_comp hA (stepMatrix d L m (n + 1 + j))
      (inv_pos.mpr (ha 0)) (blockAverageMatrix (L ^ j) (L ^ (n + 1) * m) :
        Matrix (Torus d (L ^ (n + 1) * m)) (Torus d (L ^ (n + 1 + j) * m)) ℝ) hR
      (invScale d L j fun i => a (i + 1))
    have hcomp2 := schurOp_comp hA (stepMatrix d L m (n + 1 + j))
      (inv_pos.mpr (ha 0)) (blockAverageMatrix (L ^ j) (L ^ (n + 1) * m) :
        Matrix (Torus d (L ^ (n + 1) * m)) (Torus d (L ^ (n + 1 + j) * m)) ℝ) hR
      (invScale d L j fun i => a (i + 1))
    have hs : invScale d L (j + 1) a = (invScale d L j fun i => a (i + 1)) +
        (((L : ℝ) ^ d)⁻¹) ^ j * (a 0)⁻¹ := by
      rw [invScale, mul_comm]
    unfold termDirect
    simp only []
    rw [hs, hCQ, ← hcomp1, ← hcomp2, hQ, hO, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

/-- The dictionary for the free flow `α_i = a L^{(i+1)(d-2)}` (CORRELATIONS.md §2.1): the
`j`-th term is `T_j = H (Δ + α_j Q₁ᵀ Q₁)⁻¹ Hᵀ` with `Δ = (b_j⁻¹ + C A⁻¹ Cᵀ)⁻¹`, `H = A⁻¹ Cᵀ Δ`,
`C = Q_{(j)}`, `α_j = a L^{(j+1)(d-2)}` and
`b_j⁻¹ = a⁻¹ L^{-j(d-2)} (1 - L^{-2j}) / (1 - L^{-2})`, i.e. `b_j = L^{j(d-2)} a_j` with
`a_j = a (1 - L^{-2}) / (1 - L^{-2j})`. -/
theorem termDirect_freeSeq (hd : 2 ≤ d) (hL : 1 < L) {a : ℝ} (ha : 0 < a) (j : ℕ)
    {ℓ ℓ₁ m₂ : ℕ} [NeZero ℓ] [NeZero ℓ₁] [NeZero m₂] (A : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) :
    termDirect d L j ℓ ℓ₁ m₂ A (freeSeq d L a) =
      (schurProlong A (blockAverageMatrix (L ^ j) ℓ₁ : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ)
          (a⁻¹ * ((L : ℝ) ^ (j * (d - 2)))⁻¹ *
            ((1 - ((L : ℝ) ^ (2 * j))⁻¹) / (1 - ((L : ℝ) ^ 2)⁻¹)))) *
        (schurOp A (blockAverageMatrix (L ^ j) ℓ₁ : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ)
            (a⁻¹ * ((L : ℝ) ^ (j * (d - 2)))⁻¹ *
              ((1 - ((L : ℝ) ^ (2 * j))⁻¹) / (1 - ((L : ℝ) ^ 2)⁻¹))) +
          (a * (L : ℝ) ^ ((j + 1) * (d - 2))) •
            ((blockAverageMatrix L m₂ : Matrix (Torus d m₂) (Torus d ℓ₁) ℝ)ᵀ *
              (blockAverageMatrix L m₂ : Matrix (Torus d m₂) (Torus d ℓ₁) ℝ)))⁻¹ *
        (schurProlong A (blockAverageMatrix (L ^ j) ℓ₁ : Matrix (Torus d ℓ₁) (Torus d ℓ) ℝ)
          (a⁻¹ * ((L : ℝ) ^ (j * (d - 2)))⁻¹ *
            ((1 - ((L : ℝ) ^ (2 * j))⁻¹) / (1 - ((L : ℝ) ^ 2)⁻¹))))ᵀ := by
  unfold termDirect
  simp only []
  rw [invScale_freeSeq hd hL ha j]
  rfl

end Levels
end Balaban
