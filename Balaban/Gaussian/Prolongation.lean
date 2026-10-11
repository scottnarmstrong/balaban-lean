module

public import Balaban.Gaussian.Multiscale
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prolongation: one-step identities, composition of prolongations, and the multiscale terms

Bookkeeping around `Balaban.Gaussian.Multiscale` (CORRELATIONS.md §2.1, §3.4).

## One step
* `mul_blockSpinProlong` : `A H = Qᵀ Δ` (CORRELATIONS (3.1)) for `H = a M⁻¹ Qᵀ`.
* `blockSpinOperator_inv` : `Δ⁻¹ = a⁻¹ + Q A⁻¹ Qᵀ`.

## Composition (iterated = one-shot)
* `compositeAvg d L m k` : the composite block average `Q_{(k)}` from level `k` to level `0`;
  `compositeAvg_eq` identifies it with the one-shot block average over `L ^ k` blocks.
* `mul_prolong` : `A₀ P_k = Q_{(k)}ᵀ A_k` (CORRELATIONS (3.2)).
* `invScale d L k a` : the scalar `b_k⁻¹` of the one-shot step; `effOp_inv` :
  `A_k⁻¹ = b_k⁻¹ + Q_{(k)} A₀⁻¹ Q_{(k)}ᵀ`.
* `effOp_eq_blockSpinOperator`, `prolong_eq_blockSpinProlong` : `k` iterated steps equal a single
  step with the composite average `Q_{(k)}` and the penalty `b_k = (invScale k a)⁻¹`.
* `invScale_freeSeq` : closed form of `b_k` for the free flow `α_i = a L^{(i+1)(d-2)}`.

## The terms
* `fluctTerm k A a j` : the `j`-th term of `fluct` (`j = 0` the finest scale), with
  `fluct_eq_sum_fluctTerm`.
-/

@[expose] public section

namespace Balaban

open Matrix

section Abstract
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- (3.1): `A H = Qᵀ Δ`. -/
theorem mul_blockSpinProlong {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) : A * blockSpinProlong A Q a = Qᵀ * blockSpinOperator A Q a := by
  have hM := blockSpinPrecision_posDef hA Q ha
  have hMN : blockSpinPrecision A Q a * (blockSpinPrecision A Q a)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  have h1 : A * (blockSpinPrecision A Q a)⁻¹ =
      1 - a • (Qᵀ * Q * (blockSpinPrecision A Q a)⁻¹) := by
    have : A = blockSpinPrecision A Q a - a • (Qᵀ * Q) := by simp [blockSpinPrecision]
    generalize blockSpinPrecision A Q a = M at hMN this ⊢
    subst this
    rw [Matrix.sub_mul, hMN, Matrix.smul_mul]
  unfold blockSpinProlong blockSpinOperator
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, h1]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_smul, sq, Matrix.mul_assoc]

/-- `H = A⁻¹ Qᵀ Δ`. -/
theorem blockSpinProlong_eq {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) : blockSpinProlong A Q a = A⁻¹ * (Qᵀ * blockSpinOperator A Q a) := by
  rw [← mul_blockSpinProlong hA Q ha, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), Matrix.one_mul]

/-- `Δ⁻¹ = a⁻¹ + Q A⁻¹ Qᵀ`. -/
theorem blockSpinOperator_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) : (blockSpinOperator A Q a)⁻¹ = a⁻¹ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ :=
  Matrix.inv_eq_right_inv (blockSpinOperator_mul_woodbury hA Q ha)

end Abstract

section Averages

variable {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]

theorem blockAverageMatrix_mul_transpose (hℓ : ℓ = N * m) (hN : 0 < N) :
    (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ) *
        (blockAverageMatrix N m : Matrix (Torus d m) (Torus d ℓ) ℝ)ᵀ =
      ((N : ℝ) ^ d)⁻¹ • (1 : Matrix (Torus d m) (Torus d m) ℝ) := by
  have hNd : ((N : ℝ) ^ d) ≠ 0 := by positivity
  ext y y'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockAverageMatrix, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : y = y'
  · subst h
    have key : ∀ x : Torus d ℓ, ((if blockMap N m x = y then ((N : ℝ) ^ d)⁻¹ else 0) *
        (if blockMap N m x = y then ((N : ℝ) ^ d)⁻¹ else 0)) =
        if blockMap N m x = y then ((N : ℝ) ^ d)⁻¹ * ((N : ℝ) ^ d)⁻¹ else 0 := by
      intro x; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun x _ => key x), ← Finset.sum_filter]
    have hf : (Finset.univ.filter fun x : Torus d ℓ => blockMap N m x = y) = blockFibre N m y := by
      ext x; simp [mem_blockFibre]
    rw [hf, Finset.sum_const, card_blockFibre hℓ]
    simp only [ite_true, nsmul_eq_mul, Nat.cast_pow]
    field_simp
  · simp only [h, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : blockMap N m x = y
    · have : ¬ blockMap N m x = y' := fun h2 => h (h1.symm.trans h2)
      simp [this]
    · simp [h1]


omit [NeZero m] in
theorem blockMap_one (x : Torus d ℓ) : blockMap 1 ℓ x = x := by
  funext i
  simp [blockMap_apply, blockCoord]

omit [NeZero m] in
theorem blockAverageMatrix_one :
    (blockAverageMatrix 1 ℓ : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) = 1 := by
  ext y x
  simp [blockAverageMatrix, blockMap_one, Matrix.one_apply, eq_comm]

theorem blockAverageMatrix_mul {m₁ m₂ N M : ℕ} [NeZero m₁] [NeZero m₂] (hℓ : ℓ = N * m₁)
    (hm : m₁ = M * m₂) :
    (blockAverageMatrix M m₂ : Matrix (Torus d m₂) (Torus d m₁) ℝ) *
        (blockAverageMatrix N m₁ : Matrix (Torus d m₁) (Torus d ℓ) ℝ) =
      (blockAverageMatrix (N * M) m₂ : Matrix (Torus d m₂) (Torus d ℓ) ℝ) := by
  ext z x
  simp only [Matrix.mul_apply, blockAverageMatrix]
  rw [Finset.sum_eq_single (blockMap N m₁ x)]
  · simp only [ite_true, ← blockMap_comp hℓ hm, Nat.cast_mul, mul_pow, mul_inv]
    split_ifs <;> simp [mul_comm]
  · intro y _ hy
    have : ¬ blockMap N m₁ x = y := fun h => hy h.symm
    simp [this]
  · simp

end Averages

section Levels

variable {d L m : ℕ} [NeZero L] [NeZero m]

theorem stepMatrix_mul_transpose (k : ℕ) :
    stepMatrix d L m k * (stepMatrix d L m k)ᵀ = ((L : ℝ) ^ d)⁻¹ • (1 : Matrix (Level d L m k) (Level d L m k) ℝ) :=
  blockAverageMatrix_mul_transpose (by ring) (Nat.pos_of_ne_zero (NeZero.ne L))

variable (d L m) in
/-- The composite block average `Q_{(k)} = Q_0 ⋯`: from level `k` to level `0`. -/
noncomputable def compositeAvg : (k : ℕ) → Matrix (Level d L m 0) (Level d L m k) ℝ
  | 0 => 1
  | k + 1 => compositeAvg k * stepMatrix d L m k

theorem compositeAvg_mul_transpose (k : ℕ) :
    compositeAvg d L m k * (compositeAvg d L m k)ᵀ =
      (((L : ℝ) ^ d)⁻¹) ^ k • (1 : Matrix (Level d L m 0) (Level d L m 0) ℝ) := by
  induction k with
  | zero => simp [compositeAvg]
  | succ k ih =>
    rw [compositeAvg, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (stepMatrix d L m k),
      stepMatrix_mul_transpose, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ih, smul_smul,
      pow_succ']

end Levels

section Levels2

variable {d L m : ℕ} [NeZero L] [NeZero m]

omit [NeZero m] in
theorem blockAverageMatrix_of_eq_one {ℓ N : ℕ} [NeZero ℓ] (hN : N = 1) :
    (blockAverageMatrix N ℓ : Matrix (Torus d ℓ) (Torus d ℓ) ℝ) = 1 := by
  subst hN
  exact blockAverageMatrix_one

/-- Iterated block averaging equals the one-shot block averaging over `L ^ k`-blocks. -/
theorem compositeAvg_eq (k : ℕ) :
    compositeAvg d L m k =
      (blockAverageMatrix (L ^ k) (L ^ 0 * m) : Matrix (Level d L m 0) (Level d L m k) ℝ) := by
  induction k with
  | zero => exact (blockAverageMatrix_of_eq_one (pow_zero L)).symm
  | succ k ih =>
    rw [compositeAvg, ih]
    unfold stepMatrix
    rw [blockAverageMatrix_mul (by ring) (by ring)]
    exact congrArg (fun N => (blockAverageMatrix N (L ^ 0 * m) :
      Matrix (Level d L m 0) (Level d L m (k + 1)) ℝ)) (pow_succ' L k).symm

theorem compositeAvg_apply (k : ℕ) (u : Level d L m 0) (x : Level d L m k) :
    compositeAvg d L m k u x =
      if blockMap (L ^ k) (L ^ 0 * m) x = u then (((L ^ k : ℕ) : ℝ) ^ d)⁻¹ else 0 := by
  rw [compositeAvg_eq]; rfl


/-- (3.2): `A₀ P_k = Q_{(k)}ᵀ A_k`. -/
theorem mul_prolong : ∀ (k : ℕ) {A : Matrix (Level d L m k) (Level d L m k) ℝ} {a : ℕ → ℝ},
    A.PosDef → (∀ j, 0 < a j) →
    A * prolong k A a = (compositeAvg d L m k)ᵀ * effOp k A a
  | 0, A, a, _, _ => by simp [prolong, effOp, compositeAvg]
  | k + 1, A, a, hA, ha => by
    have h1 := mul_blockSpinProlong hA (stepMatrix d L m k) (ha 0)
    have h2 := mul_prolong k (blockSpinOperator_posDef hA (stepMatrix d L m k) (ha 0))
      (fun j => ha (j + 1))
    simp only [prolong, effOp, stepProlong, stepOp, compositeAvg, Matrix.transpose_mul]
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, Matrix.mul_assoc]

/-- The scalar `b_k⁻¹ = ∑_{i<k} a_i⁻¹ (L^{-d})^{k-1-i}`, defined by peeling the first step. -/
noncomputable def invScale (d L : ℕ) : (k : ℕ) → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, a => invScale d L k (fun j => a (j + 1)) + (a 0)⁻¹ * (((L : ℝ) ^ d)⁻¹) ^ k

theorem invScale_nonneg (d L : ℕ) : ∀ (k : ℕ) {a : ℕ → ℝ}, (∀ j, 0 < a j) → 0 ≤ invScale d L k a
  | 0, _, _ => le_refl _
  | k + 1, a, ha => by
    rw [invScale]
    have := invScale_nonneg d L k (a := fun j => a (j + 1)) (fun j => ha (j + 1))
    have h0 := ha 0
    positivity

theorem invScale_pos (d L : ℕ) [NeZero L] (k : ℕ) {a : ℕ → ℝ} (ha : ∀ j, 0 < a j) :
    0 < invScale d L (k + 1) a := by
  rw [invScale]
  have := invScale_nonneg d L k (a := fun j => a (j + 1)) (fun j => ha (j + 1))
  have h0 := ha 0
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

/-- `A_k⁻¹ = b_k⁻¹ + Q_{(k)} A₀⁻¹ Q_{(k)}ᵀ`. -/
theorem effOp_inv : ∀ (k : ℕ) {A : Matrix (Level d L m k) (Level d L m k) ℝ} {a : ℕ → ℝ},
    A.PosDef → (∀ j, 0 < a j) →
    (effOp k A a)⁻¹ = invScale d L k a • (1 : Matrix (Level d L m 0) (Level d L m 0) ℝ) +
      compositeAvg d L m k * A⁻¹ * (compositeAvg d L m k)ᵀ
  | 0, A, a, _, _ => by simp [effOp, invScale, compositeAvg]
  | k + 1, A, a, hA, ha => by
    have h2 := effOp_inv k (blockSpinOperator_posDef hA (stepMatrix d L m k) (ha 0))
      (fun j => ha (j + 1))
    have h3 := blockSpinOperator_inv hA (stepMatrix d L m k) (ha 0)
    simp only [effOp, stepOp, invScale, compositeAvg, Matrix.transpose_mul]
    rw [h2, h3]
    have h4 := compositeAvg_mul_transpose (d := d) (L := L) (m := m) k
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
    rw [h4, smul_smul, add_smul, add_assoc]


/-- One-shot: after `k ≥ 1` steps the effective operator is `Δ = b - b² Q M⁻¹ Qᵀ` with the
composite average `Q = Q_{(k)}` and `b = b_k`. -/
theorem effOp_eq_blockSpinOperator (k : ℕ) {A : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ}
    {a : ℕ → ℝ} (hA : A.PosDef) (ha : ∀ j, 0 < a j) :
    effOp (k + 1) A a =
      blockSpinOperator A (compositeAvg d L m (k + 1)) (invScale d L (k + 1) a)⁻¹ := by
  have hb := invScale_pos d L k ha
  have hbi : 0 < (invScale d L (k + 1) a)⁻¹ := inv_pos.mpr hb
  have h1 := effOp_inv (k + 1) hA ha
  have h2 := blockSpinOperator_inv hA (compositeAvg d L m (k + 1)) hbi
  rw [inv_inv] at h2
  have hP := effOp_posDef (k + 1) hA ha
  have hP2 := blockSpinOperator_posDef hA (compositeAvg d L m (k + 1)) hbi
  rw [← h2] at h1
  calc effOp (k + 1) A a = ((effOp (k + 1) A a)⁻¹)⁻¹ :=
        (Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP.det_pos.ne')).symm
    _ = _ := by
      rw [h1]
      exact Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP2.det_pos.ne')

/-- One-shot prolongation: `H_0 ⋯ H_{k-1} = b M⁻¹ Qᵀ` with `Q = Q_{(k)}`, `b = b_k`. -/
theorem prolong_eq_blockSpinProlong (k : ℕ) {A : Matrix (Level d L m (k + 1)) (Level d L m (k + 1)) ℝ}
    {a : ℕ → ℝ} (hA : A.PosDef) (ha : ∀ j, 0 < a j) :
    prolong (k + 1) A a =
      blockSpinProlong A (compositeAvg d L m (k + 1)) (invScale d L (k + 1) a)⁻¹ := by
  have hb := invScale_pos d L k ha
  have hbi : 0 < (invScale d L (k + 1) a)⁻¹ := inv_pos.mpr hb
  have h1 := mul_prolong (k + 1) hA ha
  rw [effOp_eq_blockSpinOperator k hA ha, ← mul_blockSpinProlong hA _ hbi] at h1
  have hAi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  calc prolong (k + 1) A a = A⁻¹ * (A * prolong (k + 1) A a) := by
        rw [← Matrix.mul_assoc, hAi, Matrix.one_mul]
    _ = _ := by
        rw [h1, ← Matrix.mul_assoc, hAi, Matrix.one_mul]


theorem invScale_smul (d L : ℕ) {s : ℝ} (hs : s ≠ 0) :
    ∀ (k : ℕ) (a : ℕ → ℝ), invScale d L k (fun j => s * a j) = s⁻¹ * invScale d L k a
  | 0, _ => by simp [invScale]
  | k + 1, a => by
    rw [invScale, invScale, invScale_smul d L hs k (fun j => a (j + 1))]
    ring

/-- The free-flow sequence `α_i = a L^{(i+1)(d-2)}` of CORRELATIONS.md §2.1. -/
noncomputable def freeSeq (d L : ℕ) (a : ℝ) (i : ℕ) : ℝ := a * (L : ℝ) ^ ((i + 1) * (d - 2))

theorem freeSeq_pos {d L : ℕ} [NeZero L] {a : ℝ} (ha : 0 < a) (i : ℕ) : 0 < freeSeq d L a i := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold freeSeq
  positivity

/-- Closed form of the penalty after `k` steps of the free flow:
`b_k⁻¹ = a⁻¹ L^{-k(d-2)} (1 - L^{-2k}) / (1 - L^{-2})`, i.e. `b_k = L^{k(d-2)} a_k` with
`a_k = a (1 - L^{-2}) / (1 - L^{-2k})`. -/
theorem invScale_freeSeq {d L : ℕ} [NeZero L] (hd : 2 ≤ d) (hL : 1 < L) {a : ℝ} (ha : 0 < a)
    (k : ℕ) :
    invScale d L k (freeSeq d L a) =
      a⁻¹ * ((L : ℝ) ^ (k * (d - 2)))⁻¹ *
        ((1 - ((L : ℝ) ^ (2 * k))⁻¹) / (1 - ((L : ℝ) ^ 2)⁻¹)) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hx : (1 : ℝ) < L := by exact_mod_cast hL
  have hx0 : (0 : ℝ) < L := by linarith
  have hy : 0 < (L : ℝ) ^ e := by positivity
  have h12 : (1 : ℝ) - ((L : ℝ) ^ 2)⁻¹ ≠ 0 := by
    have : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
    linarith
  induction k with
  | zero => simp [invScale]
  | succ k ih =>
    have hshift : (fun j => freeSeq (e + 2) L a (j + 1)) =
        fun j => (L : ℝ) ^ e * freeSeq (e + 2) L a j := by
      funext j
      simp only [freeSeq, Nat.add_sub_cancel]
      rw [mul_left_comm, ← pow_add]
      congr 2
      ring
    rw [invScale, hshift, invScale_smul _ _ hy.ne', ih]
    simp only [freeSeq, Nat.add_sub_cancel, zero_add, one_mul, Nat.add_sub_cancel]
    have e1 : ∀ n : ℕ, (L : ℝ) ^ (n * e) = ((L : ℝ) ^ e) ^ n := fun n => by
      rw [← pow_mul, mul_comm]
    have e2 : ∀ n : ℕ, (L : ℝ) ^ (2 * n) = ((L : ℝ) ^ 2) ^ n := fun n => by
      rw [← pow_mul]
    rw [e1, e1, e2, e2, pow_add]
    simp only [inv_pow, mul_pow]
    have hY : 0 < (L : ℝ) ^ 2 := by positivity
    have hXk : 0 < ((L : ℝ) ^ e) ^ k := by positivity
    have hYk : 0 < ((L : ℝ) ^ 2) ^ k := by positivity
    have hYs : (L : ℝ) ^ 2 - 1 ≠ 0 := by
      have : (1 : ℝ) < (L : ℝ) ^ 2 := one_lt_pow₀ hx (by norm_num)
      linarith
    generalize (L : ℝ) ^ e = X at *
    generalize (L : ℝ) ^ 2 = Y at *
    field_simp
    ring


/-- The `j`-th term of `fluct`, on the finest torus `Level k`: `j = 0` is the fluctuation
covariance `M₀⁻¹` of the finest scale, and the `(j+1)`-st term is the `j`-th term of the coarser
problem `Δ₀`, prolonged by `H₀`. -/
noncomputable def fluctTerm :
    (k : ℕ) → Matrix (Level d L m k) (Level d L m k) ℝ → (ℕ → ℝ) → ℕ →
      Matrix (Level d L m k) (Level d L m k) ℝ
  | 0, _, _, _ => 0
  | k + 1, A, a, 0 => stepCov k A (a 0)
  | k + 1, A, a, j + 1 =>
    stepProlong k A (a 0) * fluctTerm k (stepOp k A (a 0)) (fun i => a (i + 1)) j *
      (stepProlong k A (a 0))ᵀ

/-- `fluct` is the sum of the terms `fluctTerm k A a j`, `j < k`. -/
theorem fluct_eq_sum_fluctTerm : ∀ (k : ℕ) (A : Matrix (Level d L m k) (Level d L m k) ℝ)
    (a : ℕ → ℝ), fluct k A a = ∑ j ∈ Finset.range k, fluctTerm k A a j
  | 0, _, _ => by simp [fluct]
  | k + 1, A, a => by
    rw [fluct, fluct_eq_sum_fluctTerm k, Finset.sum_range_succ' _ k]
    simp only [fluctTerm, ← Matrix.mul_sum, ← Matrix.sum_mul]
    exact add_comm _ _

end Levels2
end Balaban
