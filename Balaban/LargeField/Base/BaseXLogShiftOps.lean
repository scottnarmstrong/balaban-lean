/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXSqrt
public import Balaban.LargeField.Base.BaseResolventRange
public import Balaban.LargeField.Base.BaseResolventAbs
public import Balaban.Localization.DecCovCutSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Operator-norm tools for the shifted logarithm of the base covariance

Elementary `ℓ²` operator-norm estimates, in the norm `Matrix.Norms.L2Operator`, used for the
second-order large-`x` expansion of the first step's decoupled covariance (`BaseXLogShift`):

* `l2_opNorm_le_of_rowcol`: the Schur test, `‖A‖ ≤ √(r c)` from row sums `≤ r` and column sums
  `≤ c`;
* `norm_entry_le_l2_opNorm`: an entry is at most the operator norm;
* `l2_opNorm_fieldMul_le`, `l2_opNorm_fieldMul_transpose_le`, `l2_opNorm_liftOp_le`: the field
  multiplication `φ₀ ·`, its transpose and the componentwise lift;
* `opNorm_cutOperator_le`: a cut Dirichlet operator of the first step has norm at most
  `ν + 4 d + 3`;
* `OffDiag`, `opNorm_commK_le`, `opNorm_comm_chi_le`: the commutators `K(φ₀) = (φ₀ ·) H - H (φ₀ ·)`
  and `[χ, H]` are bounded by the off-diagonal row and column sums of `H` (no mass enters);
* `constrained_pi_identity`: the algebraic identity
  `Ĝ φ₀ M⁻¹ N = Ĝ Q - Ĝ φ₀ M⁻¹ K Ĝ (1 - Q)`, `Q = φ₀ (φ₀·φ₀)⁻¹ φ₀ᵀ`, for `M = φ₀ᵀ φ₀ - K Ĝ φ₀` and
  `N = φ₀ᵀ - K Ĝ`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Green Balaban.Multiscale Balaban.Localization
open scoped Matrix.Norms.L2Operator

section Schur

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- **The Schur test.**  If the row sums of `‖A y z‖` are at most `r` and the column sums at most
`c`, then `‖A‖ ≤ √(r c)` in the `ℓ²` operator norm. -/
theorem l2_opNorm_le_of_rowcol (A : Matrix m n ℂ) {r c : ℝ} (hr0 : 0 ≤ r) (hc0 : 0 ≤ c)
    (hr : ∀ y, ∑ z, ‖A y z‖ ≤ r) (hc : ∀ z, ∑ y, ‖A y z‖ ≤ c) : ‖A‖ ≤ Real.sqrt (r * c) := by
  refine l2_opNorm_le_of_sqNorm A (Real.sqrt_nonneg _) fun v => ?_
  rw [Real.sq_sqrt (mul_nonneg hr0 hc0)]
  unfold sqNorm
  have h1 : ∀ y, ‖(A *ᵥ v) y‖ ^ 2 ≤ r * ∑ z, ‖A y z‖ * ‖v z‖ ^ 2 := by
    intro y
    have hn : ‖(A *ᵥ v) y‖ ≤ ∑ z, ‖A y z‖ * ‖v z‖ := by
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_mul]
      exact le_rfl
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun z => Real.sqrt ‖A y z‖)
      (fun z => Real.sqrt ‖A y z‖ * ‖v z‖)
    have e1 : ∀ z, Real.sqrt ‖A y z‖ * (Real.sqrt ‖A y z‖ * ‖v z‖) = ‖A y z‖ * ‖v z‖ := by
      intro z
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ z, Real.sqrt ‖A y z‖ ^ 2 = ‖A y z‖ := fun z => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ z, (Real.sqrt ‖A y z‖ * ‖v z‖) ^ 2 = ‖A y z‖ * ‖v z‖ ^ 2 := by
      intro z; rw [mul_pow, e2]
    simp only [e1, e2, e3] at hcs
    calc ‖(A *ᵥ v) y‖ ^ 2 ≤ (∑ z, ‖A y z‖ * ‖v z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ (∑ z, ‖A y z‖) * ∑ z, ‖A y z‖ * ‖v z‖ ^ 2 := hcs
      _ ≤ r * ∑ z, ‖A y z‖ * ‖v z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hr y) (Finset.sum_nonneg fun _ _ => by positivity)
  calc ∑ y, ‖(A *ᵥ v) y‖ ^ 2 ≤ ∑ y, r * ∑ z, ‖A y z‖ * ‖v z‖ ^ 2 :=
        Finset.sum_le_sum fun y _ => h1 y
    _ = r * ∑ z, (∑ y, ‖A y z‖) * ‖v z‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul]
    _ ≤ r * ∑ z, c * ‖v z‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => ?_) hr0
        exact mul_le_mul_of_nonneg_right (hc z) (sq_nonneg _)
    _ = r * c * ∑ z, ‖v z‖ ^ 2 := by rw [← Finset.mul_sum]; ring

end Schur

section Entry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **An entry is at most the operator norm.** -/
theorem norm_entry_le_l2_opNorm (M : Matrix ι ι ℂ) (y z : ι) : ‖M y z‖ ≤ ‖M‖ := by
  have h1 := norm_sq_entry_le_sqNorm M y z
  have h2 := sqNorm_mulVec_le_opNorm M (Pi.single z 1 : ι → ℂ)
  rw [sqNorm_single, mul_one] at h2
  exact le_of_sq_le_sq (h1.trans h2) (norm_nonneg _)

end Entry

section FieldNorms

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- Multiplication by the field `φ` has `ℓ²` norm at most `c`. -/
theorem l2_opNorm_fieldMul_le (φ : ι → Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (hφ : ∀ y, vn (φ y) ≤ c) :
    ‖fieldMul φ‖ ≤ c := by
  refine l2_opNorm_le_of_sqNorm _ hc fun v => ?_
  unfold sqNorm
  rw [Fintype.sum_prod_type]
  have : ∀ y, ∑ i, ‖(fieldMul φ *ᵥ v) (y, i)‖ ^ 2 = vn (φ y) ^ 2 * ‖v y‖ ^ 2 := by
    intro y
    rw [vn_sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fieldMul_mulVec, norm_mul, mul_pow]
  simp only [this]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have := pow_le_pow_left₀ (vn_nonneg _) (hφ y) 2
  nlinarith [sq_nonneg ‖v y‖]

/-- The transpose of the multiplication by `φ` has `ℓ²` norm at most `c`. -/
theorem l2_opNorm_fieldMul_transpose_le (φ : ι → Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hφ : ∀ y, vn (φ y) ≤ c) : ‖(fieldMul φ)ᵀ‖ ≤ c := by
  refine l2_opNorm_le_of_sqNorm _ hc fun w => ?_
  unfold sqNorm
  have h1 : ∀ y, ‖((fieldMul φ)ᵀ *ᵥ w) y‖ ^ 2 ≤ vn (φ y) ^ 2 * ∑ i, ‖w (y, i)‖ ^ 2 := by
    intro y
    rw [fieldMul_transpose_mulVec, vn_sq]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖φ y i‖)
      (fun i => ‖w (y, i)‖)
    calc ‖∑ i, φ y i * w (y, i)‖ ^ 2 ≤ (∑ i, ‖φ y i * w (y, i)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ = (∑ i, ‖φ y i‖ * ‖w (y, i)‖) ^ 2 := by simp only [norm_mul]
      _ ≤ _ := hcs
  calc ∑ y, ‖((fieldMul φ)ᵀ *ᵥ w) y‖ ^ 2 ≤ ∑ y, vn (φ y) ^ 2 * ∑ i, ‖w (y, i)‖ ^ 2 :=
        Finset.sum_le_sum fun y _ => h1 y
    _ ≤ ∑ y, c ^ 2 * ∑ i, ‖w (y, i)‖ ^ 2 := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right ?_
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        exact pow_le_pow_left₀ (vn_nonneg _) (hφ y) 2
    _ = c ^ 2 * ∑ p : ι × Fin N, ‖w p‖ ^ 2 := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type]

/-- The componentwise lift does not increase the `ℓ²` operator norm. -/
theorem l2_opNorm_liftOp_le (A : Matrix ι ι ℂ) : ‖liftOp N A‖ ≤ ‖A‖ := by
  refine l2_opNorm_le_of_sqNorm _ (norm_nonneg _) fun w => ?_
  unfold sqNorm
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := sqNorm_mulVec_le_opNorm A (fun b => w (b, i))
  unfold sqNorm at h
  calc ∑ y, ‖(liftOp N A *ᵥ w) (y, i)‖ ^ 2 = ∑ y, ‖(A *ᵥ fun b => w (b, i)) y‖ ^ 2 := by
        simp only [liftOp_mulVec]
    _ ≤ _ := h

end FieldNorms

section Alg

variable {A V : Type*} [Fintype A] [Fintype V] [DecidableEq A] [DecidableEq V]

/-- **The algebraic identity of the constrained correction.**  Let `M = φ₀ᵀ φ₀ - K Ĝ φ₀`,
`N = φ₀ᵀ - K Ĝ`, `D = φ₀ᵀ φ₀` with right inverse `D'`, `Q = φ₀ D' φ₀ᵀ`.  If `M` is invertible
then `Ĝ φ₀ M⁻¹ N = Ĝ Q - Ĝ φ₀ M⁻¹ K Ĝ (1 - Q)`. -/
theorem constrained_pi_identity (F : Matrix V A ℂ) (K : Matrix A V ℂ) (Gl : Matrix V V ℂ)
    (D Dinv : Matrix A A ℂ) (hD : F.transpose * F = D) (hDi : D * Dinv = 1)
    (hM : (F.transpose * F - K * Gl * F)⁻¹ * (F.transpose * F - K * Gl * F) = 1) :
    Gl * F * (F.transpose * F - K * Gl * F)⁻¹ * (F.transpose - K * Gl) =
      Gl * (F * Dinv * F.transpose) -
        Gl * F * (F.transpose * F - K * Gl * F)⁻¹ * K * Gl * (1 - F * Dinv * F.transpose) := by
  set M := F.transpose * F - K * Gl * F with hMdef
  have h1 : M * (Dinv * F.transpose) = F.transpose - K * Gl * (F * Dinv * F.transpose) := by
    have e1 : F.transpose * F * (Dinv * F.transpose) = F.transpose := by
      rw [hD, ← Matrix.mul_assoc, hDi, Matrix.one_mul]
    calc M * (Dinv * F.transpose) = F.transpose * F * (Dinv * F.transpose) -
          K * Gl * F * (Dinv * F.transpose) := by rw [hMdef, Matrix.sub_mul]
      _ = _ := by rw [e1]; simp only [Matrix.mul_assoc]
  have h2 : M⁻¹ * (F.transpose - K * Gl) = Dinv * F.transpose -
      M⁻¹ * K * Gl * (1 - F * Dinv * F.transpose) := by
    have : F.transpose - K * Gl = M * (Dinv * F.transpose) -
        K * Gl * (1 - F * Dinv * F.transpose) := by
      rw [h1]
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [this, Matrix.mul_sub, ← Matrix.mul_assoc M⁻¹ M, hM, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  calc Gl * F * M⁻¹ * (F.transpose - K * Gl) = Gl * F * (M⁻¹ * (F.transpose - K * Gl)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h2, Matrix.mul_sub]
        simp only [Matrix.mul_assoc]

end Alg

section Cut

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)

theorem cutOperator_apply (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (FineBond d L N₀)) (α : G.Ω 1 → ℂ)
    (z y : G.Ω 1) :
    cutOperator G a ν cut α z y =
      ((cutFullMatrix G a ν cut z y : ℝ) : ℂ) + (if z = y then α z else 0) := by
  simp [cutOperator, Green.restrictOp, Matrix.diagonal_apply, Matrix.add_apply]

theorem cutOperator_symm (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (FineBond d L N₀)) (α : G.Ω 1 → ℂ)
    (z y : G.Ω 1) : cutOperator G a ν cut α z y = cutOperator G a ν cut α y z := by
  rw [cutOperator_apply, cutOperator_apply, cutFull_symm G a ν cut (z : Torus d _) y]
  have : (if z = y then α z else 0) = if y = z then α y else 0 := by
    by_cases h : z = y
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this]

/-- **The `ℓ²` operator norm of a cut Dirichlet operator at level one.** -/
theorem opNorm_cutOperator_le (cut : Finset (FineBond d L N₀)) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights 1 a) {ν : ℝ} (hν : 0 ≤ ν) {α : G.Ω 1 → ℂ}
    (hα : ∀ z, ‖α z‖ ≤ 1) : ‖cutOperator G a ν cut α‖ ≤ ν + 4 * d + 3 := by
  classical
  have hr : ∀ z : G.Ω 1, ∑ y, ‖cutOperator G a ν cut α z y‖ ≤ ν + 4 * d + 3 := by
    intro z
    have h1 := sum_norm_cutFull_row_le_cut G cut ha hν z
    have h2 : ∑ y : G.Ω 1, ‖(if z = y then α z else 0)‖ ≤ 1 := by
      rw [Finset.sum_eq_single z]
      · simpa using hα z
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    calc ∑ y, ‖cutOperator G a ν cut α z y‖
        ≤ ∑ y : G.Ω 1, (|cutFullMatrix G a ν cut z y| + ‖(if z = y then α z else 0)‖) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [cutOperator_apply]
          refine (norm_add_le _ _).trans ?_
          rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith
  have hr0 : 0 ≤ ν + 4 * d + 3 := by positivity
  have := l2_opNorm_le_of_rowcol (cutOperator G a ν cut α) hr0 hr0 hr
    (fun y => by simpa only [cutOperator_symm G a ν cut α] using hr y)
  rwa [Real.sqrt_mul_self hr0] at this

/-- The off-diagonal entries of the cut matrix do not depend on the mass. -/
theorem cutFull_offdiag_mass (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (FineBond d L N₀))
    {x y : Torus d (N₀ * L ^ 1)} (h : x ≠ y) :
    cutFullMatrix G a ν cut x y = cutFullMatrix G a 0 cut x y := by
  rw [cutFullMatrix_eq, cutFullMatrix_eq]
  simp [Matrix.add_apply, Matrix.smul_apply, h]

/-- **Off-diagonal row and column sums of the first step's Dirichlet operator**: at most
`4 d + 2`, for every mass and every potential. -/
theorem dirichlet_offdiag_row_le {a : ℕ → ℝ} (ha : IsAdmissibleWeights 1 a) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (z : G.Ω 1) :
    ∑ y : G.Ω 1, (if y = z then 0 else ‖dirichletOperator G a ν α z y‖) ≤ 4 * d + 2 := by
  classical
  have h1 := sum_norm_cutFull_row_le_cut G ∅ ha (le_refl (0 : ℝ)) z
  calc ∑ y : G.Ω 1, (if y = z then 0 else ‖dirichletOperator G a ν α z y‖)
      ≤ ∑ y : G.Ω 1, |cutFullMatrix G a 0 ∅ z y| := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases h : y = z
        · simp [h]
        · have hne : z ≠ y := fun hh => h hh.symm
          simp only [h, ↓reduceIte]
          rw [← cutOperator_empty, cutOperator_apply]
          simp only [hne, ↓reduceIte, add_zero]
          rw [Complex.norm_real, Real.norm_eq_abs,
            cutFull_offdiag_mass G a ν ∅ (fun hh => hne (Subtype.ext hh))]
      _ ≤ _ := by linarith

theorem dirichlet_offdiag_col_le {a : ℕ → ℝ} (ha : IsAdmissibleWeights 1 a) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (y : G.Ω 1) :
    ∑ z : G.Ω 1, (if y = z then 0 else ‖dirichletOperator G a ν α z y‖) ≤ 4 * d + 2 := by
  classical
  have := dirichlet_offdiag_row_le G ha ν α y
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) this
  rw [← cutOperator_empty, cutOperator_symm G a ν ∅ α z y]
  by_cases h : y = z <;> simp [h, eq_comm]

end Cut

section Comm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The commutator `K(φ₀)` is bounded by the off-diagonal sums of `H`.**  If the off-diagonal
row and column sums of `H` are at most `P` and `‖φ₀(y)_i‖ ≤ 3/2`, then
`‖K(φ₀)‖ ≤ 3 P √N`. -/
theorem opNorm_commK_le (H : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) {P : ℝ} (hP : 0 ≤ P)
    (hr : ∀ z, ∑ y, (if y = z then 0 else ‖H z y‖) ≤ P)
    (hc : ∀ y, ∑ z, (if y = z then 0 else ‖H z y‖) ≤ P)
    (hφ : ∀ y i, ‖φ y i‖ ≤ 3 / 2) : ‖commK H φ‖ ≤ Real.sqrt ((3 * N * P) * (3 * P)) := by
  have hd : ∀ z y i, ‖H z y * (φ z i - φ y i)‖ ≤ 3 * (if y = z then 0 else ‖H z y‖) := by
    intro z y i
    by_cases h : y = z
    · subst h; simp
    · simp only [h, ↓reduceIte]
      rw [norm_mul]
      have := (norm_sub_le (φ z i) (φ y i)).trans (add_le_add (hφ z i) (hφ y i))
      nlinarith [norm_nonneg (H z y), norm_nonneg (φ z i - φ y i)]
  refine l2_opNorm_le_of_rowcol _ (by positivity) (by positivity) (fun z => ?_) (fun p => ?_)
  · rw [Fintype.sum_prod_type]
    simp only [Localization.commK_apply]
    calc ∑ y, ∑ i, ‖H z y * (φ z i - φ y i)‖ ≤ ∑ y, ∑ _i : Fin N,
          3 * (if y = z then 0 else ‖H z y‖) :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun i _ => hd z y i
      _ = (3 * N) * ∑ y, (if y = z then 0 else ‖H z y‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ (3 * N) * P := mul_le_mul_of_nonneg_left (hr z) (by positivity)
  · obtain ⟨y, i⟩ := p
    simp only [Localization.commK_apply]
    calc ∑ z, ‖H z y * (φ z i - φ y i)‖ ≤ ∑ z, 3 * (if y = z then 0 else ‖H z y‖) :=
          Finset.sum_le_sum fun z _ => hd z y i
      _ = 3 * ∑ z, (if y = z then 0 else ‖H z y‖) := by rw [Finset.mul_sum]
      _ ≤ 3 * P := mul_le_mul_of_nonneg_left (hc y) (by norm_num)

/-- **The commutator `[χ, H]` with a multiplier of modulus at most one** is bounded by the
off-diagonal sums of `H`. -/
theorem opNorm_comm_le (H : Matrix ι ι ℂ) (χ : ι → ℂ) (hχ : ∀ y, ‖χ y‖ ≤ 1) {P : ℝ} (hP : 0 ≤ P)
    (hr : ∀ z, ∑ y, (if y = z then 0 else ‖H z y‖) ≤ P)
    (hc : ∀ y, ∑ z, (if y = z then 0 else ‖H z y‖) ≤ P) :
    ‖(Matrix.diagonal χ * H - H * Matrix.diagonal χ)‖ ≤ 2 * P := by
  have hd : ∀ z y, ‖(Matrix.diagonal χ * H - H * Matrix.diagonal χ) z y‖ ≤
      2 * (if y = z then 0 else ‖H z y‖) := by
    intro z y
    rw [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h : y = z
    · subst h; rw [mul_comm (χ y) (H y y)]; simp
    · simp only [h, ↓reduceIte]
      calc ‖χ z * H z y - H z y * χ y‖ = ‖(χ z - χ y) * H z y‖ := by ring_nf
        _ ≤ ‖χ z - χ y‖ * ‖H z y‖ := norm_mul_le _ _
        _ ≤ 2 * ‖H z y‖ := by
            have := (norm_sub_le (χ z) (χ y)).trans (add_le_add (hχ z) (hχ y))
            nlinarith [norm_nonneg (H z y), norm_nonneg (χ z - χ y)]
  have := l2_opNorm_le_of_rowcol (Matrix.diagonal χ * H - H * Matrix.diagonal χ)
    (by positivity : 0 ≤ 2 * P) (by positivity : 0 ≤ 2 * P)
    (fun z => ?_) (fun y => ?_)
  · rwa [Real.sqrt_mul_self (by positivity)] at this
  · calc _ ≤ ∑ y, 2 * (if y = z then 0 else ‖H z y‖) := Finset.sum_le_sum fun y _ => hd z y
      _ = 2 * ∑ y, (if y = z then 0 else ‖H z y‖) := by rw [Finset.mul_sum]
      _ ≤ 2 * P := mul_le_mul_of_nonneg_left (hr z) (by norm_num)
  · calc _ ≤ ∑ z, 2 * (if y = z then 0 else ‖H z y‖) :=
          Finset.sum_le_sum fun z _ => hd z y
      _ = 2 * ∑ z, (if y = z then 0 else ‖H z y‖) := by rw [Finset.mul_sum]
      _ ≤ 2 * P := mul_le_mul_of_nonneg_left (hc y) (by norm_num)

end Comm

end Balaban.LargeField.Base
