/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.AgmonCore
import Mathlib.Tactic.Linarith

/-!
# The hard-spin constrained operator `Π` and its positivity (GREEN.md (1.8′), §4.5b (1))

For an operator `A` on a finite index type `ι` (later `A = G_D(α) = H_D(α)⁻¹` on `Ω₁`) and a field
`φ₀ : ι → ℂ^N` the constrained operator of (1.8′) is

`Π = A φ₀ [φ₀ · A φ₀]⁻¹ φ₀ · A`,

with the *bilinear* (non-conjugated) dot product `φ₀ · A φ₀` of GREEN.md §1.1.  Vector fields are
functions on `ι × Fin N`; the operator `A` acts on every component (`Balaban.Multiscale.liftOp`),
the multiplication `s ↦ (φ₀ᵢ s)ᵢ` is the matrix `Balaban.Multiscale.fieldMul φ₀ : ι × Fin N → ι`
and `φ₀ ·` is its (non-conjugated) transpose.  Thus

* `Balaban.Multiscale.constraintForm A φ₀ = (fieldMul φ₀)ᵀ (liftOp A) (fieldMul φ₀)` is `φ₀ · A φ₀`;
* `Balaban.Multiscale.constrainedOp A φ₀ = (liftOp A)(fieldMul φ₀)(constraintForm A φ₀)⁻¹
  (fieldMul φ₀)ᵀ (liftOp A)` is `Π`.

The matrix inverse is Mathlib's `Matrix.inv`; it is the genuine inverse whenever `constraintForm`
is invertible (`Balaban.Multiscale.constraintForm_isUnit` below, under the smallness hypotheses of
G-2(v)).

Main result (G-1(d)(1)): `Balaban.Multiscale.constrainedOp_posSemidef`: for real `φ₀` and a
positive semidefinite `A`, `Π` is positive semidefinite; for the Dirichlet operator
(`Balaban.Multiscale.dirichletGreen_posSemidef`, `Balaban.Multiscale.constrainedOp_dirichlet_posSemidef`)
this holds for real `α` with `|α| ≤ c₁ ℓ⁻² / 2`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset
open scoped ComplexOrder

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- `A` acting on each of the `N` components of a vector field on `ι`. -/
def liftOp (N : ℕ) (A : Matrix ι ι ℂ) : Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  fun p q => if p.2 = q.2 then A p.1 q.1 else 0

/-- The multiplication `s ↦ (φ₀ᵢ s)ᵢ` of a scalar field by the vector field `φ₀`. -/
def fieldMul (φ : ι → Fin N → ℂ) : Matrix (ι × Fin N) ι ℂ :=
  fun p y => if p.1 = y then φ y p.2 else 0

/-- `φ₀ · A φ₀`: the bilinear constraint form, `(φ₀ · A φ₀)(x, y) = ∑ᵢ φ₀ᵢ(x) A(x, y) φ₀ᵢ(y)`. -/
noncomputable def constraintForm (A : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) : Matrix ι ι ℂ :=
  (fieldMul φ)ᵀ * liftOp N A * fieldMul φ

/-- **The constrained operator** `Π = A φ₀ [φ₀ · A φ₀]⁻¹ φ₀ · A` of GREEN.md (1.8′). -/
noncomputable def constrainedOp (A : Matrix ι ι ℂ) (φ : ι → Fin N → ℂ) :
    Matrix (ι × Fin N) (ι × Fin N) ℂ :=
  liftOp N A * fieldMul φ * (constraintForm A φ)⁻¹ * (fieldMul φ)ᵀ * liftOp N A

omit [Fintype ι] [DecidableEq ι] in
theorem liftOp_conjTranspose (A : Matrix ι ι ℂ) : (liftOp N A)ᴴ = liftOp N Aᴴ := by
  ext p q
  rw [conjTranspose_apply]
  unfold liftOp
  by_cases h : p.2 = q.2
  · simp only [h, ↓reduceIte, conjTranspose_apply]
  · simp [h, Ne.symm h]

omit [Fintype ι] [DecidableEq ι] in
theorem liftOp_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : (liftOp N A).IsHermitian := by
  unfold IsHermitian
  rw [liftOp_conjTranspose, hA.eq]

omit [DecidableEq ι] in
theorem liftOp_mulVec (A : Matrix ι ι ℂ) (x : ι × Fin N → ℂ) (a : ι) (i : Fin N) :
    (liftOp N A *ᵥ x) (a, i) = (A *ᵥ fun b => x (b, i)) a := by
  simp only [mulVec, dotProduct, liftOp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

omit [DecidableEq ι] in
theorem liftOp_dotProduct_mulVec (A : Matrix ι ι ℂ) (x : ι × Fin N → ℂ) :
    star x ⬝ᵥ (liftOp N A *ᵥ x) =
      ∑ i : Fin N, star (fun a => x (a, i)) ⬝ᵥ (A *ᵥ fun a => x (a, i)) := by
  simp only [dotProduct, Fintype.sum_prod_type, liftOp_mulVec, Pi.star_apply]
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem liftOp_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : (liftOp N A).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (liftOp_isHermitian hA.isHermitian) fun x => ?_
  rw [liftOp_dotProduct_mulVec]
  exact Finset.sum_nonneg fun i _ => hA.dotProduct_mulVec_nonneg _

omit [Fintype ι] in
theorem fieldMul_conjTranspose {φ : ι → Fin N → ℂ} (hφ : ∀ x i, star (φ x i) = φ x i) :
    (fieldMul φ)ᴴ = (fieldMul φ)ᵀ := by
  ext y p
  simp only [conjTranspose_apply, transpose_apply, fieldMul]
  split_ifs
  · exact hφ _ _
  · simp

/-- **G-1(d)(1), abstract form.** For real `φ₀` and `A` positive semidefinite, `Π ⪰ 0`. -/
theorem constrainedOp_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {φ : ι → Fin N → ℂ}
    (hφ : ∀ x i, star (φ x i) = φ x i) : (constrainedOp A φ).PosSemidef := by
  have hL := liftOp_posSemidef (N := N) hA
  have hM : (constraintForm A φ).PosSemidef := by
    unfold constraintForm
    rw [← fieldMul_conjTranspose hφ]
    exact hL.conjTranspose_mul_mul_same _
  have hMi := hM.inv
  have key := hMi.mul_mul_conjTranspose_same (liftOp N A * fieldMul φ)
  have e : (liftOp N A * fieldMul φ)ᴴ = (fieldMul φ)ᵀ * liftOp N A := by
    rw [conjTranspose_mul, fieldMul_conjTranspose hφ, hL.isHermitian.eq]
  rw [e] at key
  simpa only [constrainedOp, Matrix.mul_assoc] using key

end Abstract

section Concrete

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)

theorem layerProjMatrix_transpose (j : ℕ) : (layerProjMatrix G j)ᵀ = layerProjMatrix G j := by
  ext x x'
  simp only [transpose_apply, layerProjMatrix]
  by_cases h : x ∈ G.layer j ∧ x' ∈ G.layer j
  · have h' : x' ∈ G.layer j ∧ x ∈ G.layer j := ⟨h.2, h.1⟩
    simp only [h, and_self, ↓reduceIte]
    exact blockProjMatrix_symm j x' x
  · have h' : ¬ (x' ∈ G.layer j ∧ x ∈ G.layer j) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [h, h', ↓reduceIte]

theorem avgMatrix_transpose (a : ℕ → ℝ) : (avgMatrix G a)ᵀ = avgMatrix G a := by
  unfold avgMatrix
  rw [transpose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [transpose_smul, layerProjMatrix_transpose]

theorem fullMatrix_transpose (a : ℕ → ℝ) (ν : ℝ) : (fullMatrix G a ν)ᵀ = fullMatrix G a ν := by
  unfold fullMatrix
  rw [transpose_add, avgMatrix_transpose]
  congr 1
  have := latticeLaplacian_isHermitian (d := d) (ℓ := N₀ * L ^ k) ν
  simpa [IsHermitian] using this

omit [NeZero N₀] [NeZero L] in
theorem restrictOp_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (Λ : Finset ι) : (Green.restrictOp A Λ)ᴴ = Green.restrictOp Aᴴ Λ := by
  ext x y
  simp [Green.restrictOp, conjTranspose_apply]

/-- `H_D(α)` is Hermitian for real `α`. -/
theorem dirichletOperator_isHermitian (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, star (α x) = α x) : (dirichletOperator G a ν α).IsHermitian := by
  unfold IsHermitian dirichletOperator
  rw [conjTranspose_add, restrictOp_conjTranspose]
  congr 1
  · congr 1
    ext x y
    simp only [conjTranspose_apply, map_apply]
    have := congrFun (congrFun (fullMatrix_transpose G a ν) y) x
    simp only [transpose_apply] at this
    rw [this]
    simp
  · ext x y
    simp [diagonal_apply, conjTranspose_apply]
    split_ifs <;> simp_all

/-- `H_D(α)` is positive semidefinite for real `α` with `|α| ≤ c₁ ℓ⁻² / 2` (G-1(a)). -/
theorem dirichletOperator_posSemidef (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (hreal : ∀ x, star (α x) = α x) : (dirichletOperator G a ν α).PosSemidef := by
  have hH := dirichletOperator_isHermitian G a ν α hreal
  have hc := dirichletOperator_isCoercive_min G hd hν ha α hα
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hγ : 0 ≤ coerciveConst d * (((L : ℝ) ^ k) ^ 2)⁻¹ :=
    mul_nonneg (coerciveConst_pos hd).le (inv_nonneg.2 (by positivity))
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  have hz : star (star x ⬝ᵥ dirichletOperator G a ν α *ᵥ x) =
      star x ⬝ᵥ dirichletOperator G a ν α *ᵥ x := hH.star_dotProduct_mulVec_comm x x
  have hre : 0 ≤ (star x ⬝ᵥ dirichletOperator G a ν α *ᵥ x).re := by
    have h1 := hc x
    have h2 : Green.reQuad (dirichletOperator G a ν α) x =
        (star x ⬝ᵥ dirichletOperator G a ν α *ᵥ x).re := rfl
    have h3 := Green.sqNorm_nonneg x
    nlinarith
  rw [Complex.nonneg_iff]
  refine ⟨hre, ?_⟩
  have := congrArg Complex.im hz
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-- The Green's function `G_D(α) = H_D(α)⁻¹` is positive semidefinite for real `α`. -/
theorem dirichletGreen_posSemidef (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (hreal : ∀ x, star (α x) = α x) : ((dirichletOperator G a ν α)⁻¹).PosSemidef :=
  (dirichletOperator_posSemidef G hd hν ha α hα hreal).inv

/-- **G-1(d)(1).** For real data (`α` real with `|α| ≤ c₁ ℓ⁻² / 2`, `φ₀` real) the constrained
operator `Π` of (1.8′) built from the Green's function `G_D(α)` is positive semidefinite; hence
`Q_k Π Q_k^* ⪰ 0` (`Balaban.Multiscale.sandwich_nonneg`). -/
theorem constrainedOp_dirichlet_posSemidef (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (hreal : ∀ x, star (α x) = α x) {N : ℕ} {φ : G.Ω 1 → Fin N → ℂ}
    (hφ : ∀ x i, star (φ x i) = φ x i) :
    (constrainedOp (dirichletOperator G a ν α)⁻¹ φ).PosSemidef :=
  constrainedOp_posSemidef (dirichletGreen_posSemidef G hd hν ha α hα hreal) hφ

end Concrete

end Balaban.Multiscale
