/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalValueBridge
public import Balaban.Green.FinalHessian

/-!
# The Dirichlet operator of the top layer is the fine Hamiltonian

A6-3 (a), step (P1d). For a generating set with `Ω_n = univ` for `1 ≤ n ≤ k` (the single layer `k`),
`fullMatrix G a ν = -Δ + ν + (a_k / L^{2k}) P` is the fine Hamiltonian of the unit lattice
(`Balaban.fineHamiltonian`) rescaled by `L^{-2k}`.
-/

@[expose] public section

open Matrix Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

namespace Balaban.RootFSpine

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The layer projection of the top layer, when the top layer is the whole torus. -/
theorem layerProjMatrix_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) :
    layerProjMatrix G k = blockProjMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k)) := by
  ext x x'
  have h : ∀ y, y ∈ G.layer k := fun y => by
    simp [GeneratingSet.layer, hΩ k hk le_rfl, G.top]
  simp [layerProjMatrix, h]

theorem layerProjMatrix_of_lt {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) {j : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    layerProjMatrix G j = 0 := by
  ext x x'
  have h : ∀ y, y ∉ G.layer j := fun y => by
    simp [GeneratingSet.layer, hΩ j hj hjk.le, hΩ (j + 1) (by omega) hjk]
  simp [layerProjMatrix, h]

/-- The multiscale averaging form of a single top layer. -/
theorem avgMatrix_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (a : ℕ → ℝ) :
    avgMatrix G a = (a k / ((L : ℝ) ^ k) ^ 2) •
      blockProjMatrix d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k)) := by
  unfold avgMatrix
  rw [Finset.sum_eq_single k]
  · rw [layerProjMatrix_top hΩ hk]
  · intro j hj hne
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
    rw [layerProjMatrix_of_lt hΩ hj1 (lt_of_le_of_ne hjk hne), smul_zero]
  · intro h; exact absurd (Finset.mem_Icc.2 ⟨hk, le_rfl⟩) h

/-- **The full matrix of the top layer is the rescaled fine Hamiltonian**:
`-Δ + ν + (a_k/L^{2k}) P = L^{-2k} · fineHamiltonian (ν L^{2k}) a_k`. -/
theorem fullMatrix_top {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (a : ℕ → ℝ) (ν : ℝ) :
    fullMatrix G a ν = (((L : ℝ) ^ k) ^ 2)⁻¹ •
      fineHamiltonian d (N₀ * L ^ k) (L ^ k) (N₀ * L ^ (k - k)) (ν * ((L : ℝ) ^ k) ^ 2) (a k) := by
  have hN : (((L : ℝ) ^ k) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold fullMatrix fineHamiltonian
  rw [avgMatrix_top hΩ hk]
  push_cast
  rw [mul_div_cancel_right₀ _ hN, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hN, one_smul]
  simp [div_eq_inv_mul]

section Transfer

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- When `Ω₁` is the whole torus, the subtype `Ω₁` is the torus. -/
def omegaEquiv (hmem : ∀ x, x ∈ G.Ω 1) : G.Ω 1 ≃ Torus d (N₀ * L ^ k) :=
  Equiv.subtypeUnivEquiv hmem

/-- A real field on the torus, as a complex field on `Ω₁`. -/
def cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    G.Ω 1 × Fin N → ℂ := fun p => ((v (omegaEquiv hmem p.1, p.2) : ℝ) : ℂ)

theorem dirichletOperator_zero_eq (hmem : ∀ x, x ∈ G.Ω 1) (a : ℕ → ℝ) (ν : ℝ) :
    dirichletOperator G a ν 0 =
      ((fullMatrix G a ν).map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem) := by
  unfold dirichletOperator Green.restrictOp
  ext x y
  simp [omegaEquiv]

theorem liftOp_submatrix_cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (A : Matrix (Torus d (N₀ * L ^ k))
    (Torus d (N₀ * L ^ k)) ℝ) (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    liftOp N ((A.map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem)) *ᵥ
        cplxLift hmem v = cplxLift hmem (spinLift N A *ᵥ v) := by
  funext ⟨x, i⟩
  simp only [cplxLift, liftOp, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, spinLift,
    Matrix.submatrix_apply, Matrix.map_apply, Complex.coe_algebraMap]
  push_cast
  refine (Equiv.sum_comp (omegaEquiv hmem) (fun y => ∑ x₂, (if i = x₂ then
    ((A ((omegaEquiv hmem) x) y : ℝ) : ℂ) else 0) * ((v (y, x₂) : ℝ) : ℂ))).trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

end Transfer

section SpinAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- For a constant unit direction `e`, `TᵀT = 1` (`T = fieldMul (constVec e)`). -/
theorem fieldMul_transpose_mul_self {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) :
    (fieldMul (fun (_ : ι) i => (e i : ℂ)))ᵀ * fieldMul (fun (_ : ι) i => (e i : ℂ)) = 1 := by
  have h2 : ∑ i, (e i : ℂ) * (e i : ℂ) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) he
    simpa [sq] using this
  ext y z
  simp only [Matrix.mul_apply, Matrix.transpose_apply, fieldMul, Fintype.sum_prod_type,
    Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz
    simp [h2]
  · simp [hyz, Ne.symm hyz]

/-- **The multiplier of the linearized system at a constant unit direction**: from
`H φ̇ + T α̇ = S`, `Tᵀ φ̇ = 0` and `TᵀT = 1`, `α̇ = Tᵀ S`. -/
theorem response_alpha_of_system {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1) {Hm : Matrix ι ι ℂ}
    {φd S : ι × Fin N → ℂ} {αd : ι → ℂ}
    (E1 : liftOp N Hm *ᵥ φd + fieldMul (fun (_ : ι) i => (e i : ℂ)) *ᵥ αd = S)
    (E2 : (fieldMul (fun (_ : ι) i => (e i : ℂ)))ᵀ *ᵥ φd = 0) :
    αd = (fieldMul (fun (_ : ι) i => (e i : ℂ)))ᵀ *ᵥ S := by
  set T := fieldMul (fun (_ : ι) i => (e i : ℂ)) with hT
  have hcomm : Tᵀ * liftOp N Hm = Hm * Tᵀ := by
    ext x ⟨y, j⟩
    simp [hT, Matrix.mul_apply, Matrix.transpose_apply, fieldMul, liftOp, Fintype.sum_prod_type,
      mul_comm]
  have h := congrArg (fun w => Tᵀ *ᵥ w) E1
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec φd Tᵀ (liftOp N Hm), hcomm,
    ← Matrix.mulVec_mulVec φd Hm Tᵀ, E2, Matrix.mulVec_zero, zero_add,
    Matrix.mulVec_mulVec αd Tᵀ T, hT, fieldMul_transpose_mul_self he, Matrix.one_mulVec] at h
  exact h

end SpinAlgebra

section Transfer2

variable {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}

/-- The pairing of two transported real fields is the transported dot product. -/
theorem pair_cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (v w : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    pair G (cplxLift hmem v) (cplxLift hmem w) = ((v ⬝ᵥ w : ℝ) : ℂ) := by
  unfold pair
  rw [dotProduct, Complex.ofReal_sum]
  exact Fintype.sum_equiv (Equiv.prodCongr (omegaEquiv hmem) (Equiv.refl _)) _ _ fun p => by
    simp [cplxLift]; rfl

/-- The projection onto the constant direction `e` acts on transported fields as `projH e`. -/
theorem fieldMul_fieldMul_transpose_cplxLift (hmem : ∀ x, x ∈ G.Ω 1) (e : Fin N → ℝ)
    (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    fieldMul (fun (_ : G.Ω 1) i => (e i : ℂ)) *ᵥ ((fieldMul (fun (_ : G.Ω 1) i => (e i : ℂ)))ᵀ *ᵥ
      cplxLift hmem v) = cplxLift hmem (projH (ι := Torus d (N₀ * L ^ k)) e *ᵥ v) := by
  funext ⟨x, i⟩
  rw [fieldMul_mulVec, fieldMul_transpose_mulVec]
  simp only [cplxLift, projH, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [apply_ite Complex.ofReal, ite_mul, Finset.sum_ite_eq]
  ring

/-- `L^{-2k}`-rescaled fine Hamiltonians are positive definite. -/
theorem fullMatrix_top_posDef {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (hd : 0 < d) (a : ℕ → ℝ)
    (ha : 0 < a k) {ν : ℝ} (hν : 0 ≤ ν) : (fullMatrix G a ν).PosDef := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hN : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by positivity
  rw [fullMatrix_top hΩ hk]
  refine Matrix.PosDef.smul ?_ (inv_pos.2 hN)
  exact fineHamiltonian_posDef (by rw [Nat.mul_comm]; simp)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k) hd (mul_nonneg hν hN.le) ha

theorem fullMatrix_mul_inv {G : GeneratingSet d L N₀ k ϱ}
    (hΩ : ∀ n, 1 ≤ n → n ≤ k → G.Ω n = Finset.univ) (hk : 1 ≤ k) (hd : 0 < d) (a : ℕ → ℝ)
    (ha : 0 < a k) {ν : ℝ} (hν : 0 ≤ ν) : fullMatrix G a ν * (fullMatrix G a ν)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1
    (fullMatrix_top_posDef hΩ hk hd a ha hν).isUnit)

/-- The inverse Dirichlet operator acts on transported fields as the inverse real matrix. -/
theorem liftOp_inv_cplxLift {G : GeneratingSet d L N₀ k ϱ} {N : ℕ}
    (hmem : ∀ x, x ∈ G.Ω 1) {Hr : Matrix (Torus d (N₀ * L ^ k)) (Torus d (N₀ * L ^ k)) ℝ}
    (hHr : Hr * Hr⁻¹ = 1)
    (hHc : IsUnit ((Hr.map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem)))
    (v : Torus d (N₀ * L ^ k) × Fin N → ℝ) :
    liftOp N (((Hr.map (algebraMap ℝ ℂ)).submatrix (omegaEquiv hmem) (omegaEquiv hmem))⁻¹) *ᵥ
        cplxLift hmem v = cplxLift hmem (spinLift N Hr⁻¹ *ᵥ v) := by
  have h1 := liftOp_submatrix_cplxLift hmem Hr (spinLift N Hr⁻¹ *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← spinLift_mul, hHr, spinLift_one, Matrix.one_mulVec] at h1
  rw [← h1]
  exact Balaban.Background.liftOp_inv_mulVec hHc _

end Transfer2

end Balaban.RootFSpine
