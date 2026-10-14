/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledFunctional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# I-4c (iv) for real data: positivity of `𝒜` is a theorem

For real data (`φ₀`, `α₀`, the block average `Q` real-valued) the operator
`𝒜 = a L⁻² Q*Q + Δ^{(k)}` (`covOp`) is Hermitian (`covOp_isHermitian`). Since `x + 𝒜` is invertible
for every `x ≥ 0` (`decCov_one_eq`), no eigenvalue of `𝒜` is `≤ 0`: `𝒜` is positive definite
(`covOp_posDef_of_real`). The hypothesis `PosDef` of `decCovSqrt_one_eq`, `decLog_one_eq` is thereby
discharged (`decCovSqrt_one_eq_real`, `decLog_one_eq_real`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix
open scoped ComplexOrder

section Hermitian

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem layerBlockMatrix_transpose (G : GeneratingSet d L N₀ K ϱ) (j m : ℕ) :
    (layerBlockMatrix G j m)ᵀ = layerBlockMatrix G j m := by
  ext x x'
  simp only [transpose_apply, layerBlockMatrix]
  by_cases h : x ∈ G.layer j ∧ x' ∈ G.layer j
  · have h' : x' ∈ G.layer j ∧ x ∈ G.layer j := ⟨h.2, h.1⟩
    simp only [h, and_self, ↓reduceIte]
    exact blockProjMatrix_symm m x' x
  · have h' : ¬ (x' ∈ G.layer j ∧ x ∈ G.layer j) := fun h' => h ⟨h'.2, h'.1⟩
    simp only [h, h', ↓reduceIte]

end Hermitian

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {δ : ℝ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

theorem xAvgMatrix_transpose (a : ℕ → ℝ) (s₁ s₂ : ℝ) :
    (xAvgMatrix G a s₁ s₂)ᵀ = xAvgMatrix G a s₁ s₂ := by
  unfold xAvgMatrix
  simp only [transpose_add, transpose_sum, transpose_smul, layerBlockMatrix_transpose]

theorem xDirichletOperator_isHermitian (x : ℝ) (hα : ∀ w, star (α w) = α w) :
    (xDirichletOperator G a aT x ν α).IsHermitian := by
  unfold IsHermitian xDirichletOperator
  rw [conjTranspose_add, restrictOp_conjTranspose]
  congr 1
  · congr 1
    ext p q
    simp only [conjTranspose_apply, map_apply]
    have hT : (xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν)ᵀ =
        xFullMatrix G a (xS1 (a k) x) (xS2 (a k) (aT / (L : ℝ) ^ 2) x) ν := by
      unfold xFullMatrix
      rw [transpose_add, xAvgMatrix_transpose]
      congr 1
      have := latticeLaplacian_isHermitian (d := d) (ℓ := N₁ * L ^ m₁ * L ^ (k + 1)) ν
      simpa [IsHermitian] using this
    have := congrFun (congrFun hT (q : _)) (p : _)
    simp only [transpose_apply] at this
    rw [this]
    simp
  · ext p q
    simp [diagonal_apply, conjTranspose_apply]
    split_ifs <;> simp_all

theorem xH0_isHermitian (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hα : ∀ w, star (α w) = α w) : (xH0 G a ν α).IsHermitian := by
  have D0 := hfam 0 le_rfl
  have hak : 0 < a k := by
    have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)
    linarith [this.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D0.st.haT1
    positivity
  have h1 := tendsto_xDirichlet (aT := aT) (ν := ν) hak hb α
  have h2 := (continuous_id.matrix_conjTranspose.tendsto _).comp h1
  have h3 : (fun x : ℝ => (xDirichletOperator G a aT x ν α)ᴴ) =
      fun x => xDirichletOperator G a aT x ν α := by
    funext x; exact xDirichletOperator_isHermitian x hα
  have h4 : Filter.Tendsto (fun x : ℝ => (xDirichletOperator G a aT x ν α)ᴴ) Filter.atTop
      (nhds (xH0 G a ν α)ᴴ) := h2
  rw [h3] at h4
  exact tendsto_nhds_unique h4 h1

section Constrained

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem constrainedOp_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {φ' : ι → Fin N → ℂ}
    (hφ : ∀ x i, star (φ' x i) = φ' x i) : (constrainedOp A φ').IsHermitian := by
  have hF := fieldMul_conjTranspose hφ
  have hF' : ((fieldMul φ')ᵀ)ᴴ = fieldMul φ' := by
    rw [← hF, conjTranspose_conjTranspose]
  have hL : (liftOp N A)ᴴ = liftOp N A := (liftOp_isHermitian hA).eq
  have hM : (constraintForm A φ')ᴴ = constraintForm A φ' := by
    unfold constraintForm
    rw [conjTranspose_mul, conjTranspose_mul, hF, hL, hF']
    simp only [Matrix.mul_assoc]
  have hMi : ((constraintForm A φ')⁻¹)ᴴ = (constraintForm A φ')⁻¹ := by
    rw [conjTranspose_nonsing_inv, hM]
  unfold IsHermitian constrainedOp
  simp only [conjTranspose_mul, hL, hF, hF', hMi]
  simp only [Matrix.mul_assoc]

end Constrained

theorem covOp_isHermitian (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hU : IsUnitLattice G Q P) (hα : ∀ w, star (α w) = α w)
    (hQ : ∀ b y, star (Q b y) = Q b y) (hφ : ∀ y i, star (φ y i) = φ y i) :
    (covOp G a aT ν α φ Q P).IsHermitian := by
  classical
  have hH0 := xH0_isHermitian hfam hα
  have hGi : (xH0 G a ν α)⁻¹.IsHermitian := hH0.inv
  have hCO := constrainedOp_isHermitian (N := N) (φ' := restrictField G φ) hGi
    (fun x i => hφ _ _)
  have hW : (liftOp N (xH0 G a ν α)⁻¹ - constrainedOp (xH0 G a ν α)⁻¹ (restrictField G φ)).IsHermitian :=
    (liftOp_isHermitian hGi).sub hCO
  have hR : (liftRect N Q)ᴴ = (liftRect N Q)ᵀ := by
    ext p q
    simp only [conjTranspose_apply, transpose_apply, liftRect]
    by_cases h : q.2 = p.2
    · simp [h, hQ]
    · simp [h]
  have hRR : ((liftRect N Q)ᵀ)ᴴ = liftRect N Q := by rw [← hR, conjTranspose_conjTranspose]
  have hmid : (liftRect N Q * (liftOp N (xH0 G a ν α)⁻¹ - constrainedOp (xH0 G a ν α)⁻¹
      (restrictField G φ)) * (liftRect N Q)ᵀ).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, hRR, hW.eq, hR]
    simp only [Matrix.mul_assoc]
  have hP : (liftOp N P).IsHermitian := by
    unfold IsHermitian; rw [liftOp_conjTranspose, hU.herm]
  unfold covOp
  have hsm : ∀ (c : ℝ) {M : Matrix (κι × Fin N) (κι × Fin N) ℂ}, M.IsHermitian →
      ((c : ℂ) • M).IsHermitian := fun c M hM => by
    unfold IsHermitian
    rw [conjTranspose_smul, hM.eq]; simp
  exact ((hsm _ isHermitian_one).add (hsm _ hP)).sub (hsm _ hmid)

/-- A Hermitian matrix `𝒜` with `x + 𝒜` invertible for all `x ≥ 0` is positive definite. -/
theorem posDef_of_hermitian_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hH : A.IsHermitian)
    (hu : ∀ x : ℝ, 0 ≤ x → IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)) : A.PosDef := by
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  by_contra hneg
  replace hneg := not_lt.1 hneg
  set lam := hH.eigenvalues i with hlam
  have hv : A *ᵥ (hH.eigenvectorBasis i) = (lam : ℂ) • (hH.eigenvectorBasis i : ι → ℂ) :=
    hH.mulVec_eigenvectorBasis i
  have hne : (hH.eigenvectorBasis i : ι → ℂ) ≠ 0 := by
    intro h0
    have := (hH.eigenvectorBasis).orthonormal.ne_zero i
    exact this (by ext; simpa using congrFun h0 _)
  have h0 : (((-lam : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) + A) *ᵥ (hH.eigenvectorBasis i : ι → ℂ) = 0 := by
    rw [add_mulVec, smul_mulVec, one_mulVec]
    have := hv
    simp only [] at this
    rw [this]
    push_cast
    rw [← add_smul]; simp
  have hu' := hu (-lam) (by linarith)
  rw [← Matrix.mulVec_injective_iff_isUnit] at hu'
  exact hne (hu' (by rw [h0, mulVec_zero]))

/-- **Positivity of `𝒜` for real data** (GREEN.md G-1(b), (d)(1), here as a consequence of
`decCov_one_eq`): `a L⁻² Q*Q + Δ^{(k)}` is positive definite. -/
theorem covOp_posDef_of_real (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) (hα : ∀ w, star (α w) = α w)
    (hQ : ∀ b y, star (Q b y) = Q b y) (hφr : ∀ y i, star (φ y i) = φ y i) :
    (covOp G a aT ν α φ Q P).PosDef :=
  posDef_of_hermitian_of_isUnit (covOp_isHermitian hfam hU.toIsUnitLattice hα hQ hφr)
    fun _ hx => (decCov_one_eq hfam hφ hδ hsm hU hx).1

/-- **I-4c (iv), square root, real data**: `C^{1/2}(1)` is the positive inverse square root of `𝒜`. -/
theorem decCovSqrt_one_eq_real (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) (hα : ∀ w, star (α w) = α w)
    (hQ : ∀ b y, star (Q b y) = Q b y) (hφr : ∀ y i, star (φ y i) = φ y i) :
    decCovSqrt G a aT ν α (fun _ => 1) φ Q P =
      invSqrtMat (covOp_posDef_of_real hfam hφ hδ hsm hU hα hQ hφr) :=
  decCovSqrt_one_eq hfam hφ hδ hsm hU _

/-- **I-4c (iv), logarithm, real data**: `𝕃(1) = log 𝒜`. -/
theorem decLog_one_eq_real (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hU : IsUnitLatticeB G Q P) (hα : ∀ w, star (α w) = α w)
    (hQ : ∀ b y, star (Q b y) = Q b y) (hφr : ∀ y i, star (φ y i) = φ y i) :
    decLog G a aT ν α (fun _ => 1) φ Q P =
      specFun (covOp_posDef_of_real hfam hφ hδ hsm hU hα hQ hφr).isHermitian
        (fun t => (Real.log t : ℂ)) :=
  decLog_one_eq hfam hφ hδ hsm hU (covOp_posDef_of_real hfam hφ hδ hsm hU hα hQ hφr)

end Balaban.Localization
