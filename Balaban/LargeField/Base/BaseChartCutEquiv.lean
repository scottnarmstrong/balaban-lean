/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartCutLocal

/-!
# `O(N)` equivariance of the component square root

If an inner-product preserving linear map `T` of `Config ι N` intertwines two Gaussian forms
(`gaussForm e' H' ∘ T = T ∘ gaussForm e H`) and the first is positive definite in coordinates, then
`gaussSqrtMap e' H' (T u) = T (gaussSqrtMap e H u)` (`gaussSqrtMap_equivariant`).  The rotations of
the spins, with the centre rotated and the Hamiltonian commuting with the rotation, are such `T`
(P5 (S5)(i); LFR Lemma II.7.7 (e)).  The matrix core is `pdSqrtInv_conj`:
`pdSqrtInv (Q K Qᵀ) = Q (pdSqrtInv K) Qᵀ` for orthogonal `Q`.
-/

@[expose] public section

namespace Balaban.LargeField

open Matrix Balaban.Green MeasureTheory
open scoped MatrixOrder


theorem matAct_real_eq_mulVec {κ : Type*} [Fintype κ] (S : Matrix κ κ ℝ) (v : κ → ℝ) :
    matAct S v = S *ᵥ v := by
  funext x; simp [matAct, Matrix.mulVec, dotProduct]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem pdSqrtInv_conj {Q K : Matrix κ κ ℝ} (hQ : Q * Qᵀ = 1) (hQ' : Qᵀ * Q = 1)
    (hK : K.PosDef) : pdSqrtInv (Q * K * Qᵀ) = Q * pdSqrtInv K * Qᵀ := by
  symm
  refine pdSqrtInv_unique ?_ ?_
  · have h := (pdSqrtInv_posSemidef K).mul_mul_conjTranspose_same Q
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  · have hinv : (Q * K * Qᵀ)⁻¹ = Q * K⁻¹ * Qᵀ := by
      have hQi : Q⁻¹ = Qᵀ := Matrix.inv_eq_right_inv hQ
      have hQti : (Qᵀ)⁻¹ = Q := Matrix.inv_eq_right_inv (by simpa using hQ')
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hQi, hQti, Matrix.mul_assoc]
    rw [hinv]
    calc Q * pdSqrtInv K * Qᵀ * (Q * pdSqrtInv K * Qᵀ)
        = Q * pdSqrtInv K * (Qᵀ * Q) * pdSqrtInv K * Qᵀ := by simp only [Matrix.mul_assoc]
      _ = Q * (pdSqrtInv K * pdSqrtInv K) * Qᵀ := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * K⁻¹ * Qᵀ := by rw [pdSqrtInv_mul_self hK]

/-- A real matrix preserving the dot product has `Qᵀ Q = 1`. -/
theorem transpose_mul_self_of_dotProduct {Q : Matrix κ κ ℝ}
    (h : ∀ v w, (Q *ᵥ v) ⬝ᵥ (Q *ᵥ w) = v ⬝ᵥ w) : Qᵀ * Q = 1 := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, dotProduct_single_one, Matrix.one_apply] at this ⊢
  simpa [Matrix.mul_apply, dotProduct, Pi.single_apply, eq_comm, Matrix.col_apply] using this


section Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [DecidableEq ι] in
theorem cinner_eq_dotProduct_equivFun (u v : Config ι N) :
    cinner u v = ((configBasis ι N).equivFun u) ⬝ᵥ ((configBasis ι N).equivFun v) := by
  simp [cinner, configBasis, dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
    Finset.sum_sigma', mul_comm]

/-- **Equivariance of the square-root map**: if `T` preserves the inner product and intertwines the
forms (`gaussForm e' H' ∘ T = T ∘ gaussForm e H`), and the form `gaussForm e H` is positive
definite in coordinates, then `gaussSqrtMap e' H' (T u) = T (gaussSqrtMap e H u)`. -/
theorem gaussSqrtMap_equivariant (e e' : Config ι N) (H H' : Config ι N →ₗ[ℝ] Config ι N)
    (T : Config ι N →ₗ[ℝ] Config ι N) (hT : ∀ u v, cinner (T u) (T v) = cinner u v)
    (hH : ∀ u, gaussForm e' H' (T u) = T (gaussForm e H u))
    (hK : (LinearMap.toMatrix (configBasis ι N) (configBasis ι N) (gaussForm e H)).PosDef)
    (u : Config ι N) : gaussSqrtMap e' H' (T u) = T (gaussSqrtMap e H u) := by
  set B := configBasis ι N with hB
  set Q := LinearMap.toMatrix B B T with hQ
  set K := LinearMap.toMatrix B B (gaussForm e H) with hKdef
  set K' := LinearMap.toMatrix B B (gaussForm e' H') with hK'def
  have hcoordT (w : Config ι N) : B.equivFun (T w) = Q *ᵥ B.equivFun w := by
    simpa [Q] using (LinearMap.toMatrix_mulVec_repr B B T w).symm
  have hcoordF (w : Config ι N) : B.equivFun (gaussForm e H w) = K *ᵥ B.equivFun w := by
    simpa [K] using (LinearMap.toMatrix_mulVec_repr B B (gaussForm e H) w).symm
  have hcoordF' (w : Config ι N) : B.equivFun (gaussForm e' H' w) = K' *ᵥ B.equivFun w := by
    simpa [K'] using (LinearMap.toMatrix_mulVec_repr B B (gaussForm e' H') w).symm
  have hdot : ∀ v w : (Σ _ : ι, Fin N) → ℝ, (Q *ᵥ v) ⬝ᵥ (Q *ᵥ w) = v ⬝ᵥ w := by
    intro v w
    have := hT (B.equivFun.symm v) (B.equivFun.symm w)
    rw [cinner_eq_dotProduct_equivFun, cinner_eq_dotProduct_equivFun, hcoordT, hcoordT] at this
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this
  have hQ1 : Qᵀ * Q = 1 := transpose_mul_self_of_dotProduct hdot
  have hQ2 : Q * Qᵀ = 1 := mul_eq_one_comm.mp hQ1
  have hKQ : K' * Q = Q * K := by
    ext i j
    have := congrArg (fun z => B.equivFun z i) (hH (B.equivFun.symm (Pi.single j 1)))
    simp only [hcoordF', hcoordT, hcoordF, LinearEquiv.apply_symm_apply,
      Matrix.mulVec_single_one] at this
    exact this
  have hK'eq : K' = Q * K * Qᵀ := by
    calc K' = K' * (Q * Qᵀ) := by rw [hQ2, Matrix.mul_one]
      _ = (K' * Q) * Qᵀ := by rw [Matrix.mul_assoc]
      _ = Q * K * Qᵀ := by rw [hKQ]
  rw [gaussSqrtMap_eq_sqrtApply, gaussSqrtMap_eq_sqrtApply]
  change sqrtApply K' (T u) = T (sqrtApply K u)
  unfold sqrtApply
  simp only [← hB]
  apply B.equivFun.injective
  simp only [LinearEquiv.apply_symm_apply, hcoordT, matAct_real_eq_mulVec, hK'eq,
    pdSqrtInv_conj hQ2 hQ1 hK, Matrix.mulVec_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have : Qᵀ *ᵥ (Q *ᵥ B.equivFun u) = B.equivFun u := by rw [Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  rw [this]
  rw [Matrix.mulVec_mulVec]

end Config

end Balaban.LargeField
