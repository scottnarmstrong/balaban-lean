/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.Constrained

/-!
# The linearized Euler-Lagrange system from the response formulas

The formulas of Proposition 5.4 (`φ̇ = (G − Π) Ṡ`, `α̇ = [φ · G φ]⁻¹ φ · G Ṡ`, `G = H⁻¹`) solve the
linearized system `H φ̇ + α̇ φ = Ṡ`, `φ · φ̇ = 0` whenever `H` and `φ · G φ` are invertible. This is
the converse direction of `Balaban.Background.response_solve`; it lets the value of a quadratic form
at `φ̇` be computed from the system instead of from the formulas.
-/

@[expose] public section

open Matrix

namespace Balaban.RootFSpine

open Balaban.Multiscale

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem liftOp_mulVec_inv_self {Hm : Matrix ι ι ℂ} (hH : IsUnit Hm) (w : ι × Fin N → ℂ) :
    liftOp N Hm *ᵥ (liftOp N Hm⁻¹ *ᵥ w) = w := by
  rw [Matrix.mulVec_mulVec, ← liftOp_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hH), liftOp_one, Matrix.one_mulVec]

/-- **The response formulas solve the linearized system.** -/
theorem response_formula_solves {Hm : Matrix ι ι ℂ} (hH : IsUnit Hm) {φ : ι → Fin N → ℂ}
    (hM : IsUnit (constraintForm Hm⁻¹ φ)) (S : ι × Fin N → ℂ) :
    liftOp N Hm *ᵥ ((liftOp N Hm⁻¹ - constrainedOp Hm⁻¹ φ) *ᵥ S) +
        fieldMul φ *ᵥ ((constraintForm Hm⁻¹ φ)⁻¹ *ᵥ ((fieldMul φ)ᵀ *ᵥ (liftOp N Hm⁻¹ *ᵥ S))) = S ∧
      (fieldMul φ)ᵀ *ᵥ ((liftOp N Hm⁻¹ - constrainedOp Hm⁻¹ φ) *ᵥ S) = 0 := by
  set M := constraintForm Hm⁻¹ φ with hMdef
  set T := fieldMul φ with hT
  set Lg := liftOp N Hm⁻¹ with hLg
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM)
  have hMM' : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hM)
  have hPi : constrainedOp Hm⁻¹ φ = Lg * T * M⁻¹ * Tᵀ * Lg := rfl
  have hMe : M = Tᵀ * Lg * T := rfl
  constructor
  · rw [Matrix.sub_mulVec, Matrix.mulVec_sub, hPi]
    have h1 : liftOp N Hm *ᵥ (Lg *ᵥ S) = S := liftOp_mulVec_inv_self hH S
    have h2 : liftOp N Hm *ᵥ ((Lg * T * M⁻¹ * Tᵀ * Lg) *ᵥ S) =
        T *ᵥ (M⁻¹ *ᵥ (Tᵀ *ᵥ (Lg *ᵥ S))) := by
      have : (Lg * T * M⁻¹ * Tᵀ * Lg) *ᵥ S = Lg *ᵥ (T *ᵥ (M⁻¹ *ᵥ (Tᵀ *ᵥ (Lg *ᵥ S)))) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [this]
      exact liftOp_mulVec_inv_self hH _
    rw [h1, h2]
    abel
  · rw [Matrix.sub_mulVec, Matrix.mulVec_sub, hPi]
    have e : Tᵀ * (Lg * T * M⁻¹ * Tᵀ * Lg) = Tᵀ * Lg := by
      calc Tᵀ * (Lg * T * M⁻¹ * Tᵀ * Lg) = (Tᵀ * Lg * T) * M⁻¹ * Tᵀ * Lg := by
            simp only [Matrix.mul_assoc]
        _ = Tᵀ * Lg := by rw [← hMe, hMM, Matrix.one_mul]
    simp only [Matrix.mulVec_mulVec, e, sub_self]

end Balaban.RootFSpine
