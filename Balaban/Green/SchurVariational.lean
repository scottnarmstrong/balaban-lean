/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Gaussian.Schur
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variational form of the block-spin operator

Item 3 of brief W2b, generic part (GREEN.md G-6(a); P4 (5.12)-(5.13)). For real matrices with
`M = A + a QᵀQ` positive definite (`blockSpinPrecision`) and `Δ = blockSpinOperator A Q a`
(`Balaban/Gaussian/Schur.lean`), the Schur functional
`F ψ φ = a ‖ψ - Q φ‖² + φᵀ A φ` satisfies

* `Balaban.schurFunctional_sub_eq`: `F ψ φ - ψᵀ Δ ψ = (φ - φ*)ᵀ M (φ - φ*)` with
  `φ* = a M⁻¹ Qᵀ ψ`;
* `Balaban.blockSpinOperator_form_le`: `ψᵀ Δ ψ ≤ F ψ φ` for every `φ`;
* `Balaban.blockSpinOperator_form_attained`: `F ψ φ* = ψᵀ Δ ψ`;

that is, `ψᵀ Δ ψ = min_φ F ψ φ`.
-/

@[expose] public section

namespace Balaban

open Matrix

section Variational

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The functional `F ψ φ = a ‖ψ - Q φ‖² + φᵀ A φ` whose minimum over `φ` is `ψᵀ Δ ψ`. -/
def schurFunctional (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) (ψ : κ → ℝ) (φ : ι → ℝ) : ℝ :=
  a * ((ψ - Q *ᵥ φ) ⬝ᵥ (ψ - Q *ᵥ φ)) + φ ⬝ᵥ A *ᵥ φ

omit [DecidableEq ι] [DecidableEq κ] in
theorem schurFunctional_eq (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) (ψ : κ → ℝ)
    (φ : ι → ℝ) :
    schurFunctional A Q a ψ φ =
      a * (ψ ⬝ᵥ ψ) - 2 * a * ((Qᵀ *ᵥ ψ) ⬝ᵥ φ) + φ ⬝ᵥ blockSpinPrecision A Q a *ᵥ φ := by
  have h1 : ψ ⬝ᵥ Q *ᵥ φ = (Qᵀ *ᵥ ψ) ⬝ᵥ φ := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have h2 : (Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ) = φ ⬝ᵥ (Qᵀ * Q) *ᵥ φ := by
    rw [← Matrix.mulVec_mulVec, dotProduct_comm φ, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have h3 : (ψ - Q *ᵥ φ) ⬝ᵥ (ψ - Q *ᵥ φ) =
      ψ ⬝ᵥ ψ - 2 * (ψ ⬝ᵥ Q *ᵥ φ) + (Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm (Q *ᵥ φ) ψ]
    ring
  unfold schurFunctional blockSpinPrecision
  rw [h3, h1, h2, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

theorem schurFunctional_sub_eq {A : Matrix ι ι ℝ} {Q : Matrix κ ι ℝ} {a : ℝ}
    (hM : (blockSpinPrecision A Q a).PosDef) (ψ : κ → ℝ) (φ : ι → ℝ) :
    schurFunctional A Q a ψ φ - ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ =
      (φ - a • ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ))) ⬝ᵥ
        blockSpinPrecision A Q a *ᵥ (φ - a • ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ))) := by
  set M := blockSpinPrecision A Q a with hMdef
  set b : ι → ℝ := Qᵀ *ᵥ ψ with hb
  have hMs : Mᵀ = M := by
    have := hM.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM.isUnit
  have hMMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  have hMi : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMs]
  set φs : ι → ℝ := a • (M⁻¹ *ᵥ b) with hφs
  have hMφs : M *ᵥ φs = a • b := by
    rw [hφs, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMMi, Matrix.one_mulVec]
  have hb' : ψ ᵥ* Q = b := by rw [hb, Matrix.mulVec_transpose]
  have hD : ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ = a * (ψ ⬝ᵥ ψ) - a ^ 2 * (b ⬝ᵥ M⁻¹ *ᵥ b) := by
    unfold blockSpinOperator
    rw [← hMdef, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.smul_mulVec,
      dotProduct_smul, dotProduct_smul, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, hb']
    simp only [smul_eq_mul]
  rw [schurFunctional_eq, hD, ← hMdef, ← hb]
  have e1 : φ ⬝ᵥ M *ᵥ φs = a * (φ ⬝ᵥ b) := by rw [hMφs, dotProduct_smul, smul_eq_mul]
  have e2 : φs ⬝ᵥ M *ᵥ φ = a * (b ⬝ᵥ φ) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMs, hMφs, smul_dotProduct,
      smul_eq_mul]
  have e3 : φs ⬝ᵥ M *ᵥ φs = a ^ 2 * (b ⬝ᵥ M⁻¹ *ᵥ b) := by
    rw [hMφs, dotProduct_smul, hφs, smul_dotProduct, smul_eq_mul, smul_eq_mul, dotProduct_comm]
    ring
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
  rw [dotProduct_comm b φ] at e2 ⊢
  linarith

omit [DecidableEq ι] in
theorem dotProduct_mulVec_nonneg_of_posDef {M : Matrix ι ι ℝ} (hM : M.PosDef) (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ M *ᵥ v := by
  by_cases h : v = 0
  · simp [h]
  · have := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 h
    simpa using this.le

/-- **Variational form of the block-spin operator.** If `M = A + a QᵀQ` is positive definite, then
`ψᵀ Δ ψ = min_φ [a ‖ψ - Q φ‖² + φᵀ A φ]`: `Δ`-form is a lower bound for every `φ`. -/
theorem blockSpinOperator_form_le {A : Matrix ι ι ℝ} {Q : Matrix κ ι ℝ} {a : ℝ}
    (hM : (blockSpinPrecision A Q a).PosDef) (ψ : κ → ℝ) (φ : ι → ℝ) :
    ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ ≤ schurFunctional A Q a ψ φ := by
  have := schurFunctional_sub_eq hM ψ φ
  have h0 := dotProduct_mulVec_nonneg_of_posDef hM
    (φ - a • ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ)))
  linarith

/-- The minimum in the variational form is attained, at `φ = a M⁻¹ Qᵀ ψ`. -/
theorem blockSpinOperator_form_attained {A : Matrix ι ι ℝ} {Q : Matrix κ ι ℝ} {a : ℝ}
    (hM : (blockSpinPrecision A Q a).PosDef) (ψ : κ → ℝ) :
    schurFunctional A Q a ψ (a • ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ))) =
      ψ ⬝ᵥ blockSpinOperator A Q a *ᵥ ψ := by
  have := schurFunctional_sub_eq hM ψ (a • ((blockSpinPrecision A Q a)⁻¹ *ᵥ (Qᵀ *ᵥ ψ)))
  simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero] at this
  linarith

end Variational


end Balaban
