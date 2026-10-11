module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order

/-!
# Schur complement and Woodbury identities for the Gaussian block-spin step

Finite real matrices. Data: `A` positive definite on the fine index type `ι`, `Q : Matrix κ ι ℝ`
(the coarse-graining matrix, transpose `Qᵀ`), and `a > 0`. Put
* `M = A + a QᵀQ` (`blockSpinPrecision`);
* `Δ = a·1 - a² Q M⁻¹ Qᵀ` (`blockSpinOperator`), the Schur complement of `M` in the block matrix
  `[[M, aQᵀ], [aQ, a·1]]`.

Results (P4 (5.12)-(5.13), P1 (1.11) in Euclidean form):
* `blockSpinPrecision_posDef`;
* `det_blockSpinPrecision_mul_det_blockSpinOperator`:
  `det M * det Δ = a ^ card κ * det A` (Schur complement, expanded in the two ways);
* `blockSpinOperator_mul_woodbury`: `Δ (a⁻¹ + Q A⁻¹ Qᵀ) = 1`, the Woodbury form
  `Δ⁻¹ = a⁻¹ + Q A⁻¹ Qᵀ`;
* `blockSpinOperator_posDef`.
The weighted-inner-product form is in `Balaban.Gaussian.BlockSpin`.
-/

@[expose] public section

namespace Balaban

open Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `M = A + a QᵀQ`. -/
def blockSpinPrecision (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) : Matrix ι ι ℝ :=
  A + a • (Qᵀ * Q)

/-- `Δ = a·1 - a² Q M⁻¹ Qᵀ`. -/
noncomputable def blockSpinOperator (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) :
    Matrix κ κ ℝ :=
  a • (1 : Matrix κ κ ℝ) - (a ^ 2) • (Q * (blockSpinPrecision A Q a)⁻¹ * Qᵀ)

omit [DecidableEq ι] [DecidableEq κ] in
theorem blockSpinPrecision_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) : (blockSpinPrecision A Q a).PosDef := by
  unfold blockSpinPrecision
  refine hA.add_posSemidef ?_
  refine Matrix.PosSemidef.smul ?_ ha.le
  simpa using Matrix.posSemidef_conjTranspose_mul_self Q

theorem blockSpinOperator_eq_schur (A : Matrix ι ι ℝ) (Q : Matrix κ ι ℝ) (a : ℝ) :
    blockSpinOperator A Q a =
      a • (1 : Matrix κ κ ℝ) - (a • Q) * (blockSpinPrecision A Q a)⁻¹ * (a • Qᵀ) := by
  unfold blockSpinOperator
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]

theorem det_blockSpinPrecision_mul_det_blockSpinOperator {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (Q : Matrix κ ι ℝ) {a : ℝ} (ha : 0 < a) :
    (blockSpinPrecision A Q a).det * (blockSpinOperator A Q a).det =
      a ^ Fintype.card κ * A.det := by
  have hM := blockSpinPrecision_posDef hA Q ha
  have : Invertible (blockSpinPrecision A Q a) := hM.isUnit.invertible
  have hinvA : Invertible (a • (1 : Matrix κ κ ℝ)) :=
    ⟨a⁻¹ • 1, by simp [smul_smul, ha.ne'], by simp [smul_smul, ha.ne']⟩
  have hinv : ⅟(a • (1 : Matrix κ κ ℝ)) = a⁻¹ • 1 :=
    invOf_eq_right_inv (by simp [smul_smul, ha.ne'])
  have h1 := Matrix.det_fromBlocks₁₁ (blockSpinPrecision A Q a) (a • Qᵀ) (a • Q) (a • 1)
  have h2 := Matrix.det_fromBlocks₂₂ (blockSpinPrecision A Q a) (a • Qᵀ) (a • Q) (a • 1)
  rw [h1, hinv] at h2
  rw [invOf_eq_nonsing_inv] at h2
  have hd : (a • (1 : Matrix κ κ ℝ)).det = a ^ Fintype.card κ := by simp
  have hA' : blockSpinPrecision A Q a - (a • Qᵀ) * (a⁻¹ • (1 : Matrix κ κ ℝ)) * (a • Q) = A := by
    simp [blockSpinPrecision, Matrix.mul_smul, smul_smul, ha.ne']
  rw [hd, hA'] at h2
  rw [blockSpinOperator_eq_schur]
  exact h2

/-- Woodbury form: `Δ (a⁻¹ + Q A⁻¹ Qᵀ) = 1`. -/
theorem blockSpinOperator_mul_woodbury {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ)
    {a : ℝ} (ha : 0 < a) :
    blockSpinOperator A Q a * (a⁻¹ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ) = 1 := by
  have hM := blockSpinPrecision_posDef hA Q ha
  have hMu : (blockSpinPrecision A Q a).det ≠ 0 := hM.det_pos.ne'
  have hAu : A.det ≠ 0 := hA.det_pos.ne'
  set M := blockSpinPrecision A Q a with hMdef
  set K : Matrix κ κ ℝ := Q * A⁻¹ * Qᵀ with hK
  have hMi : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hMu)
  have hAi : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hAu)
  -- `M A⁻¹ Qᵀ = Qᵀ (1 + a K)`
  have h1 : M * (A⁻¹ * Qᵀ) = Qᵀ * (1 + a • K) := by
    rw [hMdef, blockSpinPrecision, hK]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    rw [← Matrix.mul_assoc A, hAi, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  -- hence `M⁻¹ Qᵀ (1 + a K) = A⁻¹ Qᵀ`
  have h2 : M⁻¹ * Qᵀ * (1 + a • K) = A⁻¹ * Qᵀ := by
    rw [Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, hMi, Matrix.one_mul]
  have h3 : Q * (M⁻¹ * Qᵀ) * (1 + a • K) = K := by
    calc Q * (M⁻¹ * Qᵀ) * (1 + a • K) = Q * (M⁻¹ * Qᵀ * (1 + a • K)) := by
          simp only [Matrix.mul_assoc]
      _ = Q * (A⁻¹ * Qᵀ) := by rw [h2]
      _ = K := by rw [hK, Matrix.mul_assoc]
  unfold blockSpinOperator
  simp only [← hMdef]
  have e : (a ^ 2) • (Q * M⁻¹ * Qᵀ) = a • (a • (Q * (M⁻¹ * Qᵀ))) := by
    simp [smul_smul, sq, Matrix.mul_assoc]
  have hD : a⁻¹ • (1 : Matrix κ κ ℝ) + K = a⁻¹ • (1 + a • K) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
  have e3 : a • (a • (Q * (M⁻¹ * Qᵀ))) * (a⁻¹ • (1 : Matrix κ κ ℝ) + K) = a • K := by
    rw [hD, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, h3]
    have : a * a * a⁻¹ = a := by field_simp
    rw [this]
  rw [e, Matrix.sub_mul, e3, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul,
    mul_inv_cancel₀ ha.ne', one_smul]
  abel

theorem woodbury_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) : (a⁻¹ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ).PosDef := by
  have h1 : (a⁻¹ • (1 : Matrix κ κ ℝ)).PosDef := by
    simpa using (Matrix.PosDef.one (n := κ) (R := ℝ)).smul (inv_pos.mpr ha)
  have h2 : (Q * A⁻¹ * Qᵀ).PosSemidef := by
    simpa using hA.inv.posSemidef.mul_mul_conjTranspose_same Q
  exact h1.add_posSemidef h2

/-- `Δ = (a⁻¹ + Q A⁻¹ Qᵀ)⁻¹`. -/
theorem blockSpinOperator_eq_inv {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) :
    blockSpinOperator A Q a = (a⁻¹ • (1 : Matrix κ κ ℝ) + Q * A⁻¹ * Qᵀ)⁻¹ :=
  (Matrix.inv_eq_left_inv (blockSpinOperator_mul_woodbury hA Q ha)).symm

/-- Positivity of the block-spin operator `Δ`. -/
theorem blockSpinOperator_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef) (Q : Matrix κ ι ℝ) {a : ℝ}
    (ha : 0 < a) : (blockSpinOperator A Q a).PosDef := by
  rw [blockSpinOperator_eq_inv hA Q ha]
  exact (woodbury_posDef hA Q ha).inv

end Balaban
