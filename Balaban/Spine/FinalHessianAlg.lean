/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalHessian

/-!
# Block matrices and the final Hessian

Real matrix identities for the pull-back `Q*` and the average `Q` used to identify the second
variation of the variational function with `finalHessian` (A6-3 (a), step P1d):
`(Q*)ᵀ = N^d Q`, `(Q*)ᵀ Q* = N^d`, and `projH e` commutes with the spin lift of `Q*`.
-/

@[expose] public section

open Matrix Finset

namespace Balaban

variable {d ℓ Nb m N : ℕ} [NeZero ℓ] [NeZero m]

section Transposes

omit [NeZero ℓ] [NeZero m] in
theorem spinLift_transpose {ι κ : Type*} (A : Matrix ι κ ℝ) :
    (spinLift N A)ᵀ = spinLift N Aᵀ := by
  ext ⟨y, i⟩ ⟨z, j⟩
  by_cases hij : i = j <;> simp [spinLift, hij, eq_comm]

theorem blockPullbackMatrix_transpose (hNb : Nb ≠ 0) :
    (blockPullbackMatrix d ℓ Nb m)ᵀ = ((Nb : ℝ) ^ d) • unitBlockAverageMatrix d ℓ Nb m := by
  ext y x
  have : ((Nb : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hNb)
  by_cases h : blockMap Nb m x = y
  · simp [blockPullbackMatrix, unitBlockAverageMatrix, h, this]
  · simp [blockPullbackMatrix, unitBlockAverageMatrix, h]

theorem blockPullbackMatrix_transpose_mul (hℓ : ℓ = Nb * m) :
    (blockPullbackMatrix d ℓ Nb m)ᵀ * blockPullbackMatrix d ℓ Nb m =
      ((Nb : ℝ) ^ d) • (1 : Matrix (Torus d m) (Torus d m) ℝ) := by
  ext y y'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockPullbackMatrix, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h : y = y'
  · subst h
    have hc := card_blockFibre (d := d) (ℓ := ℓ) (N := Nb) (m := m) hℓ y
    have e1 : ∀ x : Torus d ℓ, ((if blockMap Nb m x = y then (1 : ℝ) else 0) *
        (if blockMap Nb m x = y then 1 else 0)) = if blockMap Nb m x = y then 1 else 0 :=
      fun x => by split_ifs <;> simp
    simp only [e1, Finset.sum_boole, ite_true, mul_one]
    have : (Finset.univ.filter fun x : Torus d ℓ => blockMap Nb m x = y) = blockFibre Nb m y := rfl
    rw [this, hc]
    push_cast; rfl
  · simp only [h, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : blockMap Nb m x = y
    · have : ¬ blockMap Nb m x = y' := fun h2 => h (h1.symm.trans h2)
      simp [this]
    · simp [h1]

end Transposes

section Commute

/-- `projH e` commutes with the spin lift of any scalar matrix. -/
theorem projH_mul_spinLift {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (e : Fin N → ℝ) :
    projH (ι := ι) e * spinLift N A = spinLift N A * projH (ι := κ) e :=
  (spinLift_mul_projH A e).symm

end Commute

section Identity

omit [NeZero ℓ] [NeZero m] in
theorem dot_mulVec_transpose {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (v : ι → ℝ)
    (w : κ → ℝ) : v ⬝ᵥ (A *ᵥ w) = (Aᵀ *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- **The second variation as a quadratic form.** For a unit direction `e`, a block field `U` and
the fine Hamiltonian `H_u`, with `Λ = Q*` lifted to spins, `c = a/N²`, `Hr = N⁻² H_u`:
`c |ΛU|² − ⟨Hr⁻¹ (1 − P_e) c ΛU, c ΛU⟩ = N^{d−2} ⟨U, finalHessian U⟩`. -/
theorem second_variation_quad (hℓ : ℓ = Nb * m) (hNb : 0 < Nb) (hd : 2 ≤ d) {νu a : ℝ}
    (hν : 0 ≤ νu) (ha : 0 < a) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1)
    (Uv : Torus d m × Fin N → ℝ) :
    (a / (Nb : ℝ) ^ 2) * ((spinLift N (blockPullbackMatrix d ℓ Nb m) *ᵥ Uv) ⬝ᵥ
        (spinLift N (blockPullbackMatrix d ℓ Nb m) *ᵥ Uv)) -
      ((spinLift N (((((Nb : ℝ) ^ 2)⁻¹) • fineHamiltonian d ℓ Nb m νu a)⁻¹) *ᵥ
        ((1 - projH (ι := Torus d ℓ) e) *ᵥ ((a / (Nb : ℝ) ^ 2) •
          (spinLift N (blockPullbackMatrix d ℓ Nb m) *ᵥ Uv)))) ⬝ᵥ
        ((a / (Nb : ℝ) ^ 2) • (spinLift N (blockPullbackMatrix d ℓ Nb m) *ᵥ Uv))) =
      (Nb : ℝ) ^ (d - 2) * (Uv ⬝ᵥ (finalHessian d ℓ Nb m νu a e *ᵥ Uv)) := by
  classical
  have hd0 : 0 < d := by omega
  have hNbR : (Nb : ℝ) ≠ 0 := by exact_mod_cast hNb.ne'
  have hPD := fineHamiltonian_posDef hℓ hNb hd0 hν ha
  set Hu := fineHamiltonian d ℓ Nb m νu a with hHu
  have hHuu : Hu * Hu⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hPD.isUnit)
  have hinv : ((((Nb : ℝ) ^ 2)⁻¹) • Hu)⁻¹ = ((Nb : ℝ) ^ 2) • Hu⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hNbR),
      one_smul, hHuu]
  have hsymm : Hu⁻¹ᵀ = Hu⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    have : Huᵀ = Hu := by
      have := hPD.isHermitian
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [this]
  rw [hinv]
  set Qs := blockPullbackMatrix d ℓ Nb m with hQs
  set Λ := spinLift N Qs with hΛ
  set Pf := projH (ι := Torus d ℓ) e with hPf
  set Pc := projH (ι := Torus d m) e with hPc
  set c := a / (Nb : ℝ) ^ 2 with hc
  set Hs := spinLift N (((Nb : ℝ) ^ 2) • Hu⁻¹) with hHs
  have hcomm : (1 - Pf) * Λ = Λ * (1 - Pc) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPf, hPc, hΛ,
      projH_mul_spinLift]
  have hHsT : Hsᵀ = Hs := by
    rw [hHs, spinLift_transpose, Matrix.transpose_smul, hsymm]
  have hPcT : Pcᵀ = Pc := projH_transpose e
  have hΛΛ : Λᵀ * Λ = ((Nb : ℝ) ^ d) • (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ) := by
    rw [hΛ, spinLift_transpose, ← spinLift_mul, hQs, blockPullbackMatrix_transpose_mul hℓ,
      spinLift_smul, spinLift_one]
  set K := Λᵀ * Hs * Λ with hK
  have hT1 : (Λ *ᵥ Uv) ⬝ᵥ (Λ *ᵥ Uv) = ((Nb : ℝ) ^ d) * (Uv ⬝ᵥ Uv) := by
    rw [dot_mulVec_transpose, Matrix.mulVec_mulVec, hΛΛ, Matrix.smul_mulVec, Matrix.one_mulVec,
      smul_dotProduct, smul_eq_mul]
  have hsub : (1 - Pf) *ᵥ (c • (Λ *ᵥ Uv)) = c • (Λ *ᵥ ((1 - Pc) *ᵥ Uv)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  have hT2 : (Hs *ᵥ ((1 - Pf) *ᵥ (c • (Λ *ᵥ Uv)))) ⬝ᵥ (c • (Λ *ᵥ Uv)) =
      c ^ 2 * (Uv ⬝ᵥ (((1 - Pc) * K) *ᵥ Uv)) := by
    have key : ((Hs * Λ) *ᵥ ((1 - Pc) *ᵥ Uv)) ⬝ᵥ (Λ *ᵥ Uv) = Uv ⬝ᵥ (((1 - Pc) * K) *ᵥ Uv) := by
      calc ((Hs * Λ) *ᵥ ((1 - Pc) *ᵥ Uv)) ⬝ᵥ (Λ *ᵥ Uv)
          = (Λ *ᵥ Uv) ⬝ᵥ ((Hs * Λ) *ᵥ ((1 - Pc) *ᵥ Uv)) := dotProduct_comm _ _
        _ = ((Hs * Λ)ᵀ *ᵥ (Λ *ᵥ Uv)) ⬝ᵥ ((1 - Pc) *ᵥ Uv) := dot_mulVec_transpose _ _ _
        _ = (K *ᵥ Uv) ⬝ᵥ ((1 - Pc) *ᵥ Uv) := by
            rw [Matrix.transpose_mul, hHsT, Matrix.mulVec_mulVec, hK, Matrix.mul_assoc]
        _ = (K *ᵥ Uv) ⬝ᵥ ((1 - Pc) *ᵥ Uv) := by rw [dotProduct_comm]
        _ = ((1 - Pc)ᵀ *ᵥ (K *ᵥ Uv)) ⬝ᵥ Uv := by rw [dot_mulVec_transpose]
        _ = Uv ⬝ᵥ (((1 - Pc) * K) *ᵥ Uv) := by
            rw [dotProduct_comm, Matrix.transpose_sub, Matrix.transpose_one, hPcT,
              Matrix.mulVec_mulVec]
    rw [hsub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, key]
    ring
  set S := spinLift N (unitBlockAverageMatrix d ℓ Nb m * Hu⁻¹ * Qs) with hS
  have hKS : K = (((Nb : ℝ) ^ d) * ((Nb : ℝ) ^ 2)) • S := by
    rw [hK, hΛ, hHs, spinLift_transpose, ← spinLift_mul, ← spinLift_mul, hQs,
      blockPullbackMatrix_transpose hNb.ne', hS, ← spinLift_smul]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm]
  have hD : finalHessian d ℓ Nb m νu a e = a • (1 : Matrix (Torus d m × Fin N) (Torus d m × Fin N) ℝ)
      - (a ^ 2) • (S * (1 - Pc)) := by
    rw [finalHessian_eq_split hℓ hNb hd0 hν ha he]
    unfold unconstrainedUnitOperator
    rw [spinLift_sub, spinLift_smul, spinLift_smul, spinLift_one, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, smul_sub]
    change a • Pc + (a • 1 - a • Pc - (a ^ 2) • (S * (1 - Pc))) = _
    abel
  have hSc : (1 - Pc) * S = S * (1 - Pc) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPc, hS, projH_mul_spinLift]
  have hd2 : (Nb : ℝ) ^ d = (Nb : ℝ) ^ (d - 2) * (Nb : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [hT1, hT2, hD, hKS, Matrix.mul_smul, hSc]
  simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  rw [hc, hd2]
  field_simp

end Identity
