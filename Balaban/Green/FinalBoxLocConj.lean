/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocCut

/-!
# Complex conjugation of the cut family (A6-3, the localized square root)

The entries of the cut family of the final Hessian are built from the real operator `U = finalOp`
and the real partition of unity of the macro cover by ring operations, inverses and a real
integral.  Hence entrywise complex conjugation (`conjM`, a ring homomorphism of matrices) maps
the family at `(h, s)` to the family at `(conj h, conj s)`:

* `conjM_inv`: conjugation commutes with the inverse;
* `conjM_boxG`, `conjM_boxR`, `conjM_taggedMat`, `conjM_taggedGfin`, `conjM_intMat`: the local
  resolvents, the tagged matrices, the tagged parametrix and the matrix integral;
* `conjM_taggedCfin`, `conjM_boxCut`: the Stieltjes square-root family and the cut family.

In particular the cut family has real entries at a real `h` and real parameters.
-/

@[expose] public section

namespace Balaban.Green

open Matrix ComplexConjugate MeasureTheory

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise complex conjugation of square matrices, as a ring homomorphism. -/
noncomputable abbrev conjM : Matrix ι ι ℂ →+* Matrix ι ι ℂ := (starRingEnd ℂ).mapMatrix

theorem conjM_apply (A : Matrix ι ι ℂ) (x y : ι) : conjM A x y = conj (A x y) := rfl

/-- Conjugation commutes with the inverse. -/
theorem conjM_inv (A : Matrix ι ι ℂ) : conjM A⁻¹ = (conjM A)⁻¹ := by
  have e : ∀ B : Matrix ι ι ℂ, conjM B = Bᴴᵀ := by
    intro B; ext i j
    simp [conjM_apply, Matrix.conjTranspose_apply]
  rw [e, e, Matrix.conjTranspose_nonsing_inv, Matrix.transpose_nonsing_inv]

/-- The complexification of a real matrix is fixed by conjugation (shared core). -/
theorem conjM_map_ofReal (U : Matrix ι ι ℝ) :
    conjM (U.map (algebraMap ℝ ℂ)) = U.map (algebraMap ℝ ℂ) := by
  ext x y
  rw [conjM_apply]
  exact Complex.conj_ofReal _

theorem conjM_diagonal (c : ι → ℂ) :
    conjM (Matrix.diagonal c) = Matrix.diagonal fun i => conj (c i) := by
  ext i j
  rw [conjM_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem conjM_ofReal_smul (c : ℝ) (A : Matrix ι ι ℂ) :
    conjM ((c : ℂ) • A) = (c : ℂ) • conjM A := by
  ext i j
  simp [conjM_apply]

theorem conjM_boxP (B : Finset ι) : conjM (boxP B) = boxP B := by
  unfold boxP
  rw [conjM_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem conjM_shiftMat (U : Matrix ι ι ℂ) (t : ℝ) :
    conjM (shiftMat U t) = shiftMat (conjM U) t := by
  unfold shiftMat
  rw [map_add, conjM_ofReal_smul, map_one]

theorem conjM_boxH (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    conjM (boxH U B t) = boxH (conjM U) B t := by
  unfold boxH
  rw [map_add, map_mul, map_mul, map_sub, map_one, conjM_boxP, conjM_shiftMat]

theorem conjM_boxG (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    conjM (boxG U B t) = boxG (conjM U) B t := by
  unfold boxG
  rw [map_mul, conjM_inv, conjM_boxH, conjM_boxP]

theorem conjM_boxR (U : Matrix ι ι ℂ) (B : Finset ι) (c : ι → ℂ) (t : ℝ) :
    conjM (boxR U B c t) = boxR (conjM U) B (fun i => conj (c i)) t := by
  unfold boxR
  rw [map_sub, map_mul, map_mul, conjM_diagonal, conjM_shiftMat, conjM_boxG]

theorem conjM_taggedMat {Z Pc : Type*} (S : Finset Z) (V : Z → ι → ι → Finset Pc)
    (a : Z → Matrix ι ι ℂ) (s : Pc → ℂ) :
    conjM (taggedMat S V a s) = taggedMat S V (fun z => conjM (a z)) (fun p => conj (s p)) := by
  ext x y
  simp [conjM_apply, taggedMat, tagMon, map_sum, map_prod]

theorem conjM_taggedGfin {Z Pc : Type*} (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) (s : Pc → ℂ) :
    conjM (taggedGfin S B c V U t s) =
      taggedGfin S B (fun z i => conj (c z i)) V (conjM U) t (fun p => conj (s p)) := by
  unfold taggedGfin taggedG taggedK
  rw [map_mul, conjM_inv, map_sub, map_one, conjM_taggedMat, conjM_taggedMat]
  simp only [map_mul, conjM_diagonal, conjM_boxG, conjM_boxR]

theorem conjM_intMat (μ : Measure ℝ) (F : ℝ → Matrix ι ι ℂ) :
    conjM (Localization.intMat μ F) = Localization.intMat μ fun t => conjM (F t) := by
  ext p q
  simp only [conjM_apply, Localization.intMat]
  exact integral_conj.symm

end Generic

section Final

variable {d L N₀ k M N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

theorem conjM_finalOp : conjM (finalOp d L N₀ k v a) = finalOp d L N₀ k v a :=
  conjM_map_ofReal (ι := L1Torus d N₀) (unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a)

omit [NeZero L] in
/-- **Conjugation of the Stieltjes square-root family of a real matrix** (shared core):
`conj (C_fin(U; s)) = C_fin(U; conj s)` for `conj U = U`. -/
theorem conjM_taggedCfinU {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hU : conjM U = U)
    (s : MacIdx d N₀ M → ℂ) :
    conjM (taggedCfinU d N₀ M U s) = taggedCfinU d N₀ M U (fun p => conj (s p)) := by
  unfold taggedCfinU
  simp only [conjM_ofReal_smul, conjM_intMat, conjM_taggedGfin, hU, Complex.conj_ofReal]

/-- **Conjugation of the Stieltjes square-root family**: `conj (C_fin(s)) = C_fin(conj s)`. -/
theorem conjM_taggedCfin (s : MacIdx d N₀ M → ℂ) :
    conjM (taggedCfin d L N₀ k M v a s) = taggedCfin d L N₀ k M v a (fun p => conj (s p)) :=
  conjM_taggedCfinU conjM_finalOp s

omit [NeZero L] in
theorem conjM_liftOp (A : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) :
    conjM (Multiscale.liftOp N A) = Multiscale.liftOp N (conjM A) := by
  ext p q
  simp only [conjM_apply, Multiscale.liftOp]
  split_ifs <;> simp

omit [NeZero L] in
theorem conjM_projHC (h : Fin N → ℂ) :
    conjM (projHC h : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ) =
      projHC fun i => conj (h i) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  rw [conjM_apply, projHC_apply, projHC_apply]
  split_ifs <;> simp [map_sum, map_pow]

omit [NeZero L] in
theorem conjM_diagonal_chiSum (s : MacIdx d N₀ M → ℂ) :
    conjM (Matrix.diagonal (chiSum d N₀ M s)) =
      Matrix.diagonal (chiSum d N₀ M fun p => conj (s p)) := by
  rw [conjM_diagonal]
  congr 1
  funext x
  simp [chiSum, map_sum]

omit [NeZero L] in
/-- **Conjugation of the cut family of a real matrix** (shared core):
`conj (boxCutU(U; h, s)) = boxCutU(U; conj h, conj s)` for `conj U = U`. -/
theorem conjM_boxCutU {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hU : conjM U = U)
    (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    conjM (boxCutU d N₀ M a U h s) =
      boxCutU d N₀ M a U (fun i => conj (h i)) (fun p => conj (s p)) := by
  unfold boxCutU
  rw [map_add, conjM_ofReal_smul, map_mul, map_mul, map_sub, map_one, conjM_liftOp, conjM_liftOp,
    conjM_diagonal_chiSum, conjM_taggedCfinU hU, conjM_projHC]

/-- **Conjugation of the cut family**: `conj (boxCut(h, s)) = boxCut(conj h, conj s)`. -/
theorem conjM_boxCut (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    conjM (boxCut d L N₀ k M v a h s) =
      boxCut d L N₀ k M v a (fun i => conj (h i)) (fun p => conj (s p)) :=
  conjM_boxCutU conjM_finalOp h s

end Final

end Balaban.Green
