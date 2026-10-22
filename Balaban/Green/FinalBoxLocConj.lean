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

The chain is proved once for the twist `matConj ψ σ` (entrywise ring homomorphism `ψ`, diagonal
involution `σ`; shared core), `conjM = matConj conj 1`; the case `ψ = id`, `σ = ±1` gives the
block structure of the cut family of a block-diagonal operator (`Green/FinalBoxLocRegion`).
-/

@[expose] public section

namespace Balaban.Green

open Matrix ComplexConjugate MeasureTheory

section Twist

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Entrywise `ψ` twisted by a diagonal involution `σ`** (shared core; `σ x · σ x = 1`):
`M ↦ σ ψ(M) σ`, with entries `σ x ψ(M x y) σ y`, a ring homomorphism of square matrices.  Entrywise
conjugation `conjM` is the case `ψ = conj`, `σ = 1`; the block structure of a region `Ω` is the
case `ψ = id`, `σ = ±1` (`regionConj`). -/
noncomputable def matConj (ψ : ℂ →+* ℂ) (σ : ι → ℂ) (hσ : ∀ x, σ x * σ x = 1) :
    Matrix ι ι ℂ →+* Matrix ι ι ℂ where
  toFun A := Matrix.of fun x y => σ x * ψ (A x y) * σ y
  map_one' := by
    ext x y
    simp only [Matrix.of_apply, Matrix.one_apply]
    split_ifs with h
    · subst h; rw [map_one, mul_one, hσ]
    · rw [map_zero, mul_zero, zero_mul]
  map_mul' A B := by
    ext x y
    simp only [Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    linear_combination (-(σ x * ψ (A x z) * ψ (B z y) * σ y)) * hσ z
  map_zero' := by ext; simp
  map_add' A B := by ext; simp only [Matrix.of_apply, Matrix.add_apply, map_add]; ring

variable {ψ : ℂ →+* ℂ} {σ : ι → ℂ} {hσ : ∀ x, σ x * σ x = 1}

theorem matConj_apply (A : Matrix ι ι ℂ) (x y : ι) :
    matConj ψ σ hσ A x y = σ x * ψ (A x y) * σ y := rfl

/-- `matConj` is an involution when `ψ` is and `ψ` fixes `σ`. -/
theorem matConj_matConj (hψψ : ∀ z, ψ (ψ z) = z) (hσψ : ∀ x, ψ (σ x) = σ x)
    (A : Matrix ι ι ℂ) : matConj ψ σ hσ (matConj ψ σ hσ A) = A := by
  ext x y
  simp only [matConj_apply, map_mul, hψψ, hσψ]
  linear_combination (A x y * σ y * σ y) * hσ x + A x y * hσ y

/-- `matConj` commutes with the inverse. -/
theorem matConj_inv (hψψ : ∀ z, ψ (ψ z) = z) (hσψ : ∀ x, ψ (σ x) = σ x) (A : Matrix ι ι ℂ) :
    matConj ψ σ hσ A⁻¹ = (matConj ψ σ hσ A)⁻¹ := by
  by_cases hA : IsUnit A.det
  · have h1 : matConj ψ σ hσ A * matConj ψ σ hσ A⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv _ hA, map_one]
    exact (Matrix.inv_eq_right_inv h1).symm
  · have hB : ¬ IsUnit (matConj ψ σ hσ A).det := by
      intro hu
      apply hA
      have hu' := ((Matrix.isUnit_iff_isUnit_det _).2 hu).map (matConj ψ σ hσ)
      rw [matConj_matConj hψψ hσψ] at hu'
      exact (Matrix.isUnit_iff_isUnit_det _).1 hu'
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, map_zero,
      Matrix.nonsing_inv_apply_not_isUnit _ hB]

theorem matConj_diagonal (c : ι → ℂ) :
    matConj ψ σ hσ (Matrix.diagonal c) = Matrix.diagonal fun i => ψ (c i) := by
  ext x y
  simp only [matConj_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; linear_combination ψ (c x) * hσ x
  · simp

theorem matConj_ofReal_smul (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (c : ℝ) (A : Matrix ι ι ℂ) :
    matConj ψ σ hσ ((c : ℂ) • A) = (c : ℂ) • matConj ψ σ hσ A := by
  ext x y
  simp only [matConj_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hψℝ]
  ring

theorem matConj_boxP (B : Finset ι) : matConj ψ σ hσ (boxP B) = boxP B := by
  unfold boxP
  rw [matConj_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem matConj_shiftMat (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (U : Matrix ι ι ℂ) (t : ℝ) :
    matConj ψ σ hσ (shiftMat U t) = shiftMat (matConj ψ σ hσ U) t := by
  unfold shiftMat
  rw [map_add, matConj_ofReal_smul hψℝ, map_one]

theorem matConj_boxH (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    matConj ψ σ hσ (boxH U B t) = boxH (matConj ψ σ hσ U) B t := by
  unfold boxH
  rw [map_add, map_mul, map_mul, map_sub, map_one, matConj_boxP, matConj_shiftMat hψℝ]

theorem matConj_boxG (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (hψψ : ∀ z, ψ (ψ z) = z)
    (hσψ : ∀ x, ψ (σ x) = σ x) (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    matConj ψ σ hσ (boxG U B t) = boxG (matConj ψ σ hσ U) B t := by
  unfold boxG
  rw [map_mul, matConj_inv hψψ hσψ, matConj_boxH hψℝ, matConj_boxP]

theorem matConj_boxR (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (hψψ : ∀ z, ψ (ψ z) = z)
    (hσψ : ∀ x, ψ (σ x) = σ x) (U : Matrix ι ι ℂ) (B : Finset ι) (c : ι → ℂ) (t : ℝ) :
    matConj ψ σ hσ (boxR U B c t) = boxR (matConj ψ σ hσ U) B (fun i => ψ (c i)) t := by
  unfold boxR
  rw [map_sub, map_mul, map_mul, matConj_diagonal, matConj_shiftMat hψℝ,
    matConj_boxG hψℝ hψψ hσψ]

theorem matConj_taggedMat {Z Pc : Type*} (S : Finset Z) (V : Z → ι → ι → Finset Pc)
    (a : Z → Matrix ι ι ℂ) (s : Pc → ℂ) :
    matConj ψ σ hσ (taggedMat S V a s) =
      taggedMat S V (fun z => matConj ψ σ hσ (a z)) (fun p => ψ (s p)) := by
  ext x y
  simp only [matConj_apply, taggedMat, Matrix.of_apply, tagMon, map_sum, map_mul, map_prod,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

theorem matConj_taggedGfin (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (hψψ : ∀ z, ψ (ψ z) = z)
    (hσψ : ∀ x, ψ (σ x) = σ x) {Z Pc : Type*} (S : Finset Z) (B : Z → Finset ι)
    (c : Z → ι → ℂ) (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) (s : Pc → ℂ) :
    matConj ψ σ hσ (taggedGfin S B c V U t s) =
      taggedGfin S B (fun z i => ψ (c z i)) V (matConj ψ σ hσ U) t (fun p => ψ (s p)) := by
  unfold taggedGfin taggedG taggedK
  rw [map_mul, matConj_inv hψψ hσψ, map_sub, map_one, matConj_taggedMat, matConj_taggedMat]
  simp only [map_mul, matConj_diagonal, matConj_boxG hψℝ hψψ hσψ, matConj_boxR hψℝ hψψ hσψ]

theorem matConj_intMat (hψint : ∀ (μ : Measure ℝ) (f : ℝ → ℂ), ψ (∫ t, f t ∂μ) = ∫ t, ψ (f t) ∂μ)
    (μ : Measure ℝ) (F : ℝ → Matrix ι ι ℂ) :
    matConj ψ σ hσ (Localization.intMat μ F) =
      Localization.intMat μ fun t => matConj ψ σ hσ (F t) := by
  ext x y
  simp only [matConj_apply, Localization.intMat, hψint]
  rw [← integral_const_mul, ← integral_mul_const]

end Twist

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise complex conjugation of square matrices, as a ring homomorphism. -/
noncomputable abbrev conjM : Matrix ι ι ℂ →+* Matrix ι ι ℂ := (starRingEnd ℂ).mapMatrix

theorem conjM_apply (A : Matrix ι ι ℂ) (x y : ι) : conjM A x y = conj (A x y) := rfl

/-- `conjM` is the twist `matConj conj 1`. -/
theorem conjM_eq_matConj :
    (conjM : Matrix ι ι ℂ →+* Matrix ι ι ℂ) =
      matConj (starRingEnd ℂ) (fun _ => 1) (fun _ => mul_one 1) := by
  ext A x y
  simp [conjM_apply, matConj_apply]

/-- Conjugation commutes with the inverse. -/
theorem conjM_inv (A : Matrix ι ι ℂ) : conjM A⁻¹ = (conjM A)⁻¹ := by
  rw [conjM_eq_matConj]
  exact matConj_inv (fun z => Complex.conj_conj z) (fun _ => map_one _) A

/-- The complexification of a real matrix is fixed by conjugation (shared core). -/
theorem conjM_map_ofReal (U : Matrix ι ι ℝ) :
    conjM (U.map (algebraMap ℝ ℂ)) = U.map (algebraMap ℝ ℂ) := by
  ext x y
  rw [conjM_apply]
  exact Complex.conj_ofReal _

theorem conjM_diagonal (c : ι → ℂ) :
    conjM (Matrix.diagonal c) = Matrix.diagonal fun i => conj (c i) := by
  rw [conjM_eq_matConj]
  exact matConj_diagonal c

theorem conjM_ofReal_smul (c : ℝ) (A : Matrix ι ι ℂ) :
    conjM ((c : ℂ) • A) = (c : ℂ) • conjM A := by
  rw [conjM_eq_matConj]
  exact matConj_ofReal_smul Complex.conj_ofReal c A

theorem conjM_boxP (B : Finset ι) : conjM (boxP B) = boxP B := by
  rw [conjM_eq_matConj]
  exact matConj_boxP B

theorem conjM_shiftMat (U : Matrix ι ι ℂ) (t : ℝ) :
    conjM (shiftMat U t) = shiftMat (conjM U) t := by
  rw [conjM_eq_matConj]
  exact matConj_shiftMat Complex.conj_ofReal U t

theorem conjM_boxH (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    conjM (boxH U B t) = boxH (conjM U) B t := by
  rw [conjM_eq_matConj]
  exact matConj_boxH Complex.conj_ofReal U B t

theorem conjM_boxG (U : Matrix ι ι ℂ) (B : Finset ι) (t : ℝ) :
    conjM (boxG U B t) = boxG (conjM U) B t := by
  rw [conjM_eq_matConj]
  exact matConj_boxG Complex.conj_ofReal (fun z => Complex.conj_conj z) (fun _ => map_one _) U B t

theorem conjM_boxR (U : Matrix ι ι ℂ) (B : Finset ι) (c : ι → ℂ) (t : ℝ) :
    conjM (boxR U B c t) = boxR (conjM U) B (fun i => conj (c i)) t := by
  rw [conjM_eq_matConj]
  exact matConj_boxR Complex.conj_ofReal (fun z => Complex.conj_conj z) (fun _ => map_one _) U B c t

theorem conjM_taggedMat {Z Pc : Type*} (S : Finset Z) (V : Z → ι → ι → Finset Pc)
    (a : Z → Matrix ι ι ℂ) (s : Pc → ℂ) :
    conjM (taggedMat S V a s) = taggedMat S V (fun z => conjM (a z)) (fun p => conj (s p)) := by
  rw [conjM_eq_matConj]
  exact matConj_taggedMat S V a s

theorem conjM_taggedGfin {Z Pc : Type*} (S : Finset Z) (B : Z → Finset ι) (c : Z → ι → ℂ)
    (V : Z → ι → ι → Finset Pc) (U : Matrix ι ι ℂ) (t : ℝ) (s : Pc → ℂ) :
    conjM (taggedGfin S B c V U t s) =
      taggedGfin S B (fun z i => conj (c z i)) V (conjM U) t (fun p => conj (s p)) := by
  rw [conjM_eq_matConj]
  exact matConj_taggedGfin Complex.conj_ofReal (fun z => Complex.conj_conj z) (fun _ => map_one _) S B c V U t s

theorem conjM_intMat (μ : Measure ℝ) (F : ℝ → Matrix ι ι ℂ) :
    conjM (Localization.intMat μ F) = Localization.intMat μ fun t => conjM (F t) := by
  rw [conjM_eq_matConj]
  exact matConj_intMat (fun _ _ => integral_conj.symm) μ F

end Generic

section Final

variable {d L N₀ k M N : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

theorem conjM_finalOp : conjM (finalOp d L N₀ k v a) = finalOp d L N₀ k v a :=
  conjM_map_ofReal (ι := L1Torus d N₀) (unconstrainedUnitOperator d (N₀ * L ^ k) (L ^ k) N₀ v a)

section TwistFinal

variable {ψ : ℂ →+* ℂ} {σ : L1Torus d N₀ → ℂ} {hσ : ∀ x, σ x * σ x = 1}

omit [NeZero L] in
/-- **The twist of the Stieltjes square-root family** (shared core):
`σ ψ(C_fin(U; s)) σ = C_fin(U; ψ s)` for `σ ψ(U) σ = U`. -/
theorem matConj_taggedCfinU (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (hψψ : ∀ z, ψ (ψ z) = z)
    (hσψ : ∀ x, ψ (σ x) = σ x)
    (hψint : ∀ (μ : Measure ℝ) (f : ℝ → ℂ), ψ (∫ t, f t ∂μ) = ∫ t, ψ (f t) ∂μ)
    {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hU : matConj ψ σ hσ U = U)
    (s : MacIdx d N₀ M → ℂ) :
    matConj ψ σ hσ (taggedCfinU d N₀ M U s) = taggedCfinU d N₀ M U (fun p => ψ (s p)) := by
  unfold taggedCfinU
  simp only [matConj_ofReal_smul hψℝ, matConj_intMat hψint, matConj_taggedGfin hψℝ hψψ hσψ, hU,
    hψℝ]

omit [NeZero L] in
theorem matConj_liftOp (A : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) :
    matConj ψ (fun p : L1Torus d N₀ × Fin N => σ p.1) (fun p => hσ p.1)
        (Multiscale.liftOp N A) = Multiscale.liftOp N (matConj ψ σ hσ A) := by
  ext p q
  simp only [matConj_apply, Multiscale.liftOp]
  split_ifs <;> simp

omit [NeZero L] in
theorem matConj_projHC (h : Fin N → ℂ) :
    matConj ψ (fun p : L1Torus d N₀ × Fin N => σ p.1) (fun p => hσ p.1)
        (projHC h : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ) =
      projHC fun i => ψ (h i) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  rw [matConj_apply, projHC_apply, projHC_apply]
  split_ifs with hxy
  · subst hxy
    simp only [map_div₀, map_mul, map_sum, map_pow]
    linear_combination (ψ (h i) * ψ (h j) / ∑ k, ψ (h k) ^ 2) * hσ x
  · simp

omit [NeZero L] in
theorem matConj_diagonal_chiSum (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (s : MacIdx d N₀ M → ℂ) :
    matConj ψ σ hσ (Matrix.diagonal (chiSum d N₀ M s)) =
      Matrix.diagonal (chiSum d N₀ M fun p => ψ (s p)) := by
  rw [matConj_diagonal]
  congr 1
  funext x
  simp [chiSum, map_sum, hψℝ]

omit [NeZero L] in
/-- **The twist of the cut family** (shared core):
`σ ψ(boxCutU(U; h, s)) σ = boxCutU(U; ψ h, ψ s)` for `σ ψ(U) σ = U` (`σ` acting on the sites). -/
theorem matConj_boxCutU (hψℝ : ∀ r : ℝ, ψ (r : ℂ) = r) (hψψ : ∀ z, ψ (ψ z) = z)
    (hσψ : ∀ x, ψ (σ x) = σ x)
    (hψint : ∀ (μ : Measure ℝ) (f : ℝ → ℂ), ψ (∫ t, f t ∂μ) = ∫ t, ψ (f t) ∂μ)
    {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hU : matConj ψ σ hσ U = U)
    (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    matConj ψ (fun p : L1Torus d N₀ × Fin N => σ p.1) (fun p => hσ p.1)
        (boxCutU d N₀ M a U h s) =
      boxCutU d N₀ M a U (fun i => ψ (h i)) (fun p => ψ (s p)) := by
  unfold boxCutU
  rw [map_add, matConj_ofReal_smul hψℝ, map_mul, map_mul, map_sub, map_one, matConj_liftOp,
    matConj_liftOp, matConj_diagonal_chiSum hψℝ, matConj_taggedCfinU hψℝ hψψ hσψ hψint hU,
    matConj_projHC]

end TwistFinal

omit [NeZero L] in
/-- **Conjugation of the Stieltjes square-root family of a real matrix** (shared core):
`conj (C_fin(U; s)) = C_fin(U; conj s)` for `conj U = U`. -/
theorem conjM_taggedCfinU {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hU : conjM U = U)
    (s : MacIdx d N₀ M → ℂ) :
    conjM (taggedCfinU d N₀ M U s) = taggedCfinU d N₀ M U (fun p => conj (s p)) := by
  rw [conjM_eq_matConj] at hU ⊢
  exact matConj_taggedCfinU Complex.conj_ofReal (fun z => Complex.conj_conj z) (fun _ => map_one _)
    (fun _ _ => integral_conj.symm) hU s

/-- **Conjugation of the Stieltjes square-root family**: `conj (C_fin(s)) = C_fin(conj s)`. -/
theorem conjM_taggedCfin (s : MacIdx d N₀ M → ℂ) :
    conjM (taggedCfin d L N₀ k M v a s) = taggedCfin d L N₀ k M v a (fun p => conj (s p)) :=
  conjM_taggedCfinU conjM_finalOp s

omit [NeZero L] in
theorem conjM_liftOp (A : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) :
    conjM (Multiscale.liftOp N A) = Multiscale.liftOp N (conjM A) := by
  rw [conjM_eq_matConj, conjM_eq_matConj]
  exact matConj_liftOp (σ := fun _ : L1Torus d N₀ => (1 : ℂ)) (hσ := fun _ => mul_one 1) A

omit [NeZero L] in
theorem conjM_projHC (h : Fin N → ℂ) :
    conjM (projHC h : Matrix (L1Torus d N₀ × Fin N) (L1Torus d N₀ × Fin N) ℂ) =
      projHC fun i => conj (h i) := by
  rw [conjM_eq_matConj]
  exact matConj_projHC (σ := fun _ : L1Torus d N₀ => (1 : ℂ)) (hσ := fun _ => mul_one 1) h

omit [NeZero L] in
theorem conjM_diagonal_chiSum (s : MacIdx d N₀ M → ℂ) :
    conjM (Matrix.diagonal (chiSum d N₀ M s)) =
      Matrix.diagonal (chiSum d N₀ M fun p => conj (s p)) := by
  rw [conjM_eq_matConj]
  exact matConj_diagonal_chiSum Complex.conj_ofReal s

omit [NeZero L] in
/-- **Conjugation of the cut family of a real matrix** (shared core):
`conj (boxCutU(U; h, s)) = boxCutU(U; conj h, conj s)` for `conj U = U`. -/
theorem conjM_boxCutU {U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hU : conjM U = U)
    (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    conjM (boxCutU d N₀ M a U h s) =
      boxCutU d N₀ M a U (fun i => conj (h i)) (fun p => conj (s p)) := by
  rw [conjM_eq_matConj] at hU ⊢
  exact matConj_boxCutU (σ := fun _ : L1Torus d N₀ => (1 : ℂ)) (hσ := fun _ => mul_one 1)
    Complex.conj_ofReal (fun z => Complex.conj_conj z) (fun _ => map_one _)
    (fun _ _ => integral_conj.symm) hU h s

/-- **Conjugation of the cut family**: `conj (boxCut(h, s)) = boxCut(conj h, conj s)`. -/
theorem conjM_boxCut (h : Fin N → ℂ) (s : MacIdx d N₀ M → ℂ) :
    conjM (boxCut d L N₀ k M v a h s) =
      boxCut d L N₀ k M v a (fun i => conj (h i)) (fun p => conj (s p)) :=
  conjM_boxCutU conjM_finalOp h s

end Final

end Balaban.Green
