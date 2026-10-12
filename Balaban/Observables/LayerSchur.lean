/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Symmetry.Rotation
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The stabilizer argument of Lemma 2.1 (OBSERVABLES.md §2.2): the commutant of `O(N-1)`

Let `h ∈ ℝ^N` with `h·h = 1`.  The stabilizer of `h` in `O(N)` is
`stabilizer h = {S | Sᵀ S = 1, S h = h}` (`≅ O(N-1)` acting on `h^⊥`).  A matrix commuting with
every element of the stabilizer is `a hhᵀ + b (1 - hhᵀ)` (`commutant_stabilizer`):

* the Schur step of Lemma 2.1, valid for every `N` (for `N = 2` the space `h^⊥` is a line, for
  `N = 1` it is `0`); no irreducibility of `O(N-1)` on `h^⊥` is used, only the sign changes and the
  coordinate exchanges in an orthonormal basis with first vector `h`;
* the proof goes through `commutant_coord`, the same statement in the basis where `h = e_{i₀}`
  (commuting with `diag(1, …, -1_i, …, 1)` and with the transposition matrices of `i, j ≠ i₀`).
-/

@[expose] public section

open Matrix

namespace Balaban.Observables

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The stabilizer of `h` in `O(N)`: real orthogonal matrices fixing `h`. -/
def stabilizer (h : ι → ℝ) : Set (Matrix ι ι ℝ) := {S | Sᵀ * S = 1 ∧ S *ᵥ h = h}

/-- The sign change at the coordinate `i`. -/
def signMat (i : ι) : Matrix ι ι ℝ := Matrix.diagonal fun j => if j = i then -1 else 1

theorem signMat_transpose_mul (i : ι) : (signMat i)ᵀ * signMat i = 1 := by
  rw [signMat, diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext j; split_ifs <;> norm_num

theorem signMat_mulVec_single {i i0 : ι} (h : i ≠ i0) :
    signMat i *ᵥ (Pi.single i0 1 : ι → ℝ) = Pi.single i0 1 := by
  rw [signMat, diagonal_mulVec_single]
  ext j
  by_cases hj : j = i0
  · subst hj; simp [h.symm]
  · simp [hj]

theorem permMat_transpose_mul (σ : Equiv.Perm ι) :
    (σ.permMatrix ℝ)ᵀ * σ.permMatrix ℝ = 1 := by
  rw [transpose_permMatrix, ← permMatrix_mul]
  simp

theorem permMat_mulVec_single {σ : Equiv.Perm ι} {i0 : ι} (h : σ i0 = i0) :
    σ.permMatrix ℝ *ᵥ (Pi.single i0 1 : ι → ℝ) = Pi.single i0 1 := by
  rw [permMatrix_mulVec]
  ext j
  have hj : σ j = i0 ↔ j = i0 := ⟨fun e => σ.injective (e.trans h.symm), fun e => e ▸ h⟩
  simp [Pi.single_apply, hj]

/-- **The commutant in the basis where `h = e_{i₀}`**: a matrix commuting with the sign changes
and the exchanges of the coordinates `≠ i₀` is `diag(a, b, …, b)`. -/
theorem commutant_coord (i0 : ι) (A : Matrix ι ι ℝ)
    (hsign : ∀ i, i ≠ i0 → signMat i * A = A * signMat i)
    (hswap : ∀ i j, i ≠ i0 → j ≠ i0 → i ≠ j →
      (Equiv.swap i j).permMatrix ℝ * A = A * (Equiv.swap i j).permMatrix ℝ) :
    ∃ a b : ℝ, A = Matrix.diagonal fun r => if r = i0 then a else b := by
  have hoff : ∀ r s, r ≠ s → A r s = 0 := by
    intro r s hrs
    by_cases hr : r = i0
    · subst hr
      have hs : s ≠ r := fun h => hrs h.symm
      have := congrFun (congrFun (hsign s hs) r) s
      simp [signMat, diagonal_mul, mul_diagonal] at this
      have h2 := this (Ne.symm hs)
      linarith
    · have := congrFun (congrFun (hsign r hr) r) s
      simp [signMat, diagonal_mul, mul_diagonal, hrs.symm] at this
      linarith
  have hdiag : ∀ i j, i ≠ i0 → j ≠ i0 → A i i = A j j := by
    intro i j hi hj
    by_cases hij : i = j
    · rw [hij]
    · have := congrFun (congrFun (hswap i j hi hj hij) i) j
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.mul_apply, Equiv.toPEquiv_apply,
        Equiv.swap_apply_left, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at this
      exact this.symm
  by_cases hex : ∃ i, i ≠ i0
  · obtain ⟨i1, hi1⟩ := hex
    refine ⟨A i0 i0, A i1 i1, ?_⟩
    ext r s
    by_cases hrs : r = s
    · subst hrs
      by_cases hr : r = i0
      · subst hr; simp
      · simp [hr, hdiag r i1 hr hi1]
    · simp [Matrix.diagonal_apply_ne _ hrs, hoff r s hrs]
  · push Not at hex
    refine ⟨A i0 i0, 0, ?_⟩
    ext r s
    by_cases hrs : r = s
    · subst hrs; simp [hex r]
    · simp [Matrix.diagonal_apply_ne _ hrs, hoff r s hrs]

/-- The conjugation of the commutation relation into the basis `b` (`b i₀ = h`). -/
theorem conj_commute {h : ι → ℝ} {A B T : Matrix ι ι ℝ} {i0 : ι}
    (hA : ∀ S ∈ stabilizer h, S * A = A * S) (hB : Bᵀ * B = 1) (hB' : B * Bᵀ = 1)
    (hBh : B *ᵥ h = Pi.single i0 1) (hBe : Bᵀ *ᵥ (Pi.single i0 1 : ι → ℝ) = h)
    (hT : Tᵀ * T = 1) (hTe : T *ᵥ (Pi.single i0 1 : ι → ℝ) = Pi.single i0 1) :
    T * (B * A * Bᵀ) = (B * A * Bᵀ) * T := by
  have hS : Bᵀ * T * B ∈ stabilizer h := by
    refine ⟨?_, ?_⟩
    · have : (Bᵀ * T * B)ᵀ * (Bᵀ * T * B) = Bᵀ * (Tᵀ * (B * Bᵀ) * T) * B := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [this, hB', Matrix.mul_one, hT, Matrix.mul_one, hB]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBh, hTe, hBe]
  have h1 := hA _ hS
  have e1 : T * B = B * (Bᵀ * T * B) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB', Matrix.one_mul]
  have e2 : (Bᵀ * T * B) * Bᵀ = Bᵀ * T := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hB', Matrix.mul_one]
  calc T * (B * A * Bᵀ) = (T * B) * A * Bᵀ := by simp only [Matrix.mul_assoc]
    _ = B * ((Bᵀ * T * B) * A) * Bᵀ := by rw [e1]; simp only [Matrix.mul_assoc]
    _ = B * (A * (Bᵀ * T * B)) * Bᵀ := by rw [h1]
    _ = B * A * ((Bᵀ * T * B) * Bᵀ) := by simp only [Matrix.mul_assoc]
    _ = (B * A * Bᵀ) * T := by rw [e2]; simp only [Matrix.mul_assoc]

/-- **The Schur step of Lemma 2.1**: a real matrix commuting with the stabilizer of the unit vector
`h` in `O(N)` is `a hhᵀ + b (1 - hhᵀ)`: it preserves the line `ℝh` and acts as a scalar on `h^⊥`.
(For `N = 2` the space `h^⊥` is a line; no irreducibility of `O(N-1)` is used.) -/
theorem commutant_stabilizer [Nonempty ι] {h : ι → ℝ} (hh : h ⬝ᵥ h = 1) {A : Matrix ι ι ℝ}
    (hA : ∀ S ∈ stabilizer h, S * A = A * S) :
    ∃ a b : ℝ, A = a • vecMulVec h h + b • (1 - vecMulVec h h) := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hu : ‖(WithLp.toLp 2 h : EuclideanSpace ℝ ι)‖ = 1 := by
    have h1 := Symmetry.inner_toLp h h
    rw [hh, real_inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (WithLp.toLp 2 h : EuclideanSpace ℝ ι)]
  obtain ⟨b, hb⟩ := Symmetry.exists_basis_single (i := i0) hu
  set B := Symmetry.basisMatrix b with hBdef
  have hB : Bᵀ * B = 1 := Symmetry.basisMatrix_transpose_mul b
  have hB' : B * Bᵀ = 1 := mul_eq_one_comm.mp hB
  have hBh : B *ᵥ h = Pi.single i0 1 := by
    ext k
    rw [Symmetry.basisMatrix_mulVec, ← hb]
    have := orthonormal_iff_ite.mp b.orthonormal k i0
    rw [this]
    by_cases hk : k = i0 <;> simp [hk]
  have hBe : Bᵀ *ᵥ (Pi.single i0 1 : ι → ℝ) = h := by
    ext l
    have : (b i0) l = h l := by rw [hb]
    simp [hBdef, Symmetry.basisMatrix, Matrix.mulVec, dotProduct, Pi.single_apply, this]
  have hcomm : ∀ T : Matrix ι ι ℝ, Tᵀ * T = 1 → T *ᵥ (Pi.single i0 1 : ι → ℝ) = Pi.single i0 1 →
      T * (B * A * Bᵀ) = (B * A * Bᵀ) * T := fun T hT hTe =>
    conj_commute (i0 := i0) hA hB hB' hBh hBe hT hTe
  obtain ⟨a, b', hdiag⟩ := commutant_coord i0 (B * A * Bᵀ)
    (fun i hi => hcomm _ (signMat_transpose_mul i) (signMat_mulVec_single hi))
    (fun i j hi hj hij => hcomm _ (permMat_transpose_mul _)
      (permMat_mulVec_single (Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm))) 
  have hAeq : A = Bᵀ * (B * A * Bᵀ) * B := by
    have : Bᵀ * (B * A * Bᵀ) * B = (Bᵀ * B) * A * (Bᵀ * B) := by simp only [Matrix.mul_assoc]
    rw [this, hB, Matrix.one_mul, Matrix.mul_one]
  have hdec : (Matrix.diagonal fun r => if r = i0 then a else b' : Matrix ι ι ℝ) =
      b' • (1 : Matrix ι ι ℝ) + (a - b') • vecMulVec (Pi.single i0 1) (Pi.single i0 1) := by
    ext r s
    by_cases hrs : r = s
    · subst hrs
      by_cases hr : r = i0
      · subst hr; simp [vecMulVec_apply]
      · simp [hr, vecMulVec_apply]
    · simp [hrs, vecMulVec_apply, Pi.single_apply]
      intro h1 h2
      exact absurd (h2.trans h1.symm) hrs
  have hproj : Bᵀ * vecMulVec (Pi.single i0 1) (Pi.single i0 1) * B = vecMulVec h h := by
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hBe, ← Matrix.mulVec_transpose, hBe]
  refine ⟨a, b', ?_⟩
  rw [hAeq, hdiag, hdec, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, hB, hproj]
  ext r s
  simp
  ring

end Balaban.Observables
