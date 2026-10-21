/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteFirst

/-!
# The finite-range whitening of a real matrix is real

For a matrix `A` with real entries the matrices `K = 1 - (γ/J²) A`, the truncated square root
`S_R(K) = ∑_{n ≤ R} w_n Kⁿ` (real coefficients `w_n`) and the whitening
`W = (J²/γ)^{-1/2} S_R(K)` have real entries (`whiteW_im_eq_zero`). The proof is that complex
conjugation of the entries is a ring endomorphism of the matrix algebra fixing the real scalars.
-/

@[expose] public section

open Matrix Balaban.Green Balaban.LargeField.Base
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise complex conjugation of a complex matrix, as a ring endomorphism. -/
noncomputable abbrev matConj : Matrix ι ι ℂ →+* Matrix ι ι ℂ := (starRingEnd ℂ).mapMatrix

theorem matConj_smul_real (c : ℝ) (A : Matrix ι ι ℂ) :
    matConj ((c : ℂ) • A) = (c : ℂ) • matConj A := by
  ext i j
  simp [matConj]

theorem sqrtTrunc_conj (A : Matrix ι ι ℂ) (R : ℕ) :
    matConj (sqrtTrunc A R) = sqrtTrunc (matConj A) R := by
  unfold sqrtTrunc
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [matConj_smul_real, map_pow]

theorem whiteK_conj (γ J : ℝ) (A : Matrix ι ι ℂ) :
    matConj (whiteK γ J A) = whiteK γ J (matConj A) := by
  unfold whiteK
  rw [map_sub, map_one, matConj_smul_real]

theorem whiteW_conj (γ J : ℝ) (A : Matrix ι ι ℂ) (R : ℕ) :
    matConj (whiteW γ J A R) = whiteW γ J (matConj A) R := by
  unfold whiteW
  rw [matConj_smul_real, sqrtTrunc_conj, whiteK_conj]

/-- The whitening of a real matrix is real. -/
theorem whiteW_im_eq_zero (γ J : ℝ) (A : Matrix ι ι ℂ) (hA : ∀ i j, (A i j).im = 0) (R : ℕ)
    (i j : ι) : (whiteW γ J A R i j).im = 0 := by
  have h : matConj A = A := by
    ext p q
    simp only [matConj, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact Complex.conj_eq_iff_im.2 (hA p q)
  have h2 := congrFun (congrFun (whiteW_conj γ J A R) i) j
  rw [h] at h2
  simp only [matConj, RingHom.mapMatrix_apply, Matrix.map_apply] at h2
  exact Complex.conj_eq_iff_im.1 h2

end Balaban.LargeField.FRWhite
