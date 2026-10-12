/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovarianceSup

/-!
# Spectral lemmas for the covariance (FLUCTUATION.md Lemma 2.4)

* `cov_gap_aux`: a positive definite matrix whose inverse is bounded by `B` in `ℓ²` has
  `Re ⟨v, M v⟩ ≥ B⁻¹ ‖v‖²` (Cauchy–Schwarz for the form `⟨·, M ·⟩`);
* `cov_trace_log_posDef`: for a positive definite `A`, `tr (log A) = log det A` (real logarithm,
  `log A` the functional calculus), `det A > 0`.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Matrix
open scoped ComplexOrder

namespace Balaban.Fluctuation


theorem cov_re_dot_le {ι : Type*} [Fintype ι] (y v : ι → ℂ) :
    (star y ⬝ᵥ v).re ≤ n2 y * n2 v := by
  rw [n2_eq_norm, n2_eq_norm]
  have := re_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 y : EuclideanSpace ℂ ι) (WithLp.toLp 2 v)
  have h2 : inner ℂ (WithLp.toLp 2 y : EuclideanSpace ℂ ι) (WithLp.toLp 2 v) = star y ⬝ᵥ v := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [← h2]; simpa using this


theorem cov_gap_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (hP : M.PosDef)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ f : ι → ℂ, n2 (M⁻¹ *ᵥ f) ≤ B * n2 f) (v : ι → ℂ) :
    Green.sqNorm v ≤ B * (star v ⬝ᵥ M *ᵥ v).re := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [Green.sqNorm]
  have hdet : IsUnit M.det := (isUnit_iff_ne_zero).2 hP.det_pos.ne'
  have hMM : M *ᵥ (M⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have h := hP.star_dotProduct_mulVec_mul_le v (M⁻¹ *ᵥ v)
  simp only [hMM] at h
  set y := M⁻¹ *ᵥ v with hy
  set S := Green.sqNorm v with hS
  have hq := hP.dotProduct_mulVec_pos hv
  have hqim : (star v ⬝ᵥ M *ᵥ v).im = 0 := (Complex.pos_iff.1 hq).2.symm
  have hqre : 0 < (star v ⬝ᵥ M *ᵥ v).re := (Complex.pos_iff.1 hq).1
  have hz : (star v ⬝ᵥ v).re = S := (sqNorm_eq_re_dot v).symm
  have h1 := h.1
  rw [Complex.mul_re, Complex.mul_re] at h1
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, hqim, zero_mul, sub_zero] at h1
  have h2 : (star y ⬝ᵥ v).re ≤ n2 y * n2 v := cov_re_dot_le y v
  have h3 : n2 y * n2 v ≤ B * S := by
    have := mul_le_mul_of_nonneg_right (hB v) (n2_nonneg v)
    have e : n2 v * n2 v = S := by rw [← sq, n2_sq]
    nlinarith
  have hSpos : 0 < S := by
    rw [hS]; unfold Green.sqNorm
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have h4 : (star v ⬝ᵥ v).re * (star v ⬝ᵥ v).re ≤
      (star v ⬝ᵥ M *ᵥ v).re * (star y ⬝ᵥ v).re := by
    nlinarith [mul_self_nonneg (star v ⬝ᵥ v).im]
  have h5 : S * S ≤ (star v ⬝ᵥ M *ᵥ v).re * (B * S) := by
    have := h4
    rw [hz] at this
    nlinarith [mul_le_mul_of_nonneg_left (h2.trans h3) hqre.le]
  nlinarith



section LogDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}

theorem cov_trace_specFun (hA : A.IsHermitian) (f : ℝ → ℂ) :
    (specFun hA f).trace = ∑ i, f (hA.eigenvalues i) := by
  unfold specFun
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have : star (hA.eigenvectorUnitary : Matrix ι ι ℂ) * (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  rw [this, Matrix.one_mul, Matrix.trace_diagonal]

theorem cov_det_posDef (hP : A.PosDef) :
    A.det = ((∏ i, hP.isHermitian.eigenvalues i : ℝ) : ℂ) := by
  rw [hP.isHermitian.det_eq_prod_eigenvalues]
  push_cast; rfl

/-- `det A = exp (tr log A)` for a positive definite `A`, with the real logarithm. -/
theorem cov_trace_log_posDef (hP : A.PosDef) :
    (specFun hP.isHermitian (fun t => (Real.log t : ℂ))).trace = ((Real.log A.det.re : ℝ) : ℂ) ∧
      0 < A.det.re ∧ A.det.im = 0 := by
  have hpos : ∀ i, 0 < hP.isHermitian.eigenvalues i := hP.eigenvalues_pos
  have hdet := cov_det_posDef hP
  have hprod : 0 < ∏ i, hP.isHermitian.eigenvalues i := Finset.prod_pos fun i _ => hpos i
  refine ⟨?_, ?_, ?_⟩
  · rw [cov_trace_specFun, hdet, Complex.ofReal_re, Real.log_prod (fun i _ => (hpos i).ne')]
    push_cast; rfl
  · rw [hdet, Complex.ofReal_re]; exact hprod
  · rw [hdet, Complex.ofReal_im]

end LogDet
end Balaban.Fluctuation
