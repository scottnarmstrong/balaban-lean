/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# `det (exp A) = exp (trace A)` for complex square matrices

Jacobi's formula at the identity (from Mathlib's Taylor expansion `Matrix.det_one_add_smul`),
the derivative of `u ↦ det (exp (u A))`, and uniqueness for the linear ODE
`f' = tr A · f`.
-/

@[expose] public section

open NormedSpace Matrix Polynomial

namespace Balaban

section
variable {n : Type*} [Fintype n] [DecidableEq n]
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

theorem det_hasFDerivAt_one_apply (M : Matrix n n ℂ) :
    ∃ D : Matrix n n ℂ →L[ℂ] ℂ, HasFDerivAt (fun X : Matrix n n ℂ => X.det) D 1 ∧ D M = trace M := by
  have hd : Differentiable ℂ (fun X : Matrix n n ℂ => X.det) := by
    intro X
    simp only [Matrix.det_apply]
    fun_prop
  refine ⟨fderiv ℂ (fun X : Matrix n n ℂ => X.det) 1, (hd 1).hasFDerivAt, ?_⟩
  have h1 : HasDerivAt (fun r : ℂ => (1 + r • M).det) (fderiv ℂ (fun X : Matrix n n ℂ => X.det) 1 M) 0 := by
    have hl : HasDerivAt (fun r : ℂ => (1 : Matrix n n ℂ) + r • M) M 0 := by
      have := ((hasDerivAt_id (0:ℂ)).smul_const M).const_add (1 : Matrix n n ℂ)
      rw [one_smul] at this; exact this
    have hf : HasFDerivAt (fun X : Matrix n n ℂ => X.det)
        (fderiv ℂ (fun X : Matrix n n ℂ => X.det) 1) ((fun r : ℂ => (1 : Matrix n n ℂ) + r • M) 0) := by
      simpa using (hd 1).hasFDerivAt
    exact hf.comp_hasDerivAt (0:ℂ) hl
  have h2 : HasDerivAt (fun r : ℂ => (1 + r • M).det) (trace M) 0 := by
    have hp : HasDerivAt (fun r : ℂ => 1 + trace M * r + (det (1 + (X : ℂ[X]) • M.map C)).divX.divX.eval r * r ^ 2) (trace M) 0 := by
      have hq := (Polynomial.hasDerivAt (det (1 + (X : ℂ[X]) • M.map C)).divX.divX (0:ℂ))
      have h3 := (hq.mul (hasDerivAt_pow 2 (0:ℂ)))
      have h4 := ((hasDerivAt_id (0:ℂ)).const_mul (trace M)).const_add (1:ℂ)
      have := h4.add h3
      exact HasDerivAt.congr_deriv (this.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun r => by simp)) (by simp)
    refine hp.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun r => Matrix.det_one_add_smul r M
  exact h1.unique h2


theorem hasDerivAt_det_exp_smul (A : Matrix n n ℂ) (t : ℂ) :
    HasDerivAt (fun u : ℂ => (exp (u • A)).det) (trace A * (exp (t • A)).det) t := by
  obtain ⟨D, hD, hDA⟩ := det_hasFDerivAt_one_apply A
  have he : HasDerivAt (fun u : ℂ => exp (u • A)) (exp ((0:ℂ) • A) * A) 0 :=
    hasDerivAt_exp_smul_const A (0:ℂ)
  have hD' : HasFDerivAt (fun X : Matrix n n ℂ => X.det) D (exp ((0:ℂ) • A)) := by
    simpa using hD
  have hg := hD'.comp_hasDerivAt (0:ℂ) he
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hg
  replace hg : HasDerivAt (fun u : ℂ => (exp (u • A)).det) (trace A) 0 := by
    exact hg.congr_deriv hDA
  have hs : HasDerivAt (fun s : ℂ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have hg' : HasDerivAt (fun s : ℂ => ((fun u : ℂ => (exp (u • A)).det) (s - t)))
      (trace A * 1) t := by
    have hg0 : HasDerivAt (fun u : ℂ => (exp (u • A)).det) (trace A) (t - t) := by
      rw [sub_self]; exact hg
    have := HasDerivAt.scomp (h := fun s : ℂ => s - t) t hg0 hs
    exact this.congr_deriv (by simp)
  have := hg'.const_mul (exp (t • A)).det
  refine HasDerivAt.congr_deriv (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)) (by ring)
  have hc : Commute (t • A) ((s - t) • A) := by
    simp [Commute, SemiconjBy, smul_smul, mul_comm]
  have : exp (s • A) = exp (t • A) * exp ((s - t) • A) := by
    rw [← Matrix.exp_add_of_commute _ _ hc, ← add_smul, add_sub_cancel]
  simp [this, Matrix.det_mul]

/-- `det (exp A) = exp (trace A)` for complex square matrices. -/
theorem det_exp_eq_exp_trace (A : Matrix n n ℂ) :
    (exp A).det = Complex.exp (trace A) := by
  let g : ℂ → ℂ := fun u => (exp (u • A)).det * Complex.exp (-(u * trace A))
  have hg : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 := hasDerivAt_det_exp_smul A u
    have h2 : HasDerivAt (fun u : ℂ => Complex.exp (-(u * trace A))) (Complex.exp (-(u * trace A)) * (-(trace A))) u := by
      have := ((hasDerivAt_id u).mul_const (trace A)).neg.cexp
      simpa using this
    have := h1.mul h2
    refine this.congr_deriv ?_
    ring
  have hc : g 1 = g 0 := by
    have := is_const_of_deriv_eq_zero (f := g) (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv) 1 0
    exact this
  simp only [g, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, zero_mul, neg_zero,
    Complex.exp_zero, mul_one, one_mul] at hc
  calc (exp A).det = (exp A).det * Complex.exp (-trace A) * Complex.exp (trace A) := by
        rw [mul_assoc, ← Complex.exp_add]; simp
    _ = _ := by rw [hc]; simp

end
end Balaban
