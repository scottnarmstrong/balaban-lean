/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.GaussianChangeGeneral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The moment-generating function of the standard Gaussian

For the standard Gaussian `pdGaussian ι ℝ` on `ι → ℝ` and a complex linear form `a`,
`∫ exp(∑_x a_x w_x) dγ(w) = exp(½ ∑_x a_x²)` (`pdGaussian_integral_exp_lin`). The proof is the
density formula, Fubini for the product (`integral_fintype_prod_eq_prod`) and the one-dimensional
complex Gaussian integral `integral_cexp_quadratic`.
-/

@[expose] public section

open MeasureTheory Complex Balaban.LargeField

namespace Balaban.Green

variable {ι : Type*} [Fintype ι]

/-- The one-dimensional complex Gaussian integral `∫ (2π)^{-1/2} e^{-t²/2 + c t} dt = e^{c²/2}`. -/
theorem integral_gauss_lin (c : ℂ) :
    ∫ t : ℝ, (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2 + c * t) =
      cexp (c ^ 2 / 2) := by
  have h := integral_cexp_quadratic (b := -(1 / 2 : ℂ)) (by simp) c 0
  simp only [add_zero] at h
  rw [integral_const_mul, h]
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have e1 : ((Real.pi : ℂ) / -(-(1 / 2 : ℂ))) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : (0 : ℂ) - c ^ 2 / (4 * -(1 / 2 : ℂ)) = c ^ 2 / 2 := by ring
  rw [e1, e2, ← mul_assoc]
  have e3 : (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((2 * Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    have hx : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2pi.ne'
    rw [Complex.ofReal_cpow h2pi.le, ← Complex.cpow_add _ _ hx]
    push_cast
    norm_num
  rw [e3, one_mul]


/-- **The moment-generating function of the standard Gaussian**:
`∫ exp(∑_x a_x w_x) dγ(w) = exp(½ ∑_x a_x²)` for a complex linear form `a`. -/
theorem pdGaussian_integral_exp_lin (a : ι → ℂ) :
    ∫ w : ι → ℝ, cexp (∑ x, a x * (w x : ℂ)) ∂(pdGaussian ι ℝ) = cexp (∑ x, a x ^ 2 / 2) := by
  unfold pdGaussian
  have hmeas : Measurable fun ψ : ι → ℝ => ENNReal.ofReal ((2 * Real.pi) ^ (-(pdDim ι ℝ : ℝ) / 2) *
      Real.exp (-(1 / 2) * ∑ x, ‖ψ x‖ ^ 2)) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ w : ι → ℝ, (ENNReal.ofReal ((2 * Real.pi) ^ (-(pdDim ι ℝ : ℝ) / 2) *
        Real.exp (-(1 / 2) * ∑ x, ‖w x‖ ^ 2))).toReal • cexp (∑ x, a x * (w x : ℂ)) =
      ∏ x, ((((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        cexp (-(1 / 2 : ℂ) * ((w x : ℝ) : ℂ) ^ 2 + a x * ((w x : ℝ) : ℂ))) := by
    intro w
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hr : (2 * Real.pi) ^ (-(pdDim ι ℝ : ℝ) / 2) =
        ((2 * Real.pi) ^ (-(1 / 2 : ℝ))) ^ (Fintype.card ι) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2pi.le]
      congr 1
      simp [pdDim]
      ring
    rw [ENNReal.toReal_ofReal (by positivity), hr, Complex.real_smul]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    rw [← Complex.exp_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod (f := fun x (t : ℝ) => (((2 * Real.pi) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    cexp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2 + a x * t)) (μ := fun _ => (volume : Measure ℝ))]
  simp_rw [integral_gauss_lin]
  rw [← Complex.exp_sum]

section Linear

variable [DecidableEq ι]

/-- **The Gaussian average of a linear source in the variable `v = K^{-1/2} w`**:
`∫ exp(∑_x J_x v_x) dγ(w) = exp(½ ∑_{x,y} J_x K⁻¹(x,y) J_y)`, `v = K^{-1/2} w`, for a positive
definite `K` and a complex linear form `J`. -/
theorem pdGaussian_integral_exp_lin_sqrtInv {K : Matrix ι ι ℝ} (hK : K.PosDef) (J : ι → ℂ) :
    ∫ w : ι → ℝ, cexp (∑ x, J x * ((matAct (pdSqrtInv K) w x : ℝ) : ℂ)) ∂(pdGaussian ι ℝ) =
      cexp ((1 / 2 : ℂ) * ∑ x, ∑ y, J x * ((K⁻¹ x y : ℝ) : ℂ) * J y) := by
  set S := pdSqrtInv K with hS
  set a : ι → ℂ := fun y => ∑ x, J x * ((S x y : ℝ) : ℂ) with ha
  have h1 : ∀ w : ι → ℝ, ∑ x, J x * ((matAct S w x : ℝ) : ℂ) = ∑ y, a y * (w y : ℂ) := by
    intro w
    simp only [matAct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, ha,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  simp_rw [h1]
  rw [pdGaussian_integral_exp_lin a]
  congr 1
  have hSS : ∀ x x', ∑ y, S x y * S x' y = K⁻¹ x x' := by
    intro x x'
    have := congrFun (congrFun (pdSqrtInv_mul_self hK) x) x'
    rw [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hT := congrFun (congrFun (pdSqrtInv_transpose K) x') y
    simp only [Matrix.transpose_apply] at hT
    rw [← hS] at hT
    show S x y * S x' y = S x y * S y x'
    rw [hT]
  have h2 : ∀ y, a y ^ 2 = ∑ x, ∑ x', J x * J x' * ((S x y * S x' y : ℝ) : ℂ) := by
    intro y
    simp only [ha, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    push_cast; ring
  simp_rw [h2, ← Finset.sum_div]
  rw [Finset.sum_comm]
  rw [div_eq_inv_mul, show ((2 : ℂ)⁻¹) = 1 / 2 by norm_num]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, hSS x x']
  ring

end Linear

end Balaban.Green
