/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FunProp

/-!
# Quadratic forms from resolvent differences

If `x²` times the resolvent difference `(x + A)⁻¹ - (x + A')⁻¹` has quadratic form bounded by `η`
for all large `x`, then the quadratic form of `A' - A` is bounded by `η`
(`norm_quad_sub_le_of_resolvent`): `x (x + A)⁻¹ → 1` as `x → ∞`.
-/

@[expose] public section

open Matrix Filter Topology

namespace Balaban

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tendsto_inv_one_add_smul (A : Matrix ι ι ℂ) :
    Tendsto (fun x : ℝ => ((1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A)⁻¹) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => (1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x : ℝ => ((x : ℂ)⁻¹)) atTop (𝓝 0) := by
      have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_id
      have h := (Complex.continuous_ofReal.tendsto 0).comp this
      simpa [Function.comp_def] using h
    have := (h0.smul_const A).const_add (1 : Matrix ι ι ℂ)
    simpa using this
  have hc : ContinuousAt (Inv.inv : Matrix ι ι ℂ → Matrix ι ι ℂ) 1 := by
    refine continuousAt_matrix_inv _ ?_
    simp only [Matrix.det_one]
    have : (Ring.inverse : ℂ → ℂ) = Inv.inv := Ring.inverse_eq_inv'
    rw [this]; exact continuousAt_inv₀ one_ne_zero
  have := hc.tendsto.comp h1
  simpa [Function.comp_def, inv_one] using this

theorem tendsto_smul_resolvent (A : Matrix ι ι ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) atTop (𝓝 1) := by
  refine (tendsto_inv_one_add_smul A).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : (x : ℂ) • (1 : Matrix ι ι ℂ) + A = (x : ℂ) • ((1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hx', one_smul]
  rw [this]
  have key : ((x : ℂ) • ((1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A))⁻¹ =
      (x : ℂ)⁻¹ • ((1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A)⁻¹ := by
    by_cases hu : IsUnit ((1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A).det
    · exact Matrix.inv_smul' _ (Units.mk0 (x : ℂ) hx') hu
    · have h2 : ¬ IsUnit (((x : ℂ) • ((1 : Matrix ι ι ℂ) + ((x : ℂ)⁻¹) • A))).det := by
        rw [Matrix.det_smul]
        intro h
        exact hu ((IsUnit.mul_iff.1 h).2)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ hu,
        smul_zero]
  rw [key, smul_smul, mul_inv_cancel₀ hx', one_smul]


theorem norm_quad_sub_le_of_resolvent (A A' : Matrix ι ι ℂ) (v : ι → ℂ) {η : ℝ}
    (hA : ∀ x : ℝ, 0 < x → IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A))
    (hA' : ∀ x : ℝ, 0 < x → IsUnit ((x : ℂ) • (1 : Matrix ι ι ℂ) + A'))
    (h : ∀ x : ℝ, 1 ≤ x → ‖star v ⬝ᵥ
      ((((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ - ((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹) *ᵥ v)‖ ≤
        η / x ^ 2) :
    ‖star v ⬝ᵥ ((A' - A) *ᵥ v)‖ ≤ η := by
  set T : ℝ → Matrix ι ι ℂ := fun x =>
    ((x : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹) * (A' - A) *
      ((x : ℂ) • ((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹) with hT
  have hTlim : Tendsto T atTop (𝓝 (A' - A)) := by
    have := ((tendsto_smul_resolvent A).mul_const (A' - A)).mul (tendsto_smul_resolvent A')
    simpa [hT] using this
  have hcont : Continuous (fun M : Matrix ι ι ℂ => ‖star v ⬝ᵥ (M *ᵥ v)‖) := by fun_prop
  have hlim := (hcont.tendsto _).comp hTlim
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hid : T x = (x : ℂ) ^ 2 • (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ -
      ((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹) := by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hA x hx0)
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hA' x hx0)
    have e1 : ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A) = 1 :=
      Matrix.nonsing_inv_mul _ hu
    have e2 : ((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹ * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A') = 1 :=
      Matrix.nonsing_inv_mul _ hu'
    have e3 : ((x : ℂ) • (1 : Matrix ι ι ℂ) + A) * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hu
    have e4 : ((x : ℂ) • (1 : Matrix ι ι ℂ) + A') * ((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ hu'
    set RA := ((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹
    set RB := ((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹
    have hdiff : RA - RB = RA * (A' - A) * RB := by
      have : A' - A = ((x : ℂ) • (1 : Matrix ι ι ℂ) + A') - ((x : ℂ) • (1 : Matrix ι ι ℂ) + A) := by
        abel
      rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc RA, e4, Matrix.mul_one, e1,
        Matrix.one_mul]
    simp only [hT]
    rw [hdiff]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]
    rfl
  simp only [Function.comp, hid]
  rw [Matrix.smul_mulVec, dotProduct_smul, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx0.le,
    Matrix.sub_mulVec]
  have := h x hx
  rw [Matrix.sub_mulVec] at this
  calc x ^ 2 * ‖star v ⬝ᵥ ((((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹ *ᵥ v) - ((((x : ℂ) • (1 : Matrix ι ι ℂ) + A')⁻¹) *ᵥ v))‖
      ≤ x ^ 2 * (η / x ^ 2) := by gcongr
    _ = η := by field_simp

end
end Balaban
