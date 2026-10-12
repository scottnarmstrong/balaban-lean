/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Complex.Basic
public import Balaban.Green.Coercive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Scalar and matrix analysis for the resolvent integrals of I-4c

* `contOn_matrix_inv`: the inverse of a continuous family of invertible matrices is continuous;
* `integral_rpow_inv_add`: `∫₀^∞ x^{-1/2} (λ + x)⁻¹ dx = π λ^{-1/2}`, with integrability;
* `integral_inv_add_sub`: `∫₀^∞ ((λ + x)⁻¹ - (μ + x)⁻¹) dx = log (μ/λ)`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology Matrix

namespace Balaban.Localization

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Set ℝ}

theorem contOn_matrix_inv {F : ℝ → Matrix ι ι ℂ} (hF : ContinuousOn F S)
    (hU : ∀ x ∈ S, IsUnit (F x)) : ContinuousOn (fun x => (F x)⁻¹) S := by
  have hdet : ContinuousOn (fun x => (F x).det) S :=
    (continuous_id.matrix_det).comp_continuousOn hF
  have hadj : ContinuousOn (fun x => (F x).adjugate) S :=
    (continuous_id.matrix_adjugate).comp_continuousOn hF
  have hne : ∀ x ∈ S, (F x).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).1 (hU x hx)).ne_zero
  have : ∀ x ∈ S, (F x)⁻¹ = ((F x).det)⁻¹ • (F x).adjugate := by
    intro x hx
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContinuousOn.congr (hdet.inv₀ hne |>.smul hadj) this

end Matrix

section Scalar

theorem integral_Ioi_inv_sq_add {μ : ℝ} (hμ : 0 < μ) :
    ∫ x in Ioi (0 : ℝ), (μ ^ 2 + x ^ 2)⁻¹ = π / (2 * μ) := by
  have h1 : ∫ x in Ioi (0 : ℝ), (1 + (μ⁻¹ * x) ^ 2)⁻¹ = μ * (π / 2) := by
    rw [integral_comp_mul_left_Ioi (fun t : ℝ => (1 + t ^ 2)⁻¹) 0 (inv_pos.2 hμ)]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, arctan_zero, sub_zero, inv_inv, smul_eq_mul]
  have h2 : ∀ x : ℝ, (μ ^ 2 + x ^ 2)⁻¹ = (μ ^ 2)⁻¹ * (1 + (μ⁻¹ * x) ^ 2)⁻¹ := by
    intro x
    field_simp
  simp_rw [h2]
  rw [integral_const_mul, h1]
  field_simp

theorem integrableOn_Ioi_inv_sq_add {μ : ℝ} (hμ : 0 < μ) :
    IntegrableOn (fun x : ℝ => (μ ^ 2 + x ^ 2)⁻¹) (Ioi 0) := by
  have h2 : ∀ x : ℝ, (μ ^ 2 + x ^ 2)⁻¹ = (μ ^ 2)⁻¹ * (1 + (μ⁻¹ * x) ^ 2)⁻¹ := by
    intro x
    field_simp
  simp_rw [h2]
  exact ((integrable_inv_one_add_mul_sq (inv_ne_zero hμ.ne')).const_mul _).integrableOn

/-- The substitution `y = x²` on `(0, ∞)`. -/
theorem rpow_two_image : (fun x : ℝ => x ^ (2 : ℝ)) '' Ioi 0 = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact rpow_pos_of_pos hx _
  · intro hy
    refine ⟨y ^ (1 / (2 : ℝ)), rpow_pos_of_pos hy _, ?_⟩
    simp only
    rw [← rpow_mul hy.le]
    norm_num

theorem sub_rpow_aux {l x : ℝ} (hx : 0 < x) :
    ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • ((x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (l + x ^ (2 : ℝ))⁻¹) =
      2 * (l + x ^ 2)⁻¹ := by
  have h1 : (x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) = x⁻¹ := by
    rw [← rpow_mul hx.le]
    norm_num
    exact rpow_neg_one x
  have h2 : x ^ ((2 : ℝ) - 1) = x := by norm_num
  have h3 : x ^ (2 : ℝ) = x ^ 2 := by exact_mod_cast rpow_natCast x 2
  rw [smul_eq_mul, h1, h2, h3]
  field_simp

theorem integrableOn_rpow_inv_add {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (l + y)⁻¹) (Ioi 0) := by
  have hs : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  have key := (integrableOn_image_iff_integrableOn_abs_deriv_smul hs
    (f := fun x : ℝ => x ^ (2 : ℝ)) (f' := fun x => (2 : ℝ) * x ^ ((2 : ℝ) - 1))
    (fun x hx => (hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hx).ne')).hasDerivWithinAt
      |>.congr_deriv (by simp))
    ((rpow_left_injOn (by norm_num : (2 : ℝ) ≠ 0)).mono (by
      intro x hx; exact le_of_lt hx))
    (fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (l + y)⁻¹))
  rw [rpow_two_image] at key
  rw [key]
  have hint : IntegrableOn (fun x : ℝ => 2 * (l + x ^ 2)⁻¹) (Ioi 0) := by
    have := integrableOn_Ioi_inv_sq_add (μ := Real.sqrt l) (Real.sqrt_pos.2 hl)
    rw [Real.sq_sqrt hl.le] at this
    exact this.const_mul 2
  refine hint.congr_fun (fun x hx => ?_) hs
  have hx' := mem_Ioi.mp hx
  have e := sub_rpow_aux (l := l) hx'
  show 2 * (l + x ^ 2)⁻¹ = |2 * x ^ ((2 : ℝ) - 1)| • _
  rw [abs_of_nonneg (by positivity)]
  exact e.symm

theorem integral_rpow_inv_add {l : ℝ} (hl : 0 < l) :
    ∫ y in Ioi (0 : ℝ), y ^ (-(1 / 2 : ℝ)) * (l + y)⁻¹ = π / Real.sqrt l := by
  have h := integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ (-(1 / 2 : ℝ)) * (l + y)⁻¹)
    (p := (2 : ℝ)) (by norm_num)
  rw [← h]
  have : ∫ x in Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
      ((x ^ (2 : ℝ)) ^ (-(1 / 2 : ℝ)) * (l + x ^ (2 : ℝ))⁻¹) =
      ∫ x in Ioi (0 : ℝ), 2 * (l + x ^ 2)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact sub_rpow_aux (mem_Ioi.mp hx)
  rw [this, integral_const_mul]
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  have e := integral_Ioi_inv_sq_add hs
  rw [Real.sq_sqrt hl.le] at e
  rw [e]
  field_simp

theorem integrableOn_inv_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => ((a + x)⁻¹) ^ 2) (Ioi 0) := by
  have h := integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => -(a + x)⁻¹)
    (g' := fun x : ℝ => ((a + x)⁻¹) ^ 2) (a := 0) (l := 0)
    (by
      refine ContinuousAt.continuousWithinAt ?_
      have : a + 0 ≠ 0 := by simp [ha.ne']
      fun_prop (disch := simp [ha.ne']))
    (fun x hx => by
      have hx' : 0 < a + x := by have := mem_Ioi.mp hx; linarith
      have h := (((hasDerivAt_id x).const_add a).inv hx'.ne').neg
      refine h.congr_deriv ?_
      simp only [id_eq]
      field_simp)
    (fun x _ => sq_nonneg _)
    (by
      have : Tendsto (fun x : ℝ => a + x) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
      simpa using (tendsto_inv_atTop_zero.comp this).neg)
  exact h

theorem integrableOn_rpow_inv_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) * ((a + x)⁻¹) ^ 2) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_rpow_inv_add ha).const_mul a⁻¹) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul ?_ ?_
    · exact fun x hx => (Real.continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hx).ne')).continuousWithinAt
    · refine ContinuousOn.pow (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_) 2
      have := mem_Ioi.mp hx; linarith
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := mem_Ioi.mp hx
    have h1 : 0 < a + x := by linarith
    have h2 : (a + x)⁻¹ ≤ a⁻¹ := inv_anti₀ ha (by linarith)
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos hx0 _
    rw [norm_mul, Real.norm_of_nonneg h3.le, Real.norm_of_nonneg (by positivity)]
    calc x ^ (-(1 / 2 : ℝ)) * ((a + x)⁻¹) ^ 2
        = x ^ (-(1 / 2 : ℝ)) * ((a + x)⁻¹ * (a + x)⁻¹) := by ring
      _ ≤ x ^ (-(1 / 2 : ℝ)) * (a⁻¹ * (a + x)⁻¹) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by positivity)) h3.le
      _ = a⁻¹ * (x ^ (-(1 / 2 : ℝ)) * (a + x)⁻¹) := by ring

theorem integral_inv_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), ((a + x)⁻¹) ^ 2 = a⁻¹ := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x : ℝ => -(a + x)⁻¹)
    (f' := fun x : ℝ => ((a + x)⁻¹) ^ 2) (a := 0) (m := 0)
    (by
      refine ContinuousAt.continuousWithinAt ?_
      have : a + 0 ≠ 0 := by simp [ha.ne']
      fun_prop (disch := simp [ha.ne']))
    (fun x hx => by
      have hx' : 0 < a + x := by have := mem_Ioi.mp hx; linarith
      have h := (((hasDerivAt_id x).const_add a).inv hx'.ne').neg
      refine h.congr_deriv ?_
      simp only [id_eq]
      field_simp)
    (integrableOn_inv_add_sq ha)
    (by
      have : Tendsto (fun x : ℝ => a + x) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
      simpa using (tendsto_inv_atTop_zero.comp this).neg)
  rw [h]
  simp

theorem integral_rpow_inv_add_sq_le {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * ((a + x)⁻¹) ^ 2 ≤ a⁻¹ * (π / Real.sqrt a) := by
  rw [← integral_rpow_inv_add ha, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ((integrableOn_rpow_inv_add ha).const_mul _) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => by
      have := mem_Ioi.mp hx
      have : 0 < x ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos this _
      positivity)
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := mem_Ioi.mp hx
    have h2 : (a + x)⁻¹ ≤ a⁻¹ := inv_anti₀ ha (by linarith)
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := rpow_pos_of_pos hx0 _
    have h4 : 0 < (a + x)⁻¹ := inv_pos.2 (by linarith)
    calc x ^ (-(1 / 2 : ℝ)) * ((a + x)⁻¹) ^ 2
        = x ^ (-(1 / 2 : ℝ)) * ((a + x)⁻¹ * (a + x)⁻¹) := by ring
      _ ≤ x ^ (-(1 / 2 : ℝ)) * (a⁻¹ * (a + x)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 h4.le) h3.le
      _ = a⁻¹ * (x ^ (-(1 / 2 : ℝ)) * (a + x)⁻¹) := by ring

end Scalar

section OpInt

theorem sqNorm_eq_re_dot' {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    Green.sqNorm v = (star v ⬝ᵥ v).re := by
  unfold Green.sqNorm
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : star (v i) * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  rw [this, Complex.ofReal_re]

variable {ι : Type*} [Fintype ι]

/-- The entrywise integral of a matrix-valued function. -/
noncomputable def intMat (μ : Measure ℝ) (F : ℝ → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun p q => ∫ x, F x p q ∂μ

theorem integrable_mulVec_apply {μ : Measure ℝ} {F : ℝ → Matrix ι ι ℂ}
    (hint : ∀ p q, Integrable (fun x => F x p q) μ) (f : ι → ℂ) (p : ι) :
    Integrable (fun x => (F x *ᵥ f) p) μ := by
  simp only [Matrix.mulVec, dotProduct]
  exact integrable_finsetSum _ fun q _ => (hint p q).mul_const _

theorem intMat_mulVec_apply {μ : Measure ℝ} {F : ℝ → Matrix ι ι ℂ}
    (hint : ∀ p q, Integrable (fun x => F x p q) μ) (f : ι → ℂ) (p : ι) :
    (intMat μ F *ᵥ f) p = ∫ x, (F x *ᵥ f) p ∂μ := by
  simp only [Matrix.mulVec, dotProduct, intMat]
  rw [integral_finsetSum _ fun q _ => (hint p q).mul_const _]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_mul_const]

theorem norm_star_dot_le_sqNorm (v w : ι → ℂ) :
    ‖star v ⬝ᵥ w‖ ≤ Real.sqrt (Green.sqNorm v) * Real.sqrt (Green.sqNorm w) := by
  calc ‖star v ⬝ᵥ w‖ ≤ ∑ p, ‖star (v p) * w p‖ := norm_sum_le _ _
    _ = ∑ p, ‖v p‖ * ‖w p‖ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ p, ‖v p‖ ^ 2) * Real.sqrt (∑ p, ‖w p‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := rfl

/-- **Operator bound for an integral of operators.** -/
theorem sqNorm_intMat_le (μ : Measure ℝ) (F : ℝ → Matrix ι ι ℂ)
    (hint : ∀ p q, Integrable (fun x => F x p q) μ) (g : ℝ → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hbd : ∀ᵐ x ∂μ, ∀ (f : ι → ℂ), Green.sqNorm (F x *ᵥ f) ≤ (g x) ^ 2 * Green.sqNorm f)
    (f : ι → ℂ) :
    Green.sqNorm (intMat μ F *ᵥ f) ≤ (∫ x, g x ∂μ) ^ 2 * Green.sqNorm f := by
  set v := intMat μ F *ᵥ f with hv
  set nv := Real.sqrt (Green.sqNorm v) with hnv
  set nf := Real.sqrt (Green.sqNorm f) with hnf
  have hG0 : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae hg0
  have hsv : 0 ≤ Green.sqNorm v := Green.sqNorm_nonneg v
  have hsf : 0 ≤ Green.sqNorm f := Green.sqNorm_nonneg f
  have hdot : star v ⬝ᵥ v = ∫ x, star v ⬝ᵥ (F x *ᵥ f) ∂μ := by
    simp only [dotProduct]
    have : ∀ p, v p = ∫ x, (F x *ᵥ f) p ∂μ := fun p => intMat_mulVec_apply hint f p
    rw [integral_finsetSum _ fun p _ => (integrable_mulVec_apply hint f p).const_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, ← this p]
  have hbound : ∀ᵐ x ∂μ, ‖star v ⬝ᵥ (F x *ᵥ f)‖ ≤ nv * nf * g x := by
    filter_upwards [hg0, hbd] with x hgx hbx
    refine (norm_star_dot_le_sqNorm v _).trans ?_
    have h1 : Real.sqrt (Green.sqNorm (F x *ᵥ f)) ≤ g x * nf := by
      calc Real.sqrt (Green.sqNorm (F x *ᵥ f)) ≤ Real.sqrt ((g x) ^ 2 * Green.sqNorm f) :=
            Real.sqrt_le_sqrt (hbx f)
        _ = g x * nf := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hgx]
    calc nv * Real.sqrt (Green.sqNorm (F x *ᵥ f)) ≤ nv * (g x * nf) :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = nv * nf * g x := by ring
  have hint2 : Integrable (fun x => nv * nf * g x) μ := hg.const_mul _
  have hle : ‖∫ x, star v ⬝ᵥ (F x *ᵥ f) ∂μ‖ ≤ nv * nf * ∫ x, g x ∂μ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hint2
      hbound
  have hsq : Green.sqNorm v ≤ nv * nf * ∫ x, g x ∂μ := by
    rw [sqNorm_eq_re_dot' v, hdot]
    exact (Complex.re_le_norm _).trans hle
  have hnv2 : nv ^ 2 = Green.sqNorm v := Real.sq_sqrt hsv
  have hnf2 : nf ^ 2 = Green.sqNorm f := Real.sq_sqrt hsf
  have hnv0 : 0 ≤ nv := Real.sqrt_nonneg _
  have hnf0 : 0 ≤ nf := Real.sqrt_nonneg _
  have : nv ≤ (∫ x, g x ∂μ) * nf := by
    by_cases h0 : nv = 0
    · rw [h0]; positivity
    · have hpos : 0 < nv := lt_of_le_of_ne hnv0 (Ne.symm h0)
      have : nv * nv ≤ nv * (nf * ∫ x, g x ∂μ) := by nlinarith
      have := le_of_mul_le_mul_left this hpos
      linarith
  calc Green.sqNorm v = nv ^ 2 := hnv2.symm
    _ ≤ ((∫ x, g x ∂μ) * nf) ^ 2 := pow_le_pow_left₀ hnv0 this 2
    _ = (∫ x, g x ∂μ) ^ 2 * Green.sqNorm f := by rw [mul_pow, hnf2]

end OpInt

end Balaban.Localization
