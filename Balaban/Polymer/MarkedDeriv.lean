/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Balaban.Polymer.CauchySum

/-!
# Derivative of `∫ exp (A + z G)` in the mark `z`

For bounded measurable `A, G` and a probability measure `ν`,
`d/dz ∫ exp (A + z G) dν |_{z = 0} = ∫ G exp A dν`.
-/

@[expose] public section

namespace Balaban.Polymer

open MeasureTheory Metric

theorem hasDerivAt_expMark {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (A G : X → ℂ) (hA : Measurable A) (hG : Measurable G) {CA CG : ℝ} (hCG : 0 ≤ CG)
    (hAb : ∀ x, ‖A x‖ ≤ CA) (hGb : ∀ x, ‖G x‖ ≤ CG) :
    HasDerivAt (fun z : ℂ => ∫ x, Complex.exp (A x + z * G x) ∂ν)
      (∫ x, G x * Complex.exp (A x) ∂ν) 0 := by
  have hmeas : ∀ z : ℂ, Measurable (fun x => Complex.exp (A x + z * G x)) := fun z =>
    Complex.measurable_exp.comp (hA.add (measurable_const.mul hG))
  have hint : Integrable (fun x => Complex.exp (A x + (0 : ℂ) * G x)) ν := by
    refine Integrable.of_bound (hmeas 0).aestronglyMeasurable (Real.exp CA) (Filter.Eventually.of_forall fun x => ?_)
    simp only [zero_mul, add_zero]
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 (hAb x))
  have hF'm : Measurable (fun x => G x * Complex.exp (A x + (0 : ℂ) * G x)) :=
    hG.mul (hmeas 0)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℂ))
    (F := fun (z : ℂ) x => Complex.exp (A x + z * G x))
    (F' := fun (z : ℂ) x => G x * Complex.exp (A x + z * G x)) (s := ball (0 : ℂ) 1)
    (bound := fun _ => CG * Real.exp (CA + CG)) (ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun z => (hmeas z).aestronglyMeasurable) hint
    hF'm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x z hz => by
      rw [norm_mul]
      refine mul_le_mul (hGb x) ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_))
        (norm_nonneg _) hCG
      calc ‖A x + z * G x‖ ≤ ‖A x‖ + ‖z * G x‖ := norm_add_le _ _
        _ ≤ CA + CG := by
          rw [norm_mul]
          refine add_le_add (hAb x) ?_
          have : ‖z‖ ≤ 1 := by simpa using (mem_ball_zero_iff.1 hz).le
          calc ‖z‖ * ‖G x‖ ≤ 1 * CG := mul_le_mul this (hGb x) (norm_nonneg _) zero_le_one
            _ = CG := one_mul _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x z _ => by
      have h1 : HasDerivAt (fun z : ℂ => A x + z * G x) (G x) z := by
        simpa using ((hasDerivAt_id z).mul_const (G x)).const_add (A x)
      have := HasDerivAt.cexp h1
      simpa [mul_comm] using this)
  simpa using key.2

theorem D1_expMark {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (A G : X → ℂ) (hA : Measurable A) (hG : Measurable G) {CA CG : ℝ}
    (hCG : 0 ≤ CG) (hAb : ∀ x, ‖A x‖ ≤ CA) (hGb : ∀ x, ‖G x‖ ≤ CG) :
    D1 () (fun l : Unit → ℂ => ∫ x, Complex.exp (A x + l () * G x) ∂ν) =
      ∫ x, G x * Complex.exp (A x) ∂ν := by
  have h1 := hasDerivAt_expMark ν A G hA hG hCG hAb hGb
  have h2 : HasFDerivAt (fun z : ℂ => ∫ x, Complex.exp (A x + z * G x) ∂ν)
      (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (∫ x, G x * Complex.exp (A x) ∂ν)) 0 :=
    h1.hasFDerivAt
  have h3 := h2.comp (0 : Unit → ℂ) (ContinuousLinearMap.proj () : (Unit → ℂ) →L[ℂ] ℂ).hasFDerivAt
  unfold D1
  have h4 : fderiv ℂ (fun l : Unit → ℂ => ∫ x, Complex.exp (A x + l () * G x) ∂ν) 0 =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (∫ x, G x * Complex.exp (A x) ∂ν) ∘L
        (ContinuousLinearMap.proj () : (Unit → ℂ) →L[ℂ] ℂ) := h3.fderiv
  rw [h4]
  simp

end Balaban.Polymer
