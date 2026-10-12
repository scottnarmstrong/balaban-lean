/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Balaban.LargeField.Operators.PiTools

/-!
# Product measures: lintegrals of products, densities, and linear changes of variables

`Measure.pi` of measures with densities and of constant multiples, and the linear change of
variables for a Haar measure.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Set
open scoped ENNReal

universe u

variable {ι : Type u} [Fintype ι]

theorem pi_withDensity_eq {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    (μ : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (g : (i : ι) → E i → ℝ) (hg : ∀ i, Measurable (g i)) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (g i x))) =
      (Measure.pi μ).withDensity (fun a => ∏ i, ENNReal.ofReal (g i (a i))) := by
  refine Measure.pi_eq fun s hs => ?_
  have hbox : MeasurableSet (Set.pi univ s) := MeasurableSet.univ_pi hs
  have hF : Measurable (fun a : (i : ι) → E i => ∏ i, ENNReal.ofReal (g i (a i))) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp ((hg i).comp (measurable_pi_apply i))
  rw [withDensity_apply _ hbox, ← lintegral_indicator hbox]
  have : ∀ a : (i : ι) → E i, (Set.pi univ s).indicator
      (fun a => ∏ i, ENNReal.ofReal (g i (a i))) a =
      ∏ i, (s i).indicator (fun x => ENNReal.ofReal (g i x)) (a i) := by
    intro a
    by_cases ha : a ∈ Set.pi univ s
    · rw [Set.indicator_of_mem ha]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (ha i (mem_univ i))]
    · rw [Set.indicator_of_notMem ha]
      have : ∃ i, a i ∉ s i := by
        by_contra h
        exact ha fun i _ => by by_contra h'; exact h ⟨i, h'⟩
      obtain ⟨i, hi⟩ := this
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Set.indicator_of_notMem hi]
  simp_rw [this]
  rw [PiTools.lintegral_fintype_prod_eq_prod ι (fun i x => (s i).indicator (fun x => ENNReal.ofReal (g i x)) x)
    (fun i => (ENNReal.measurable_ofReal.comp (hg i)).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

theorem pi_const_smul {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    (ν : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (ν i)] (c : NNReal) :
    Measure.pi (fun i => c • ν i) = (c ^ Fintype.card ι) • Measure.pi ν := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  push_cast
  rfl


section Linear

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [MeasurableSpace X] [BorelSpace X]

/-- Linear change of variables for the lintegral. -/
theorem lintegral_eq_ofReal_abs_det_mul (μ : Measure X) [μ.IsAddHaarMeasure] (R : X ≃ₗ[ℝ] X)
    (f : X → ℝ≥0∞) :
    ∫⁻ y, f y ∂μ = ENNReal.ofReal |LinearMap.det (R : X →ₗ[ℝ] X)| * ∫⁻ x, f (R x) ∂μ := by
  have hdet : LinearMap.det (R : X →ₗ[ℝ] X) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact Units.ne_zero _
  have hemb : MeasurableEmbedding R := (R.toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  have h1 : ∫⁻ y, f y ∂(Measure.map (R : X →ₗ[ℝ] X) μ) = ∫⁻ x, f (R x) ∂μ :=
    hemb.lintegral_map f
  rw [hmap, lintegral_smul_measure] at h1
  rw [← h1, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
    mul_inv_cancel₀ hdet]
  simp

end Linear

end Balaban.LargeField
