/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Evenness of the fluctuation measure

`ν₁` and `ν_p = ⨂ ν₁` are invariant under `ψ̂ ↦ -ψ̂`; consequently every coordinate mark
`ψ̂(y)` (and each of its real components) has mean zero.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Set

variable {N : ℕ}

theorem fluctDensity_neg (p : ℝ) (x : Rn N) : fluctDensity N p (-x) = fluctDensity N p x := by
  simp [fluctDensity]

/-- The single-site measure is invariant under `ψ̂ ↦ -ψ̂`. -/
theorem map_neg_fluctMeasure1 (p : ℝ) : (fluctMeasure1 N p).map Neg.neg = fluctMeasure1 N p := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  have hm : MeasurableSet (Neg.neg ⁻¹' s) := measurable_neg hs
  unfold fluctMeasure1
  rw [Measure.smul_apply, Measure.smul_apply, withDensity_apply _ hm, withDensity_apply _ hs]
  congr 1
  rw [← lintegral_indicator hm, ← lintegral_indicator hs]
  have := (Measure.measurePreserving_neg (volume : Measure (Rn N))).lintegral_comp_emb
    (Homeomorph.neg (Rn N)).measurableEmbedding
    (fun x => s.indicator (fun x => ENNReal.ofReal (fluctDensity N p x)) x)
  rw [← this]
  congr 1
  funext x
  simp only [Set.indicator, Set.mem_preimage, fluctDensity_neg]
  rfl

/-- The product measure is invariant under `ψ̂ ↦ -ψ̂`. -/
theorem map_neg_fluctMeasure (T : Type*) [Fintype T] (p : ℝ) :
    (fluctMeasure T N p).map Neg.neg = fluctMeasure T N p := by
  classical
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_neg (MeasurableSet.univ_pi hs)]
  have : (Neg.neg : (T → Rn N) → _) ⁻¹' (Set.univ.pi s) = Set.univ.pi fun t => Neg.neg ⁻¹' s t := by
    ext x; simp [Set.mem_pi]
  rw [this]
  unfold fluctMeasure
  have : ∀ _ : T, SigmaFinite (fluctMeasure1 N p) := fun _ => inferInstance
  rw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [← map_neg_fluctMeasure1 p, Measure.map_apply measurable_neg (hs t)]
  rw [map_neg_fluctMeasure1 p]

theorem integral_nuFl1_eq_zero (p : ℝ) :
    ∫ y, y ∂fluctMeasure1 N p = 0 := by
  rw [integral_fluctMeasure1]
  have h : ∫ y : Rn N, fluctDensity N p y • y = 0 := by
    have h1 := integral_neg_eq_self (fun y : Rn N => fluctDensity N p y • y) volume
    simp only [fluctDensity_neg, smul_neg] at h1
    rw [integral_neg] at h1
    have : (2 : ℝ) • ∫ y : Rn N, fluctDensity N p y • y = 0 := by
      rw [two_smul]; nth_rewrite 1 [← h1]; simp
    simpa using this
  rw [h]; simp

/-- Each coordinate mark `ψ̂(y)` has mean zero under `ν_p`. -/
theorem integral_coord_nuFl_eq_zero (T : Type*) [Fintype T] (p : ℝ) (hp : 0 < p) (y : T) :
    ∫ x, x y ∂fluctMeasure T N p = 0 := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  unfold fluctMeasure
  have := MeasureTheory.integral_comp_eval (μ := fun _ : T => fluctMeasure1 N p) (i := y)
    (f := fun v : Rn N => v) aestronglyMeasurable_id
  simpa using this.trans (integral_nuFl1_eq_zero p)

/-- Each real component of a coordinate mark has mean zero under `ν_p`. -/
theorem integral_coord_apply_nuFl_eq_zero (T : Type*) [Fintype T] (p : ℝ) (hp : 0 < p)
    (y : T) (i : Fin N) : ∫ x, x y i ∂fluctMeasure T N p = 0 := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  unfold fluctMeasure
  have h1 := MeasureTheory.integral_comp_eval (μ := fun _ : T => fluctMeasure1 N p) (i := y)
    (f := fun v : Rn N => v i) (by fun_prop)
  rw [h1, integral_fluctMeasure1]
  have h : ∫ v : Rn N, fluctDensity N p v • v i = 0 := by
    have h1 := integral_neg_eq_self (fun v : Rn N => fluctDensity N p v • v i) volume
    simp only [fluctDensity_neg, PiLp.neg_apply, smul_neg] at h1
    rw [integral_neg] at h1
    linarith
  rw [h]; simp

end Balaban.Fluctuation
