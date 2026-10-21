/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalGaussBochner
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fields of `N`-vectors as real fields on `ι × Fin N`

The block-spin fields of the class are maps `ι → EuclideanSpace ℝ (Fin N)`; the quadratic forms
of the last integral (`finalHessian`) are matrices on `ι × Fin N`, which do not act componentwise
in the spin index. `spinField` is the measurable equivalence from the first space to the real
fields `ι × Fin N → ℝ`, and `spinField_measurePreserving` shows it preserves the Lebesgue
measures, so that `Green/FinalGaussBochner.lean` applies with `W = ℝ` and the index type
`ι × Fin N`.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Green

variable (ι : Type*) [Fintype ι] (N : ℕ)

/-- The curry equivalence of real fields. -/
def fieldCurry : (ι → (Fin N → ℝ)) ≃ᵐ (ι × Fin N → ℝ) where
  toEquiv := (Equiv.curry ι (Fin N) ℝ).symm
  measurable_toFun := by
    refine Measurable.of_eval fun p => ?_
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  measurable_invFun := by
    refine Measurable.of_eval fun y => Measurable.of_eval fun i => ?_
    exact measurable_pi_apply (y, i)

theorem fieldCurry_measurePreserving :
    MeasurePreserving (fieldCurry ι N) (Measure.pi fun _ : ι => (volume : Measure (Fin N → ℝ)))
      (volume : Measure (ι × Fin N → ℝ)) := by
  refine ⟨(fieldCurry ι N).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [MeasurableEquiv.map_apply]
  have : (fieldCurry ι N) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun y : ι => Set.univ.pi fun i : Fin N => s (y, i) := by
    ext ψ; simp [fieldCurry, Set.mem_pi]
  rw [this, Measure.pi_pi]
  simp_rw [volume_pi, Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- A field of `N`-vectors as a real field on `ι × Fin N`. -/
noncomputable def spinField : (ι → EuclideanSpace ℝ (Fin N)) ≃ᵐ (ι × Fin N → ℝ) :=
  (MeasurableEquiv.piCongrRight fun _ : ι => (MeasurableEquiv.toLp 2 (Fin N → ℝ)).symm).trans
    (fieldCurry ι N)

omit [Fintype ι] in
theorem spinField_apply (ψ : ι → EuclideanSpace ℝ (Fin N)) (p : ι × Fin N) :
    spinField ι N ψ p = ψ p.1 p.2 := by
  simp [spinField, fieldCurry, Function.uncurry]
  rfl

theorem spinField_measurePreserving :
    MeasurePreserving (spinField ι N) (volume : Measure (ι → EuclideanSpace ℝ (Fin N)))
      (volume : Measure (ι × Fin N → ℝ)) := by
  refine MeasurePreserving.trans (μb := Measure.pi fun _ : ι => (volume : Measure (Fin N → ℝ)))
    ?_ (fieldCurry_measurePreserving ι N)
  exact volume_preserving_pi (fun _ : ι => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin N))

/-- **Integration over fields of `N`-vectors is integration over real fields on `ι × Fin N`.** -/
theorem integral_spinField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι × Fin N → ℝ) → E) :
    ∫ ψ : ι → EuclideanSpace ℝ (Fin N), f (spinField ι N ψ) = ∫ v, f v ∂(volume : Measure (ι × Fin N → ℝ)) :=
  (spinField_measurePreserving ι N).integral_comp' f

end Balaban.Green
