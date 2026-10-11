/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Model.AprioriMeasure
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

/-!
# The sphere measure and the a priori measure: finiteness and symmetries

For `N ≥ 1` the surface measure `volume.toSphere` on the unit sphere of `ℝ^N` is a finite measure
of positive mass and is invariant under every linear isometry; the a priori measure of the
hard-spin model (`Balaban.aprioriMeasure`) is a finite measure of positive mass, invariant under
sitewise rotations and under translations of the torus.
-/

@[expose] public section

namespace Balaban

open MeasureTheory
open scoped Pointwise

/-- The unit sphere of `ℝ^N`, the target of a single hard spin. -/
abbrev SpinSphere (N : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1

/-! ### The sphere measure -/

theorem toSphere_volume_ne_zero (N : ℕ) [NeZero N] :
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere ≠ 0 :=
  Measure.toSphere_ne_zero _

theorem toSphere_volume_univ_pos (N : ℕ) [NeZero N] :
    0 < (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ :=
  Measure.measure_univ_pos.2 (toSphere_volume_ne_zero N)

theorem toSphere_volume_univ_lt_top (N : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ < ⊤ :=
  measure_lt_top _ _

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- The action of a linear isometry on the unit sphere. -/
def sphereIsoMap (f : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) : Metric.sphere (0 : E) 1 :=
  ⟨f x.1, by simp [f.norm_map]⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_sphereIsoMap (f : E ≃ₗᵢ[ℝ] E) : Continuous (sphereIsoMap f) :=
  (f.continuous.comp continuous_subtype_val).subtype_mk _

theorem measurable_sphereIsoMap (f : E ≃ₗᵢ[ℝ] E) : Measurable (sphereIsoMap f) :=
  (continuous_sphereIsoMap f).measurable

omit [MeasurableSpace E] [BorelSpace E] in
theorem sphereIsoMap_trans_symm (f : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    sphereIsoMap f.symm (sphereIsoMap f x) = x :=
  Subtype.ext (by simp [sphereIsoMap])

omit [MeasurableSpace E] [BorelSpace E] in
theorem sphereIsoMap_symm_trans (f : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    sphereIsoMap f (sphereIsoMap f.symm x) = x :=
  Subtype.ext (by simp [sphereIsoMap])

/-- The action of a linear isometry on the unit sphere, as a measurable equivalence. -/
noncomputable def sphereIsoEquiv (f : E ≃ₗᵢ[ℝ] E) :
    Metric.sphere (0 : E) 1 ≃ᵐ Metric.sphere (0 : E) 1 where
  toFun := sphereIsoMap f
  invFun := sphereIsoMap f.symm
  left_inv := sphereIsoMap_trans_symm f
  right_inv := sphereIsoMap_symm_trans f
  measurable_toFun := measurable_sphereIsoMap f
  measurable_invFun := measurable_sphereIsoMap f.symm

omit [MeasurableSpace E] [BorelSpace E] in
theorem sphereIsoMap_cone_preimage (f : E ≃ₗᵢ[ℝ] E) (s : Set (Metric.sphere (0 : E) 1)) :
    Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereIsoMap f ⁻¹' s) : Set E) =
      (fun x : E => f x) ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
  ext x
  simp only [Set.mem_preimage]
  constructor
  · rintro ⟨u, hu, _, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨u, hu, f w.1, ⟨sphereIsoMap f w, hw, rfl⟩, by simp [map_smul]⟩
  · rintro ⟨u, hu, _, ⟨w, hw, rfl⟩, hfx⟩
    have hxeq : f.symm (u • w.1) = x := by
      apply f.injective
      simpa using hfx
    refine ⟨u, hu, f.symm w.1, ⟨⟨f.symm w.1, by simp⟩, ?_, rfl⟩, ?_⟩
    · simpa [sphereIsoMap] using hw
    · simpa [map_smul] using hxeq

variable [FiniteDimensional ℝ E]

/-- The surface measure on the unit sphere is invariant under linear isometries. -/
theorem map_sphereIsoMap_toSphere (f : E ≃ₗᵢ[ℝ] E) :
    (volume : Measure E).toSphere.map (sphereIsoMap f) = (volume : Measure E).toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_sphereIsoMap f) hs,
    Measure.toSphere_apply' _ (hs.preimage (measurable_sphereIsoMap f)),
    Measure.toSphere_apply' _ hs, sphereIsoMap_cone_preimage]
  congr 1
  have hm : MeasurePreserving (f.toHomeomorph.toMeasurableEquiv) (volume : Measure E) volume :=
    f.measurePreserving
  exact hm.measure_preimage_equiv _

end Rotation

/-! ### The a priori measure -/

section Apriori

variable (d N ℓ : ℕ) [NeZero ℓ]

instance : IsFiniteMeasure (aprioriMeasure d N ℓ) := by
  unfold aprioriMeasure
  infer_instance

theorem aprioriMeasure_ne_zero [NeZero N] : aprioriMeasure d N ℓ ≠ 0 := by
  intro h
  have h1 : aprioriMeasure d N ℓ Set.univ = 0 := by rw [h]; rfl
  unfold aprioriMeasure at h1
  rw [Measure.pi_univ] at h1
  exact (Finset.prod_ne_zero_iff.2 fun _ _ => (toSphere_volume_univ_pos N).ne') h1

theorem aprioriMeasure_univ_pos [NeZero N] : 0 < aprioriMeasure d N ℓ Set.univ :=
  Measure.measure_univ_pos.2 (aprioriMeasure_ne_zero d N ℓ)

/-- The sitewise rotation `φ ↦ (x ↦ R φ(x))` of spin configurations, as a measurable equivalence. -/
noncomputable def rotConfig (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    (Torus d ℓ → SpinSphere N) ≃ᵐ (Torus d ℓ → SpinSphere N) :=
  MeasurableEquiv.arrowCongr' (Equiv.refl _) (sphereIsoEquiv R)

/-- The translation `φ ↦ φ(· + a)` of spin configurations, as a measurable equivalence. -/
noncomputable def shiftConfig (a : Torus d ℓ) :
    (Torus d ℓ → SpinSphere N) ≃ᵐ (Torus d ℓ → SpinSphere N) :=
  MeasurableEquiv.arrowCongr' (Equiv.addRight a).symm (MeasurableEquiv.refl _)

omit [NeZero ℓ] in
theorem rotConfig_apply (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
    (φ : Torus d ℓ → SpinSphere N) (x : Torus d ℓ) :
    ((rotConfig d N ℓ R φ x : SpinSphere N) : EuclideanSpace ℝ (Fin N)) = R (φ x : _) := rfl

omit [NeZero ℓ] in
theorem shiftConfig_apply (a : Torus d ℓ) (φ : Torus d ℓ → SpinSphere N) (x : Torus d ℓ) :
    shiftConfig d N ℓ a φ x = φ (x + a) := by
  simp [shiftConfig, MeasurableEquiv.arrowCongr', Equiv.arrowCongr']

/-- The a priori measure is invariant under sitewise rotations. -/
theorem measurePreserving_rotConfig
    (R : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    MeasurePreserving (rotConfig d N ℓ R) (aprioriMeasure d N ℓ) (aprioriMeasure d N ℓ) := by
  refine measurePreserving_arrowCongr' (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) (Equiv.refl _)
    (sphereIsoEquiv R) fun _ => ⟨(sphereIsoEquiv R).measurable, ?_⟩
  exact map_sphereIsoMap_toSphere R

/-- The a priori measure is invariant under translations of the torus. -/
theorem measurePreserving_shiftConfig (a : Torus d ℓ) :
    MeasurePreserving (shiftConfig d N ℓ a) (aprioriMeasure d N ℓ) (aprioriMeasure d N ℓ) :=
  measurePreserving_arrowCongr' (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
    (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) _ (MeasurableEquiv.refl _)
    fun _ => MeasurePreserving.id _

end Apriori

end Balaban
