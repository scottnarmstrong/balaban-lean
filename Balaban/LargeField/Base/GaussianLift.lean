/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.SphereChart
public import Balaban.LargeField.Base.PiLintegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Gaussian lift of the tangent integral (LF-RECONSTRUCTION Lemma II.7.4 (b))

For a unit vector `e ∈ ℝ^N` and `s ⊆ e^⊥` measurable, the part of `ℝ^N` projecting into `s` carries
the Gaussian weight `e^{-⟨e,u⟩²/2}` of total mass `√(2π) vol(s)` (`lintegral_perpK_preimage`), i.e.
`∫_{e^⊥} f(ξ) dξ = (2π)^{-1/2} ∫_{ℝ^N} f(P^⊥ u) e^{-⟨e,u⟩²/2} du`: the real identity (b) with
`s = 1`, for every Borel `f ≥ 0`.  `lintegral_tangent_eq` is the product form over a finite set of
sites with directions `e_x`, which is the form used by the base step.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

namespace Balaban.LargeField.SphereChart

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (e : E)

theorem lintegral_gaussian_real :
    ∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (-(a ^ 2) / 2)) = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  have hint : Integrable (fun a : ℝ => Real.exp (-(1 / 2 : ℝ) * a ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal ?_ (ae_of_all _ fun a => (Real.exp_pos _).le)]
  · congr 1
    have e1 : (fun a : ℝ => Real.exp (-(a ^ 2) / 2)) = fun a => Real.exp (-(1 / 2 : ℝ) * a ^ 2) := by
      funext a; congr 1; ring
    rw [e1, h]
    congr 1; field_simp
  · have e1 : (fun a : ℝ => Real.exp (-(a ^ 2) / 2)) = fun a => Real.exp (-(1 / 2 : ℝ) * a ^ 2) := by
      funext a; congr 1; ring
    rw [e1]; exact hint

theorem measurableEmbedding_splitMap (he : ‖e‖ = 1) : MeasurableEmbedding (splitMap e he) := by
  have hc : Continuous (splitMap e he) := by
    have : splitMap e he = fun p : perp e × ℝ => (p.1 : E) + p.2 • e := funext (splitMap_apply e he)
    rw [this]; fun_prop
  have hi : Function.Injective (splitMap e he) := by
    intro p q h
    have h1 := congrArg (perpK e he) h
    have h2 := congrArg (inner ℝ e) h
    rw [perpK_splitMap, perpK_splitMap] at h1
    rw [inner_splitMap, inner_splitMap] at h2
    exact Prod.ext h1 h2
  exact hc.measurableEmbedding hi

/-- **Lemma II.7.4 (b), one site** (the Gaussian lift of the tangent integral): for measurable
`s ⊆ e^⊥`, the Gaussian weight `e^{-⟨e,u⟩²/2}` on the part of `ℝ^N` projecting into `s` has
mass `√(2π) vol(s)`. -/
theorem lintegral_perpK_preimage (he : ‖e‖ = 1) {s : Set (perp e)} (hs : MeasurableSet s) :
    ∫⁻ u in (perpK e he) ⁻¹' s, ENNReal.ofReal (Real.exp (-(inner ℝ e u ^ 2) / 2))
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi)) * volume s := by
  have hp : Measurable (perpK e he) := (continuous_perpK e he).measurable
  have hm : MeasurableSet ((perpK e he) ⁻¹' s) := hs.preimage hp
  rw [← lintegral_indicator hm]
  rw [← (measurePreserving_splitMap e he).lintegral_comp_emb (measurableEmbedding_splitMap e he)]
  have : ∀ p : perp e × ℝ, ((perpK e he) ⁻¹' s).indicator
      (fun u => ENNReal.ofReal (Real.exp (-(inner ℝ e u ^ 2) / 2))) (splitMap e he p) =
      s.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ENNReal.ofReal (Real.exp (-(p.2 ^ 2) / 2)) := by
    intro p
    by_cases hp1 : p.1 ∈ s
    · rw [Set.indicator_of_mem (by simpa [perpK_splitMap] using hp1 : splitMap e he p ∈ (perpK e he) ⁻¹' s),
        Set.indicator_of_mem hp1, inner_splitMap]; simp
    · rw [Set.indicator_of_notMem (by simpa [perpK_splitMap] using hp1 : splitMap e he p ∉ (perpK e he) ⁻¹' s),
        Set.indicator_of_notMem hp1]; simp
  simp_rw [this]
  have hf : AEMeasurable (s.indicator fun _ => (1 : ℝ≥0∞)) (volume : Measure (perp e)) :=
    (measurable_const.indicator hs).aemeasurable
  have hg : AEMeasurable (fun a : ℝ => ENNReal.ofReal (Real.exp (-(a ^ 2) / 2))) volume :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod_mul hf hg, lintegral_gaussian_real, lintegral_indicator hs]
  simp [mul_comm]


/-- The Gaussian integral `∫ e^{-s a²/2} da = √(2π/s)`. -/
theorem lintegral_gaussian_real_param {s : ℝ} (hs : 0 < s) :
    ∫⁻ a : ℝ, ENNReal.ofReal (Real.exp (-(s / 2) * a ^ 2)) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi / s)) := by
  have hint : Integrable (fun a : ℝ => Real.exp (-(s / 2) * a ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun a => (Real.exp_pos _).le)]
  congr 1
  rw [integral_gaussian]
  congr 1
  field_simp

/-- Parametric version of `lintegral_perpK_preimage` (Gaussian weight `e^{-s⟨e,u⟩²/2}`). -/
theorem lintegral_perpK_preimage_param (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) {t : Set (perp e)}
    (ht : MeasurableSet t) :
    ∫⁻ u in (perpK e he) ⁻¹' t, ENNReal.ofReal (Real.exp (-(s / 2) * inner ℝ e u ^ 2))
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi / s)) * volume t := by
  have hp : Measurable (perpK e he) := (continuous_perpK e he).measurable
  have hm : MeasurableSet ((perpK e he) ⁻¹' t) := ht.preimage hp
  rw [← lintegral_indicator hm]
  rw [← (measurePreserving_splitMap e he).lintegral_comp_emb (measurableEmbedding_splitMap e he)]
  have : ∀ p : perp e × ℝ, ((perpK e he) ⁻¹' t).indicator
      (fun u => ENNReal.ofReal (Real.exp (-(s / 2) * inner ℝ e u ^ 2))) (splitMap e he p) =
      t.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ENNReal.ofReal (Real.exp (-(s / 2) * p.2 ^ 2)) := by
    intro p
    by_cases hp1 : p.1 ∈ t
    · rw [Set.indicator_of_mem (by simpa [perpK_splitMap] using hp1 : splitMap e he p ∈ (perpK e he) ⁻¹' t),
        Set.indicator_of_mem hp1, inner_splitMap]; simp
    · rw [Set.indicator_of_notMem (by simpa [perpK_splitMap] using hp1 : splitMap e he p ∉ (perpK e he) ⁻¹' t),
        Set.indicator_of_notMem hp1]; simp
  simp_rw [this]
  have hf : AEMeasurable (t.indicator fun _ => (1 : ℝ≥0∞)) (volume : Measure (perp e)) :=
    (measurable_const.indicator ht).aemeasurable
  have hg : AEMeasurable (fun a : ℝ => ENNReal.ofReal (Real.exp (-(s / 2) * a ^ 2))) volume :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod_mul hf hg, lintegral_gaussian_real_param hs, lintegral_indicator ht]
  simp [mul_comm]

/-- **Lemma II.7.4 (b)** (the Gaussian lift of the tangent integral), for a unit vector `e` and
`s > 0`: for every Borel `g ≥ 0` on `e^⊥`,
`∫_{e^⊥} g(ξ) dξ = (s/2π)^{1/2} ∫ g(P^⊥_e u) e^{-s ⟨e,u⟩²/2} du`. -/
theorem lintegral_perp_eq (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s) (g : perp e → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ ξ, g ξ = ENNReal.ofReal (Real.sqrt (s / (2 * Real.pi))) *
      ∫⁻ u : E, g (perpK e he u) * ENNReal.ofReal (Real.exp (-(s / 2) * inner ℝ e u ^ 2)) := by
  have hp : Measurable (perpK e he) := (continuous_perpK e he).measurable
  set d : E → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-(s / 2) * inner ℝ e u ^ 2)) with hd
  have hdm : Measurable d := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    have : Continuous fun u : E => inner ℝ e u := continuous_const.inner continuous_id
    fun_prop
  have hmap : (volume.withDensity d).map (perpK e he) =
      (Real.sqrt (2 * Real.pi / s)).toNNReal • (volume : Measure (perp e)) := by
    ext t ht
    rw [Measure.map_apply hp ht, withDensity_apply _ (ht.preimage hp), Measure.coe_nnreal_smul_apply,
      lintegral_perpK_preimage_param e he hs ht]
    rfl
  have h1 : ∫⁻ u, d u * g (perpK e he u) = ∫⁻ ξ, g ξ ∂((volume.withDensity d).map (perpK e he)) := by
    rw [lintegral_map hg hp, lintegral_withDensity_eq_lintegral_mul₀ (f := d)
      (g := fun u => g (perpK e he u)) hdm.aemeasurable (hg.comp hp).aemeasurable]
    rfl
  rw [hmap, lintegral_smul_measure] at h1
  have hc : ENNReal.ofReal (Real.sqrt (s / (2 * Real.pi))) *
      ((Real.sqrt (2 * Real.pi / s)).toNNReal : ℝ≥0∞) = 1 := by
    have : ((Real.sqrt (2 * Real.pi / s)).toNNReal : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt (2 * Real.pi / s)) := rfl
    rw [this, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul (by positivity)]
    have : s / (2 * Real.pi) * (2 * Real.pi / s) = 1 := by field_simp
    rw [this]; simp
  have h2 : ∫⁻ u, g (perpK e he u) * d u = ∫⁻ u, d u * g (perpK e he u) :=
    lintegral_congr fun u => mul_comm _ _
  rw [h2, h1, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, hc, one_mul]


end

end Balaban.LargeField.SphereChart

namespace Balaban.LargeField

open SphereChart

universe u

noncomputable section

variable {ι : Type u} [Fintype ι] {N : ℕ}

/-- The projection `V = (ι → ℝ^N) → Π x, e_x^⊥`, `u ↦ (Q_x u_x)_x`. -/
def tangentProj (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (u : ι → EuclideanSpace ℝ (Fin N)) : (x : ι) → perp (e x) :=
  fun x => perpK (e x) (he x) (u x)

omit [Fintype ι] in
theorem measurable_tangentProj (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) :
    Measurable (tangentProj e he) :=
  measurable_pi_iff.2 fun x => ((continuous_perpK (e x) (he x)).measurable).comp (measurable_pi_apply x)

/-- The Gaussian weight in the normal directions. -/
def normalWeight (e : ι → EuclideanSpace ℝ (Fin N)) (u : ι → EuclideanSpace ℝ (Fin N)) : ℝ :=
  Real.exp (-(1 / 2) * ∑ x, inner ℝ (e x) (u x) ^ 2)

theorem measurable_normalWeight (e : ι → EuclideanSpace ℝ (Fin N)) :
    Measurable (normalWeight e) := by
  unfold normalWeight; fun_prop

theorem map_tangentProj_site (e : EuclideanSpace ℝ (Fin N)) (he : ‖e‖ = 1) :
    (volume.withDensity fun u : EuclideanSpace ℝ (Fin N) =>
      ENNReal.ofReal (Real.exp (-(inner ℝ e u ^ 2) / 2))).map (perpK e he) =
    (Real.sqrt (2 * Real.pi)).toNNReal • (volume : Measure (perp e)) := by
  ext s hs
  have hp : Measurable (perpK e he) := (continuous_perpK e he).measurable
  rw [Measure.map_apply hp hs, withDensity_apply _ (hs.preimage hp), Measure.coe_nnreal_smul_apply,
    lintegral_perpK_preimage e he hs]
  rfl

/-- **Lemma II.7.4 (b), product form**: the Gaussian lift of a tangent integral. -/
theorem lintegral_tangent_eq (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    (g : ((x : ι) → perp (e x)) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) *
        ∫⁻ u : ι → EuclideanSpace ℝ (Fin N),
          g (tangentProj e he u) * ENNReal.ofReal (normalWeight e u) := by
  classical
  set ν : ι → Measure (EuclideanSpace ℝ (Fin N)) := fun x =>
    volume.withDensity fun u : EuclideanSpace ℝ (Fin N) =>
      ENNReal.ofReal (Real.exp (-(inner ℝ (e x) u ^ 2) / 2)) with hν
  have hgx : ∀ x, Measurable fun u : EuclideanSpace ℝ (Fin N) =>
      Real.exp (-(inner ℝ (e x) u ^ 2) / 2) := fun x => by fun_prop
  -- the density of the product
  have hdens : (fun u : ι → EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (normalWeight e u)) =
      fun u => ∏ x, ENNReal.ofReal (Real.exp (-(inner ℝ (e x) (u x) ^ 2) / 2)) := by
    funext u
    unfold normalWeight
    rw [← ENNReal.ofReal_prod_of_nonneg (fun x _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hpi : (volume : Measure (ι → EuclideanSpace ℝ (Fin N))).withDensity
      (fun u => ENNReal.ofReal (normalWeight e u)) = Measure.pi ν := by
    rw [hdens]
    exact (pi_withDensity_eq (fun _ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
      (fun x u => Real.exp (-(inner ℝ (e x) u ^ 2) / 2)) hgx).symm
  have hmap : ∀ x, (ν x).map (perpK (e x) (he x)) =
      (Real.sqrt (2 * Real.pi)).toNNReal • (volume : Measure (perp (e x))) :=
    fun x => map_tangentProj_site (e x) (he x)
  have : ∀ x, SigmaFinite ((ν x).map (perpK (e x) (he x))) := fun x => by
    rw [hmap x]; infer_instance
  have hmapπ : (Measure.pi ν).map (tangentProj e he) =
      ((Real.sqrt (2 * Real.pi)).toNNReal ^ Fintype.card ι) •
        Measure.pi fun x => (volume : Measure (perp (e x))) := by
    have := Measure.pi_map_pi (μ := ν) (f := fun x => perpK (e x) (he x))
      (fun x => ((continuous_perpK (e x) (he x)).measurable).aemeasurable)
    simp_rw [hmap] at this
    rw [show tangentProj e he = fun u x => perpK (e x) (he x) (u x) from rfl, this]
    exact pi_const_smul _ _
  have hl : ∫⁻ u : ι → EuclideanSpace ℝ (Fin N),
      g (tangentProj e he u) * ENNReal.ofReal (normalWeight e u) =
      ((Real.sqrt (2 * Real.pi)).toNNReal ^ Fintype.card ι : NNReal) *
        ∫⁻ ξ, g ξ ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
    have h1 : ∫⁻ u : ι → EuclideanSpace ℝ (Fin N), g (tangentProj e he u) *
        ENNReal.ofReal (normalWeight e u) =
        ∫⁻ u, g (tangentProj e he u) ∂((volume : Measure (ι → EuclideanSpace ℝ (Fin N))).withDensity
          (fun u => ENNReal.ofReal (normalWeight e u))) := by
      rw [lintegral_withDensity_eq_lintegral_mul₀
        (f := fun u => ENNReal.ofReal (normalWeight e u))
        (g := fun u => g (tangentProj e he u))
        (ENNReal.measurable_ofReal.comp (measurable_normalWeight e)).aemeasurable
        (hg.comp (measurable_tangentProj e he)).aemeasurable]
      refine lintegral_congr fun u => ?_
      simp [mul_comm]
    rw [h1, hpi, ← lintegral_map hg (measurable_tangentProj e he), hmapπ, lintegral_smul_measure]
    rfl
  rw [hl, ← mul_assoc]
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2)) *
      (((Real.sqrt (2 * Real.pi)).toNNReal ^ Fintype.card ι : NNReal) : ℝ≥0∞) = 1 := by
    have h1 : (((Real.sqrt (2 * Real.pi)).toNNReal ^ Fintype.card ι : NNReal) : ℝ≥0∞) =
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi)) ^ Fintype.card ι) := by
      rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]; rfl
    rw [h1, ← ENNReal.ofReal_mul (by positivity)]
    have h2 : (2 * Real.pi) ^ (-(Fintype.card ι : ℝ) / 2) * (Real.sqrt (2 * Real.pi)) ^ Fintype.card ι = 1 := by
      have hp : 0 < 2 * Real.pi := by positivity
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
      rw [show -(Fintype.card ι : ℝ) / 2 + 1 / 2 * (Fintype.card ι : ℝ) = 0 by ring]
      simp
    rw [h2]; simp
  rw [hc, one_mul]

end

end Balaban.LargeField
