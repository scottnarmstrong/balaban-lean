/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastIntegral
public import Balaban.LargeField.Base.KF0CutoffSplit
public import Balaban.Polymer.FibreProduct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian measure of the box as a product measure

A6-3, gas layer. The standard Gaussian `γ` on the real fields `w : ι × Fin N → ℝ` is the product over
`ι` of the standard Gaussians `γ₁` of `Fin N → ℝ` (`measurePreserving_fieldCurry_pdGaussian`, through
the curry equivalence `fieldCurry`), and the box `|w_p| ≤ p₁` is the product of the one-site boxes
(`fieldCurry_preimage_gaussBox`). Hence the integral over the box against `γ` is
`γ₁(box₁)^{|ι|}` times the integral against the product of the conditioned measures
`γ₁(· | box₁)` (`setIntegral_gaussBox_eq`), and `γ₁(box₁) > 0` for `p₁ > 0`
(`pdGaussian_gaussBox_pos`). Grouping the sites by a map `q : ι → B` (`Polymer.qSites`) turns the
product over the sites into a product over the groups (`integral_pi_eq_qRef`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Balaban.Green

namespace Balaban.RootFSpine

section WithDensity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The image of a measure with density under a measurable equivalence. -/
theorem withDensity_map_equiv (μ : Measure α) (e : α ≃ᵐ β) (f : α → ENNReal) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs, lintegral_map_equiv]
  simp

end WithDensity

section Gauss

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- The one-site factor of the Gaussian density. -/
theorem pdGaussian_fin_eq (N : ℕ) :
    pdGaussian (Fin N) ℝ = (Measure.pi fun _ : Fin N => (volume : Measure ℝ)).withDensity
      fun v => ENNReal.ofReal ((2 * Real.pi) ^ (-(N : ℝ) / 2) *
        Real.exp (-(1 / 2) * ∑ i, ‖v i‖ ^ 2)) := by
  unfold pdGaussian pdDim pdVol
  simp

/-- **The Gaussian of the real fields on `ι × Fin N` is the product of the Gaussians of
`Fin N → ℝ`.** -/
theorem measurePreserving_fieldCurry_pdGaussian :
    MeasurePreserving (fieldCurry ι N) (Measure.pi fun _ : ι => pdGaussian (Fin N) ℝ)
      (pdGaussian (ι × Fin N) ℝ) := by
  refine ⟨(fieldCurry ι N).measurable, ?_⟩
  have hg : ∀ _ : ι, Measurable fun v : Fin N → ℝ =>
      (2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / 2) * ∑ i, ‖v i‖ ^ 2) := fun _ => by
    fun_prop
  rw [pdGaussian_fin_eq N]
  rw [Balaban.LargeField.pi_withDensity_eq (fun _ : ι => Measure.pi fun _ : Fin N => volume)
    (fun _ v => (2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / 2) * ∑ i, ‖v i‖ ^ 2)) hg]
  rw [withDensity_map_equiv]
  have hvol : (Measure.pi fun _ : ι => Measure.pi fun _ : Fin N => (volume : Measure ℝ)).map
      (fieldCurry ι N) = pdVol (ι × Fin N) ℝ := by
    have := (fieldCurry_measurePreserving ι N).map_eq
    rw [show (Measure.pi fun _ : ι => Measure.pi fun _ : Fin N => (volume : Measure ℝ)) =
      Measure.pi fun _ : ι => (volume : Measure (Fin N → ℝ)) from rfl, this]
    rfl
  rw [hvol]
  unfold pdGaussian
  congr 1
  funext w
  simp only [Function.comp_apply]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ]
  congr 1
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    simp only [pdDim, Fintype.card_prod, Fintype.card_fin, Module.finrank_self]
    push_cast; ring
  · congr 1
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rfl

omit [Fintype ι] in
/-- The box `|w_p| ≤ p₁` of the fields on `ι × Fin N` is the product of the one-site boxes. -/
theorem fieldCurry_preimage_gaussBox (p1 : ℝ) :
    fieldCurry ι N ⁻¹' gaussBox (ι × Fin N) p1 =
      Set.pi Set.univ fun _ : ι => gaussBox (Fin N) p1 := by
  ext Φ
  simp only [Set.mem_preimage, gaussBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
    true_implies, Prod.forall]
  rfl

theorem measurableSet_gaussBox (κ : Type*) [Fintype κ] (p1 : ℝ) :
    MeasurableSet (gaussBox κ p1) := by
  have : gaussBox κ p1 = ⋂ p, {w : κ → ℝ | |w p| ≤ p1} := by
    ext w; simp [gaussBox]
  rw [this]
  exact MeasurableSet.iInter fun p => measurableSet_le ((measurable_pi_apply p).abs) measurable_const

/-- **The one-site box has positive Gaussian measure** for `p₁ > 0`. -/
theorem pdGaussian_gaussBox_pos {p1 : ℝ} (hp1 : 0 < p1) :
    0 < pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1) := by
  rw [pdGaussian_fin_eq N, withDensity_apply _ (measurableSet_gaussBox _ p1)]
  set c : ℝ := (2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / 2) * (N * p1 ^ 2)) with hc
  have hc0 : 0 < c := by positivity
  have hle : ∀ v ∈ gaussBox (Fin N) p1, ENNReal.ofReal c ≤ ENNReal.ofReal
      ((2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / 2) * ∑ i, ‖v i‖ ^ 2)) := by
    intro v hv
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
      (by positivity))
    have : ∑ i, ‖v i‖ ^ 2 ≤ N * p1 ^ 2 := by
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, p1 ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs]
            have h1 := hv i
            have h2 := abs_nonneg (v i)
            nlinarith
        _ = N * p1 ^ 2 := by simp
    linarith
  have hbox : gaussBox (Fin N) p1 = Set.pi Set.univ fun _ : Fin N => Set.Icc (-p1) p1 := by
    ext v
    simp only [gaussBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
      abs_le]
  have hvol : 0 < (Measure.pi fun _ : Fin N => (volume : Measure ℝ)) (gaussBox (Fin N) p1) := by
    rw [hbox, Measure.pi_pi]
    refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  calc (0 : ENNReal) < ENNReal.ofReal c * (Measure.pi fun _ : Fin N => (volume : Measure ℝ))
        (gaussBox (Fin N) p1) :=
        pos_iff_ne_zero.2 (mul_ne_zero (ENNReal.ofReal_pos.2 hc0).ne' hvol.ne')
    _ = ∫⁻ _v in gaussBox (Fin N) p1, ENNReal.ofReal c ∂(Measure.pi fun _ : Fin N => volume) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := setLIntegral_mono' (measurableSet_gaussBox _ p1) hle

/-- **The integral over the box as an integral against the product of the conditioned one-site
Gaussians**: `∫_{box} F dγ = γ₁(box₁)^{|ι|} ∫ F(Φ) d⨂_ι γ₁(· | box₁)`. -/
theorem setIntegral_gaussBox_eq {p1 : ℝ} (hp1 : 0 < p1) (F : (ι × Fin N → ℝ) → ℂ) :
    ∫ w in gaussBox (ι × Fin N) p1, F w ∂(pdGaussian (ι × Fin N) ℝ) =
      (((pdGaussian (Fin N) ℝ (gaussBox (Fin N) p1)).toReal ^ Fintype.card ι : ℝ) : ℂ) *
        ∫ Φ, F (fieldCurry ι N Φ) ∂(Measure.pi fun _ : ι =>
          cond (pdGaussian (Fin N) ℝ) (gaussBox (Fin N) p1)) := by
  have hprob : IsProbabilityMeasure (pdGaussian (Fin N) ℝ) := ⟨pdGaussian_univ⟩
  have hmp := measurePreserving_fieldCurry_pdGaussian (ι := ι) (N := N)
  rw [← hmp.setIntegral_preimage_emb (fieldCurry ι N).measurableEmbedding F,
    fieldCurry_preimage_gaussBox]
  have hpos := (pdGaussian_gaussBox_pos (N := N) hp1).ne'
  rw [Balaban.LargeField.restrict_pi_set_eq (pdGaussian (Fin N) ℝ) (measurableSet_gaussBox _ p1)
    hpos, integral_smul_measure, ENNReal.toReal_pow]
  rw [Complex.real_smul]

end Gauss

section Group

variable {ι B W : Type*} [Fintype ι] [Fintype B] [DecidableEq B] [MeasurableSpace W]
  (q : ι → B)

/-- **The product over the sites as a product over the groups**: for every function `G` of the
site configurations, `∫ G d⨂_ι μ = ∫ G ∘ qSites d⨂_b (⨂_{x ∈ q⁻¹(b)} μ)`. -/
theorem integral_pi_eq_qRef (μ : Measure W) [SigmaFinite μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : (ι → W) → E) :
    ∫ ψ, G ψ ∂(Measure.pi fun _ : ι => μ) =
      ∫ Φ, G (Polymer.qSites q Φ) ∂(Measure.pi (Polymer.qRef q μ)) := by
  have hmp : MeasurePreserving (Polymer.qSitesEquiv q (W := W)) (Measure.pi (Polymer.qRef q μ))
      (Measure.pi fun _ : ι => μ) :=
    ⟨(Polymer.qSitesEquiv q).measurable, Polymer.map_qSites_pi μ⟩
  exact (hmp.integral_comp' G).symm

end Group

end Balaban.RootFSpine
