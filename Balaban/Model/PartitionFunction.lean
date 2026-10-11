/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.Symmetry
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The partition function with a source is entire (Lemma 0.1)

`sourceIntegral c g = ∫ c(φ) exp(-β H(φ) + ⟨g, φ⟩) dμ(φ)` is an entire function of the complex
source `g : Torus d ℓ → Fin N → ℂ` for every continuous weight `c`; its Fréchet derivative is
obtained by differentiating under the integral sign (`hasFDerivAt_sourceIntegral`).  The
partition function is `sourceIntegral 1` (`partitionFunction_eq_sourceIntegral`).
-/

@[expose] public section

namespace Balaban

open MeasureTheory

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- The source term `⟨g, φ⟩ = ∑_x ∑_i g_i(x) φ_i(x)`. -/
noncomputable def sourcePairing (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) : ℂ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N, g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)

/-- The source term as a continuous linear functional of `g`. -/
noncomputable def sourcePairingCLM (φ : Torus d ℓ → SpinSphere N) :
    (Torus d ℓ → Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ x : Torus d ℓ, ∑ i : Fin N,
    (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) •
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Torus d ℓ => Fin N → ℂ) x))

theorem sourcePairingCLM_apply (φ : Torus d ℓ → SpinSphere N) (g : Torus d ℓ → Fin N → ℂ) :
    sourcePairingCLM φ g = sourcePairing g φ := by
  simp [sourcePairingCLM, sourcePairing, mul_comm]

theorem continuous_sourcePairing_prod :
    Continuous fun p : (Torus d ℓ → Fin N → ℂ) × (Torus d ℓ → SpinSphere N) =>
      sourcePairing p.1 p.2 := by
  unfold sourcePairing
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ => ?_
  have hg : Continuous fun p : (Torus d ℓ → Fin N → ℂ) × (Torus d ℓ → SpinSphere N) =>
      p.1 x i := by fun_prop
  have hs : Continuous fun p : (Torus d ℓ → Fin N → ℂ) × (Torus d ℓ → SpinSphere N) =>
      (((p.2 x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_spin_coord x i).comp continuous_snd)
  exact hg.mul hs

theorem continuous_sourcePairingCLM :
    Continuous fun φ : Torus d ℓ → SpinSphere N => sourcePairingCLM (d := d) (N := N) (ℓ := ℓ) φ := by
  unfold sourcePairingCLM
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun i _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_spin_coord x i)).smul continuous_const

/-- The integrand `c(φ) exp(-β H(φ) + ⟨g, φ⟩)`. -/
noncomputable def sourceIntegrand (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (c : (Torus d ℓ → SpinSphere N) → ℂ)
    (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) : ℂ :=
  c φ * Complex.exp (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ)

/-- `∫ c(φ) exp(-β H(φ) + ⟨g, φ⟩) dμ(φ)`. -/
noncomputable def sourceIntegral (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (c : (Torus d ℓ → SpinSphere N) → ℂ) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  ∫ φ, sourceIntegrand d N ℓ β ν h c g φ ∂aprioriMeasure d N ℓ

/-- The derivative in `g` of the integrand. -/
noncomputable def sourceIntegrandDeriv (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (c : (Torus d ℓ → SpinSphere N) → ℂ)
    (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) :
    (Torus d ℓ → Fin N → ℂ) →L[ℂ] ℂ :=
  sourceIntegrand d N ℓ β ν h c g φ • sourcePairingCLM φ

theorem partitionFunction_eq_sourceIntegral (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    partitionFunction d N ℓ β ν h = sourceIntegral d N ℓ β ν h (fun _ => 1) := by
  funext g
  simp [partitionFunction, sourceIntegral, sourceIntegrand, sourcePairing]

theorem continuous_sourceIntegrand_prod (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {c : (Torus d ℓ → SpinSphere N) → ℂ} (hc : Continuous c) :
    Continuous fun p : (Torus d ℓ → Fin N → ℂ) × (Torus d ℓ → SpinSphere N) =>
      sourceIntegrand d N ℓ β ν h c p.1 p.2 := by
  have h1 := continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h
  have h2 := continuous_sourcePairing_prod (d := d) (N := N) (ℓ := ℓ)
  unfold sourceIntegrand
  fun_prop

/-- Differentiation under the integral sign for `sourceIntegral`. -/
theorem hasFDerivAt_sourceIntegral (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {c : (Torus d ℓ → SpinSphere N) → ℂ} (hc : Continuous c) (g₀ : Torus d ℓ → Fin N → ℂ) :
    HasFDerivAt (sourceIntegral d N ℓ β ν h c)
      (∫ φ, sourceIntegrandDeriv d N ℓ β ν h c g₀ φ ∂aprioriMeasure d N ℓ) g₀ := by
  have hI := continuous_sourceIntegrand_prod (d := d) (N := N) (ℓ := ℓ) β ν h hc
  have hF'cont : Continuous fun p : (Torus d ℓ → Fin N → ℂ) × (Torus d ℓ → SpinSphere N) =>
      sourceIntegrandDeriv d N ℓ β ν h c p.1 p.2 :=
    hI.smul (continuous_sourcePairingCLM.comp continuous_snd)
  obtain ⟨B, hB⟩ := (isCompact_closedBall g₀ 1 |>.prod isCompact_univ).exists_bound_of_continuousOn
    (f := fun p : (Torus d ℓ → Fin N → ℂ) × (Torus d ℓ → SpinSphere N) =>
      sourceIntegrandDeriv d N ℓ β ν h c p.1 p.2) hF'cont.continuousOn
  have h1 : ∀ᶠ g in nhds g₀, AEStronglyMeasurable (sourceIntegrand d N ℓ β ν h c g)
      (aprioriMeasure d N ℓ) :=
    Filter.Eventually.of_forall fun g =>
      (hI.comp (Continuous.prodMk_right g)).aestronglyMeasurable
  have h2 : Integrable (sourceIntegrand d N ℓ β ν h c g₀) (aprioriMeasure d N ℓ) :=
    integrable_of_continuous (hI.comp (Continuous.prodMk_right g₀))
  have h3 : AEStronglyMeasurable (sourceIntegrandDeriv d N ℓ β ν h c g₀) (aprioriMeasure d N ℓ) :=
    (hF'cont.comp (Continuous.prodMk_right g₀)).aestronglyMeasurable
  have h4 : ∀ᵐ φ ∂aprioriMeasure d N ℓ, ∀ g ∈ Metric.ball g₀ 1,
      ‖sourceIntegrandDeriv d N ℓ β ν h c g φ‖ ≤ B :=
    Filter.Eventually.of_forall fun φ g hg =>
      hB (g, φ) ⟨Metric.ball_subset_closedBall hg, Set.mem_univ _⟩
  have h5 : Integrable (fun _ : Torus d ℓ → SpinSphere N => B) (aprioriMeasure d N ℓ) :=
    integrable_const B
  have h6 : ∀ᵐ φ ∂aprioriMeasure d N ℓ, ∀ g ∈ Metric.ball g₀ 1,
      HasFDerivAt (fun g' => sourceIntegrand d N ℓ β ν h c g' φ)
        (sourceIntegrandDeriv d N ℓ β ν h c g φ) g := by
    refine Filter.Eventually.of_forall fun φ g _ => ?_
    have hl : HasFDerivAt (fun g' : Torus d ℓ → Fin N → ℂ => sourcePairingCLM φ g')
        (sourcePairingCLM φ) g := (sourcePairingCLM φ).hasFDerivAt
    have := (((hl.const_add (-((β * energy d N ℓ ν h φ : ℝ) : ℂ))).cexp).const_mul (c φ))
    simp only [sourcePairingCLM_apply] at this
    simpa [sourceIntegrand, sourceIntegrandDeriv, smul_smul, smul_eq_mul] using this
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (E := ℂ)
    (Metric.ball_mem_nhds g₀ one_pos) h1 h2 h3 h4 h5 h6

theorem differentiable_sourceIntegral (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {c : (Torus d ℓ → SpinSphere N) → ℂ} (hc : Continuous c) :
    Differentiable ℂ (sourceIntegral d N ℓ β ν h c) :=
  fun g => (hasFDerivAt_sourceIntegral β ν h hc g).differentiableAt

/-- Lemma 0.1: the partition function is entire in the source. -/
theorem differentiable_partitionFunction (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    Differentiable ℂ (partitionFunction d N ℓ β ν h) := by
  rw [partitionFunction_eq_sourceIntegral]
  exact differentiable_sourceIntegral β ν h continuous_const

end Balaban
