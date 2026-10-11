/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.Symmetry
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Real.Pi.Bounds

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

/-! ### Positivity at `g = 0` and the logarithm -/

theorem sourcePairing_zero (φ : Torus d ℓ → SpinSphere N) :
    sourcePairing (0 : Torus d ℓ → Fin N → ℂ) φ = 0 := by
  simp [sourcePairing]

/-- `Z(0) = ∫ e^{-βH}` (as a complex number). -/
theorem partitionFunction_zero (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    partitionFunction d N ℓ β ν h 0 =
      ((∫ φ, Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold partitionFunction
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  show Complex.exp (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing 0 φ) = _
  rw [sourcePairing_zero, add_zero]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg]

theorem partitionFunctionReal_pos [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    0 < ∫ φ, Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ := by
  have : NeZero (aprioriMeasure d N ℓ) := ⟨aprioriMeasure_ne_zero d N ℓ⟩
  have hE := continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h
  exact integral_exp_pos (integrable_of_continuous (by fun_prop))

/-- `Z(0) > 0`, and it is real. -/
theorem partitionFunction_zero_pos [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    ∃ r : ℝ, 0 < r ∧ partitionFunction d N ℓ β ν h 0 = (r : ℂ) :=
  ⟨_, partitionFunctionReal_pos β ν h, partitionFunction_zero β ν h⟩

/-- The domain `∑_x ∑_i |g_i(x)| < 1` on which the logarithm of `Z(g)/Z(0)` is analytic. -/
def sourceBall (d N ℓ : ℕ) [NeZero ℓ] : Set (Torus d ℓ → Fin N → ℂ) :=
  {g | ∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖ < 1}

theorem isOpen_sourceBall : IsOpen (sourceBall d N ℓ) :=
  isOpen_lt (by fun_prop) continuous_const

theorem zero_mem_sourceBall : (0 : Torus d ℓ → Fin N → ℂ) ∈ sourceBall d N ℓ := by
  simp [sourceBall]

theorem abs_im_sourcePairing_le (g : Torus d ℓ → Fin N → ℂ) (φ : Torus d ℓ → SpinSphere N) :
    |(sourcePairing g φ).im| ≤ ∑ x : Torus d ℓ, ∑ i : Fin N, ‖g x i‖ := by
  refine (Complex.abs_im_le_norm _).trans ?_
  unfold sourcePairing
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real]
  have : ‖(φ x : EuclideanSpace ℝ (Fin N)) i‖ ≤ 1 := by
    calc ‖(φ x : EuclideanSpace ℝ (Fin N)) i‖ ≤ ‖(φ x : EuclideanSpace ℝ (Fin N))‖ :=
          PiLp.norm_apply_le _ i
      _ = 1 := by simp
  nlinarith [norm_nonneg (g x i)]

/-- On `∑ |g| < 1` the real part of `Z(g)` is positive (`|Im ⟨g, φ⟩| < 1 < π/2`). -/
theorem re_partitionFunction_pos [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) :
    0 < (partitionFunction d N ℓ β ν h g).re := by
  have : NeZero (aprioriMeasure d N ℓ) := ⟨aprioriMeasure_ne_zero d N ℓ⟩
  have h1 := continuous_energy (d := d) (N := N) (ℓ := ℓ) ν h
  have h2 : Continuous fun φ : Torus d ℓ → SpinSphere N => sourcePairing g φ :=
    continuous_sourcePairing_prod.comp (Continuous.prodMk_right g)
  have hint : Integrable (fun φ => Complex.exp
      (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ)) (aprioriMeasure d N ℓ) :=
    integrable_of_continuous (by fun_prop)
  have key : (partitionFunction d N ℓ β ν h g).re = ∫ φ, (Complex.exp
      (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ)).re ∂aprioriMeasure d N ℓ := by
    have := (integral_re hint).symm
    simp only [RCLike.re_to_complex] at this
    exact this
  rw [key]
  simp only [Complex.exp_re]
  have hpos : ∀ φ : Torus d ℓ → SpinSphere N, 0 < Real.exp ((-((β * energy d N ℓ ν h φ : ℝ) : ℂ)
      + sourcePairing g φ).re) * Real.cos (-((β * energy d N ℓ ν h φ : ℝ) : ℂ)
      + sourcePairing g φ).im := by
    intro φ
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · have := abs_im_sourcePairing_le g φ
      have h1 := abs_lt.1 (lt_of_le_of_lt this hg)
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add]
      linarith [Real.pi_gt_three, h1.1]
    · have := abs_im_sourcePairing_le g φ
      have h1 := abs_lt.1 (lt_of_le_of_lt this hg)
      simp only [Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add]
      linarith [Real.pi_gt_three, h1.2]
  have hcont : Continuous fun φ : Torus d ℓ → SpinSphere N =>
      Real.exp ((-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ).re) *
        Real.cos (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ).im := by
    fun_prop
  rw [integral_pos_iff_support_of_nonneg (fun φ => (hpos φ).le) (integrable_of_continuous hcont)]
  have : Function.support (fun φ : Torus d ℓ → SpinSphere N =>
      Real.exp ((-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ).re) *
        Real.cos (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing g φ).im) = Set.univ :=
    Set.eq_univ_of_forall fun φ => (hpos φ).ne'
  rw [this]
  exact aprioriMeasure_univ_pos d N ℓ

theorem partitionFunction_ne_zero [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) :
    partitionFunction d N ℓ β ν h g ≠ 0 := by
  intro h0
  have := re_partitionFunction_pos β ν h hg
  rw [h0] at this
  simp at this

/-- `Re (Z(g)/Z(0)) > 0` on `∑ |g| < 1`. -/
theorem re_partitionFunction_div_pos [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) :
    0 < (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0).re := by
  obtain ⟨r, hr, h0⟩ := partitionFunction_zero_pos (d := d) (N := N) (ℓ := ℓ) β ν h
  rw [h0, Complex.div_ofReal_re]
  exact div_pos (re_partitionFunction_pos β ν h hg) hr

/-- `Z(g)/Z(0)` lies in the slit plane on `∑ |g| < 1`. -/
theorem partitionFunction_div_mem_slitPlane [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) :
    partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0 ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.2 (Or.inl (re_partitionFunction_div_pos β ν h hg))

end Balaban
