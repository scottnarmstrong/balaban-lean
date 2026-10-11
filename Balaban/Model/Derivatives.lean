/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Model.PartitionFunction

/-!
# Derivatives of the logarithm of the partition function (Lemma 0.1, Proposition 1.4)

With `F(g) = log (Z(g) / Z(0))` (`logPartition`), analytic on `∑ |g| < 1`
(`analyticOnNhd_logPartition`):

* `fderiv ℂ F 0 (δ_x e_i) = ⟨φ_i(x)⟩` (`fderiv_logPartition_zero`);
* `fderiv ℂ (fun g => fderiv ℂ F g (δ_x e_i)) 0 (δ_y e_k) = G_{ik}(x, y)`
  (`fderiv_fderiv_logPartition_zero`).
-/

@[expose] public section

namespace Balaban

open MeasureTheory

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- The source `δ_x e_i`: equal to `1` at the site `x` and component `i`, and `0` elsewhere. -/
def sourceDelta (x : Torus d ℓ) (i : Fin N) : Torus d ℓ → Fin N → ℂ :=
  Pi.single x (Pi.single i 1)

/-- The logarithm of the normalized partition function, the generating function of the connected
correlations. -/
noncomputable def logPartition (d N ℓ : ℕ) [NeZero ℓ] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  Complex.log (partitionFunction d N ℓ β ν h g / partitionFunction d N ℓ β ν h 0)

theorem sourcePairingCLM_delta (φ : Torus d ℓ → SpinSphere N) (x : Torus d ℓ) (i : Fin N) :
    sourcePairingCLM φ (sourceDelta x i) = (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
  rw [sourcePairingCLM_apply]
  unfold sourcePairing
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [sourceDelta, hy]) (by simp),
    Finset.sum_eq_single i (fun j _ hj => by simp [sourceDelta, hj]) (by simp)]
  simp [sourceDelta]

/-- The directional derivative of `sourceIntegral`. -/
theorem fderiv_sourceIntegral_apply (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {c : (Torus d ℓ → SpinSphere N) → ℂ} (hc : Continuous c) (g u : Torus d ℓ → Fin N → ℂ) :
    fderiv ℂ (sourceIntegral d N ℓ β ν h c) g u =
      sourceIntegral d N ℓ β ν h (fun φ => c φ * sourcePairingCLM φ u) g := by
  rw [(hasFDerivAt_sourceIntegral β ν h hc g).fderiv]
  have hI := continuous_sourceIntegrand_prod (d := d) (N := N) (ℓ := ℓ) β ν h hc
  have hint : Integrable (sourceIntegrandDeriv d N ℓ β ν h c g) (aprioriMeasure d N ℓ) :=
    integrable_of_continuous
      ((hI.comp (Continuous.prodMk_right g)).smul continuous_sourcePairingCLM)
  rw [ContinuousLinearMap.integral_apply hint]
  unfold sourceIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  simp only [sourceIntegrandDeriv, sourceIntegrand, smul_apply, smul_eq_mul]
  ring

theorem continuous_mul_sourcePairingCLM {c : (Torus d ℓ → SpinSphere N) → ℂ} (hc : Continuous c)
    (u : Torus d ℓ → Fin N → ℂ) :
    Continuous fun φ => c φ * sourcePairingCLM φ u :=
  hc.mul (continuous_sourcePairingCLM.clm_apply continuous_const)

/-- Values at `g = 0`: `∫ F e^{-βH}` for a real observable. -/
theorem sourceIntegral_zero_ofReal (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (F : (Torus d ℓ → SpinSphere N) → ℝ) :
    sourceIntegral d N ℓ β ν h (fun φ => (F φ : ℂ)) 0 =
      ((∫ φ, F φ * Real.exp (-(β * energy d N ℓ ν h φ)) ∂aprioriMeasure d N ℓ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold sourceIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun φ => ?_)
  show (F φ : ℂ) * Complex.exp (-((β * energy d N ℓ ν h φ : ℝ) : ℂ) + sourcePairing 0 φ) = _
  rw [sourcePairing_zero, add_zero]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]

theorem sourceIntegral_zero_div (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (F : (Torus d ℓ → SpinSphere N) → ℝ) :
    sourceIntegral d N ℓ β ν h (fun φ => (F φ : ℂ)) 0 / partitionFunction d N ℓ β ν h 0 =
      (gibbsExpectation d N ℓ β ν h F : ℂ) := by
  rw [sourceIntegral_zero_ofReal, partitionFunction_zero, ← Complex.ofReal_div]
  rfl

theorem partitionFunction_zero_ne_zero [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    partitionFunction d N ℓ β ν h 0 ≠ 0 := by
  obtain ⟨r, hr, h0⟩ := partitionFunction_zero_pos (d := d) (N := N) (ℓ := ℓ) β ν h
  rw [h0]
  exact_mod_cast hr.ne'

theorem hasFDerivAt_logPartition [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) :
    HasFDerivAt (logPartition d N ℓ β ν h)
      ((partitionFunction d N ℓ β ν h g)⁻¹ • fderiv ℂ (partitionFunction d N ℓ β ν h) g) g := by
  have hZ := (differentiable_partitionFunction (d := d) (N := N) (ℓ := ℓ) β ν h g).hasFDerivAt
  have h0 := partitionFunction_zero_ne_zero (d := d) (N := N) (ℓ := ℓ) β ν h
  have hne := partitionFunction_ne_zero β ν h hg
  have hdiv : HasFDerivAt (fun t => partitionFunction d N ℓ β ν h t /
      partitionFunction d N ℓ β ν h 0) ((partitionFunction d N ℓ β ν h 0)⁻¹ •
        fderiv ℂ (partitionFunction d N ℓ β ν h) g) g := by
    simpa only [div_eq_inv_mul] using hZ.const_mul (partitionFunction d N ℓ β ν h 0)⁻¹
  have := hdiv.clog (partitionFunction_div_mem_slitPlane β ν h hg)
  refine this.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  field_simp

/-- Lemma 0.1: `log (Z(g)/Z(0))` is complex differentiable on `∑ |g| < 1`. -/
theorem differentiableOn_logPartition [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) :
    DifferentiableOn ℂ (logPartition d N ℓ β ν h) (sourceBall d N ℓ) :=
  fun _ hg => (hasFDerivAt_logPartition β ν h hg).differentiableAt.differentiableWithinAt

theorem fderiv_partitionFunction_apply (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g u : Torus d ℓ → Fin N → ℂ) :
    fderiv ℂ (partitionFunction d N ℓ β ν h) g u =
      sourceIntegral d N ℓ β ν h (fun φ => sourcePairingCLM φ u) g := by
  rw [partitionFunction_eq_sourceIntegral,
    fderiv_sourceIntegral_apply β ν h continuous_const]
  simp only [one_mul]

theorem fderiv_logPartition_apply [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    {g : Torus d ℓ → Fin N → ℂ} (hg : g ∈ sourceBall d N ℓ) (u : Torus d ℓ → Fin N → ℂ) :
    fderiv ℂ (logPartition d N ℓ β ν h) g u =
      (partitionFunction d N ℓ β ν h g)⁻¹ *
        sourceIntegral d N ℓ β ν h (fun φ => sourcePairingCLM φ u) g := by
  rw [(hasFDerivAt_logPartition β ν h hg).fderiv, smul_apply,
    fderiv_partitionFunction_apply, smul_eq_mul]

/-- Proposition 1.4 (first derivative): `∂_{g_i(x)} log (Z(g)/Z(0)) |_{g=0} = ⟨φ_i(x)⟩`. -/
theorem fderiv_logPartition_zero [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (x : Torus d ℓ) (i : Fin N) :
    fderiv ℂ (logPartition d N ℓ β ν h) 0 (sourceDelta x i) =
      (onePoint d N ℓ β ν h x i : ℂ) := by
  rw [fderiv_logPartition_apply β ν h zero_mem_sourceBall]
  simp only [sourcePairingCLM_delta]
  rw [← div_eq_inv_mul]
  exact sourceIntegral_zero_div β ν h (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i)

/-- Proposition 1.4 (second derivative): the mixed second derivative of `log (Z(g)/Z(0))` at
`g = 0` in the directions `δ_x e_i` and `δ_y e_k` is the truncated two-point function. -/
theorem fderiv_fderiv_logPartition_zero [NeZero N] (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (x y : Torus d ℓ) (i k : Fin N) :
    fderiv ℂ (fun g => fderiv ℂ (logPartition d N ℓ β ν h) g (sourceDelta x i)) 0
        (sourceDelta y k) = (twoPointTruncated d N ℓ β ν h x y i k : ℂ) := by
  set Z := partitionFunction d N ℓ β ν h with hZdef
  have h0 : Z 0 ≠ 0 := partitionFunction_zero_ne_zero β ν h
  set cu : (Torus d ℓ → SpinSphere N) → ℂ := fun φ => sourcePairingCLM φ (sourceDelta x i)
    with hcu
  have hcu_cont : Continuous cu := continuous_sourcePairingCLM.clm_apply continuous_const
  set A := sourceIntegral d N ℓ β ν h cu with hA
  have heq : (fun g => fderiv ℂ (logPartition d N ℓ β ν h) g (sourceDelta x i)) =ᶠ[nhds 0]
      fun g => (Z g)⁻¹ * A g :=
    Filter.eventually_of_mem (isOpen_sourceBall.mem_nhds zero_mem_sourceBall)
      fun g hg => fderiv_logPartition_apply β ν h hg _
  rw [heq.fderiv_eq]
  have hZ : HasFDerivAt Z (fderiv ℂ Z 0) 0 :=
    (differentiable_partitionFunction (d := d) (N := N) (ℓ := ℓ) β ν h 0).hasFDerivAt
  have hAd : HasFDerivAt A (fderiv ℂ A 0) 0 :=
    (differentiable_sourceIntegral β ν h hcu_cont 0).hasFDerivAt
  have hinv : HasFDerivAt (fun g => (Z g)⁻¹) (-(Z 0 ^ 2)⁻¹ • fderiv ℂ Z 0) 0 :=
    (hasDerivAt_inv h0).comp_hasFDerivAt 0 hZ
  have hQ : HasFDerivAt (fun g => (Z g)⁻¹ * A g)
      ((Z 0)⁻¹ • fderiv ℂ A 0 + A 0 • (-(Z 0 ^ 2)⁻¹ • fderiv ℂ Z 0)) 0 := hinv.mul hAd
  rw [hQ.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hA, fderiv_sourceIntegral_apply β ν h hcu_cont, hZdef, fderiv_partitionFunction_apply, ← hZdef]
  -- identify the values at `g = 0`
  have hP := sourceIntegral_zero_div β ν h (d := d) (N := N) (ℓ := ℓ)
    (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i * (φ y : EuclideanSpace ℝ (Fin N)) k)
  have hMx := sourceIntegral_zero_div β ν h (d := d) (N := N) (ℓ := ℓ)
    (fun φ => (φ x : EuclideanSpace ℝ (Fin N)) i)
  have hMy := sourceIntegral_zero_div β ν h (d := d) (N := N) (ℓ := ℓ)
    (fun φ => (φ y : EuclideanSpace ℝ (Fin N)) k)
  simp only [hcu, sourcePairingCLM_delta] at *
  simp only [Complex.ofReal_mul] at hP
  rw [div_eq_iff h0] at hP hMx hMy
  unfold twoPointTruncated onePoint
  push_cast
  rw [hP, hMx, hMy]
  field_simp
  ring

end Balaban
