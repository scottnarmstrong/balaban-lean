/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseSectorSupport
public import Balaban.LargeField.Base.BaseChartAction
import Mathlib.Tactic.Positivity

/-!
# The physical first-step integrand in a variable hemisphere chart

The chart centre depends on the coarse field. The first identities below rescale each tangent
coordinate and separate the physical mass and complex source without changing the frozen model.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background MeasureTheory SphereChart

noncomputable section

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- Lebesgue scaling on a finite product of tangent hyperplanes. -/
theorem integral_pi_perp_inv_sqrt_smul
    (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    {β : ℝ} (hβ : 0 < β) (F : ((x : ι) → perp (e x)) → ℂ) :
    (∫ ξ : (x : ι) → perp (e x), F ξ
        ∂(Measure.pi fun x => (volume : Measure (perp (e x))))) =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card ι * (N - 1))) •
        ∫ v : (x : ι) → perp (e x), F ((Real.sqrt β)⁻¹ • v)
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  let μ : Measure ((x : ι) → perp (e x)) :=
    Measure.pi fun x => (volume : Measure (perp (e x)))
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have h := Measure.integral_comp_inv_smul_of_nonneg μ F hs.le
  rw [finrank_pi_perp e he] at h
  change (∫ ξ, F ξ ∂μ) =
    ((Real.sqrt β)⁻¹ ^ (Fintype.card ι * (N - 1))) •
      (∫ v, F ((Real.sqrt β)⁻¹ • v) ∂μ)
  rw [h]
  rw [smul_smul]
  have hc : (Real.sqrt β)⁻¹ ^ (Fintype.card ι * (N - 1)) *
      Real.sqrt β ^ (Fintype.card ι * (N - 1)) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hs.ne']
    simp
  rw [hc, one_smul]

/-- The complex source pairing after the rescaled chart substitution, for a variable centre. -/
theorem source_chartPoint_complex {β : ℝ} (e w : ι → EuclideanSpace ℝ (Fin N))
    (g : ι → Fin N → ℂ) :
    (∑ x : ι, ∑ i : Fin N,
      g x i * (((chartPoint β e w x) i : ℝ) : ℂ)) =
      (∑ x : ι, ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) +
        (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
          (∑ x : ι, ∑ i : Fin N,
            g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)) := by
  have hx (x : ι) (i : Fin N) :
      g x i * (((chartPoint β e w x) i : ℝ) : ℂ) =
        g x i * (((e x) i : ℝ) : ℂ) +
          (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
            (g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)) := by
    simp [chartPoint]
    ring
  simp_rw [hx, Finset.sum_add_distrib, ← Finset.mul_sum]

variable {d L n : ℕ} [NeZero L] [NeZero n]

/-- Split the physical mass into the background mass and its regime-A remainder. -/
theorem energy_mass_split (ν μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) :
    energy d N (L * n) ν h φ = energy d N (L * n) μ h φ +
      (ν - μ) / 2 * ∑ x : Torus d (L * n),
        ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 := by
  unfold energy
  ring_nf

/-- The first block kernel is a constant times the exponential of its quadratic action. -/
theorem baseKernel_exp (β a : ℝ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) :
    baseKernel d N L n β a θ φ =
      (∏ _y : Torus d n,
        ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2)) *
        Real.exp (-(β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2) := by
  unfold baseKernel gaussT
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum]

/-- Move the Gaussian block action into the complex exponent. -/
theorem baseKernel_mul_exp (β a : ℝ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) (s : ℂ) :
    ((baseKernel d N L n β a θ φ : ℝ) : ℂ) * Complex.exp s =
      ((∏ _y : Torus d n,
        ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 : ℝ) : ℂ) + s) := by
  rw [baseKernel_exp, Complex.ofReal_mul, Complex.ofReal_exp, Complex.exp_add]
  push_cast
  ring_nf

/-- The product of chart weights becomes the rescaled Jacobian at a variable centre. -/
theorem chartWeight_prod_inv_sqrt_eq_chartJac
    (e : ι → EuclideanSpace ℝ (Fin N)) {β : ℝ} (hβ : 0 < β)
    (v : (x : ι) → perp (e x)) :
    (∏ x : ι, chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x)) =
      chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) := by
  unfold chartJac
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]

omit [Fintype ι] in
/-- Inside the tangent balls, the chart map is the explicit normal-coordinate field. -/
theorem chartMapPi_inv_sqrt_eq_chartPoint
    (e : ι → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    {β : ℝ} (hβ : 0 < β) (v : (x : ι) → perp (e x))
    (hv : ∀ x, ‖v x‖ < Real.sqrt β) :
    (fun x => (chartMapPi e he ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N))) =
      chartPoint β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) := by
  funext x
  have hlt : ‖((Real.sqrt β)⁻¹ • v) x‖ < 1 := by
    rw [Pi.smul_apply]
    exact (norm_inv_sqrt_smul_lt_one_iff hβ (v x)).2 (hv x)
  unfold chartMapPi
  rw [coe_hemiPt_of_lt (e x) (he x) hlt, Pi.smul_apply,
    chartPoint_eq β hβ (e x) (v x)]
  rfl

/-- The physical exponent in the variable chart, with the regime-A mass kept separate. -/
theorem basePhysicalExponent_chart
    (e : Torus d (L * n) → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1)
    {β : ℝ} (hβ : 0 < β) (ν μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ)
    (v : (x : Torus d (L * n)) → perp (e x)) (hv : ∀ x, ‖v x‖ < Real.sqrt β) :
    -((β * energy d N (L * n) ν h (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) : ℝ) : ℂ) +
        (∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((chartMapPi e he ((Real.sqrt β)⁻¹ • v) x :
            EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) =
      -((β * energy d N (L * n) μ h (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) : ℝ) : ℂ) -
        ((β * (ν - μ) / 2 * ∑ x : Torus d (L * n),
          ‖(chartMapPi e he ((Real.sqrt β)⁻¹ • v) x :
            EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
        (∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((e x) i : ℝ) : ℂ)) +
        (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((((v x : EuclideanSpace ℝ (Fin N)) +
              chartShift β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) x) i : ℝ) : ℂ))) := by
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := fun x => (v x : EuclideanSpace ℝ (Fin N))
  have hpt := chartMapPi_inv_sqrt_eq_chartPoint e he hβ v hv
  have hsrc := source_chartPoint_complex (β := β) e w g
  have hsrc' :
      (∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) =
      (∑ x : Torus d (L * n), ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) +
        (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
          (∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)) := by
    simpa only [φ, w, ← hpt] using hsrc
  change -((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
      (∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) = _
  rw [energy_mass_split ν μ h φ, hsrc']
  push_cast
  ring

/-- The exact physical chart integral in rescaled tangent variables. The kernel, source,
Jacobian and regime-A mass are retained with their literal first-step coefficients. -/
theorem baseChartIntegral_eq_rescaled_physicalAction
    {β : ℝ} (hβ : 0 < β) (a ν μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (χ : CfgT d N L n → ℝ)
    (e : Torus d (L * n) → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) :
    baseChartIntegral d N L n β a ν h g θ χ e he =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
        ∫ v : (x : Torus d (L * n)) → perp (e x),
          let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
          let w : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := fun x => (v x : EuclideanSpace ℝ (Fin N))
          ((chartJac β w : ℝ) : ℂ) *
            ((χ φ : ℂ) * ((baseKernel d N L n β a θ φ : ℝ) : ℂ) *
              Complex.exp (
                -((β * energy d N (L * n) μ h φ : ℝ) : ℂ) -
                ((β * (ν - μ) / 2 * ∑ x : Torus d (L * n),
                  ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
                (∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((e x) i : ℝ) : ℂ)) +
                (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
                  (∑ x : Torus d (L * n), ∑ i : Fin N,
                    g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ))))
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  let F : ((x : Torus d (L * n)) → perp (e x)) → ℂ := fun ξ =>
    (∏ x, ((chartWeight (e x) (ξ x) : ℝ) : ℂ)) *
      ((χ (chartMapPi e he ξ) : ℂ) *
        ((baseKernel d N L n β a θ (chartMapPi e he ξ) : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h (chartMapPi e he ξ) : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((chartMapPi e he ξ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
  change (∫ ξ, F ξ ∂(Measure.pi fun x => (volume : Measure (perp (e x))))) = _
  rw [integral_pi_perp_inv_sqrt_smul e he hβ F]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
  let w : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := fun x => (v x : EuclideanSpace ℝ (Fin N))
  have hJ : (∏ x : Torus d (L * n),
      ((chartWeight (e x) (((Real.sqrt β)⁻¹ • v) x) : ℝ) : ℂ)) =
        ((chartJac β w : ℝ) : ℂ) := by
    rw [← Complex.ofReal_prod, chartWeight_prod_inv_sqrt_eq_chartJac e hβ v]
  change F ((Real.sqrt β)⁻¹ • v) = _
  unfold F
  rw [hJ]
  by_cases hv : ∀ x, ‖v x‖ < Real.sqrt β
  · rw [basePhysicalExponent_chart e he hβ ν μ h g v hv]
  · push Not at hv
    obtain ⟨x, hx⟩ := hv
    have hz : chartJac β w = 0 :=
      chartJac_eq_zero (x₀ := x) (by simpa [w] using (not_lt.mpr hx))
    simp [w, hz]

/-- The same identity with the normalized block Gaussian written as an action. -/
theorem baseChartIntegral_eq_rescaled_action
    {β : ℝ} (hβ : 0 < β) (a ν μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (χ : CfgT d N L n → ℝ)
    (e : Torus d (L * n) → EuclideanSpace ℝ (Fin N)) (he : ∀ x, ‖e x‖ = 1) :
    baseChartIntegral d N L n β a ν h g θ χ e he =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
        ∫ v : (x : Torus d (L * n)) → perp (e x),
          let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
          let w : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := fun x => (v x : EuclideanSpace ℝ (Fin N))
          ((chartJac β w : ℝ) : ℂ) *
            ((χ φ : ℂ) *
              ((∏ _y : Torus d n,
                ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) : ℝ) : ℂ) *
              Complex.exp (
                -((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 *
                  ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 : ℝ) : ℂ) +
                (-((β * energy d N (L * n) μ h φ : ℝ) : ℂ) -
                ((β * (ν - μ) / 2 * ∑ x : Torus d (L * n),
                  ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
                (∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((e x) i : ℝ) : ℂ)) +
                (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
                  (∑ x : Torus d (L * n), ∑ i : Fin N,
                    g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)))))
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  rw [baseChartIntegral_eq_rescaled_physicalAction hβ a ν μ h g θ χ e he]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  simp only [mul_assoc]
  rw [baseKernel_mul_exp β a θ]
  ring_nf

open Classical in
/-- The all-good P5 first-step chart term, with its coarse-field-dependent background,
as a rescaled physical action integral. This is the chart term of
`baseSector_partitionFunction_eq_bad_add_chart`. -/
theorem baseSectorChartIntegral_eq_rescaled_action
    {β : ℝ} (hβ : 0 < β) (a ν δ₀ : ℝ) (regimeB : Prop)
    (ϱ : ℝ) (aw : ℕ → ℝ) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    let e := baseSectorCenter ϱ aw regimeB ν h θ
    let χ := baseSectorCubeProduct regimeB ν δ₀ h θ
    let he := baseSectorCenter_unit ϱ aw regimeB ν h hh H θ
    baseChartIntegral d N L n β a ν h g θ χ e he =
      ((Real.sqrt β)⁻¹ ^ (Fintype.card (Torus d (L * n)) * (N - 1))) •
        ∫ v : (x : Torus d (L * n)) → perp (e x),
          let φ := chartMapPi e he ((Real.sqrt β)⁻¹ • v)
          let w : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := fun x => (v x : EuclideanSpace ℝ (Fin N))
          ((chartJac β w : ℝ) : ℂ) *
            ((χ φ : ℂ) *
              ((∏ _y : Torus d n,
                ((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) : ℝ) : ℂ) *
              Complex.exp (
                -((β * a * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 *
                  ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 : ℝ) : ℂ) +
                (-((β * energy d N (L * n) (if regimeB then ν else 0) h φ : ℝ) : ℂ) -
                ((β * (ν - (if regimeB then ν else 0)) / 2 * ∑ x : Torus d (L * n),
                  ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
                (∑ x : Torus d (L * n), ∑ i : Fin N,
                  g x i * (((e x) i : ℝ) : ℂ)) +
                (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
                  (∑ x : Torus d (L * n), ∑ i : Fin N,
                    g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)))))
          ∂(Measure.pi fun x => (volume : Measure (perp (e x)))) := by
  dsimp only
  exact baseChartIntegral_eq_rescaled_action hβ a ν (if regimeB then ν else 0) h g θ
    (baseSectorCubeProduct regimeB ν δ₀ h θ)
    (baseSectorCenter ϱ aw regimeB ν h θ)
    (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ)

end

end Balaban.LargeField
