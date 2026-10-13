/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartAction
public import Balaban.Model.SphereMeasure

/-!
# The partition-function integrand in the hemisphere chart (BASE.md, B2; LF-BASE-KF0 (A.2))

Let `E_h = {φ | ∀ x, ⟨h, φ_x⟩ > 0}`.  For a real source `g`,
`restrictedIntegrand` is `1_{E_h}(φ) exp(-β H₀(φ) + ⟨g, φ⟩)`, the integrand of the frozen
`Balaban.partitionFunction` restricted to `E_h`.  `lintegral_restrictedIntegrand` states, with the
one-spin measure identity landed in `HemispherePi.lean` (so no hypothesis is needed):

`∫ 1_{E_h} e^{-βH₀ + ⟨g,φ⟩} d(aprioriMeasure)`
`  = β^{-(N-1)|Λ|/2} ∫ J_β(v) exp(-½⟨v,K_ν v⟩ - R_β(v) + ⟨g,h⟩ + β^{-1/2}⟨g,v⟩ + β^{-1/2}Σ_x (g_x·h) w_x) dv`,

`dv` the Lebesgue measure on `∏_x h^⊥`, `J_β(v) = ∏_x 1[‖v_x‖ < √β] (1 - ‖v_x‖²/β)^{-1/2}`
(`chartJac`).  The identity is an identity in `[0, ∞]` for a real source; the integral is the
lower integral of the nonnegative integrand.  This is the exact chart form of the action on the
event that all spins lie in the open hemisphere around `h`; no estimate of the complementary event,
no expansion and no statement about Root-F are proved here.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.LargeField

open SphereChart

noncomputable section

variable {d N ℓ : ℕ} [NeZero ℓ]

/-- `1_{E_h}(φ) exp(-β H₀(φ) + ⟨g, φ⟩)` as an extended nonnegative number (real source `g`). -/
def restrictedIntegrand (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℝ)
    (φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : ENNReal :=
  if ∀ x, 0 < inner ℝ h (φ x : EuclideanSpace ℝ (Fin N)) then
    ENNReal.ofReal (Real.exp (-(β * energy d N ℓ ν h φ) + sourcePair g φ))
  else 0

theorem measurable_restrictedIntegrand (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : Torus d ℓ → Fin N → ℝ) : Measurable (restrictedIntegrand β ν h g) := by
  unfold restrictedIntegrand
  refine Measurable.ite ?_ ?_ measurable_const
  · have : {φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 |
        ∀ x, 0 < inner ℝ h (φ x : EuclideanSpace ℝ (Fin N))} =
        ⋂ x, {φ | 0 < inner ℝ h (φ x : EuclideanSpace ℝ (Fin N))} := by
      ext φ; simp
    rw [show {φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 |
        ∀ x, 0 < inner ℝ h (φ x : EuclideanSpace ℝ (Fin N))} = _ from this]
    refine MeasurableSet.iInter fun x => ?_
    have hc : Continuous fun φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 =>
        inner ℝ h (φ x : EuclideanSpace ℝ (Fin N)) :=
      continuous_const.inner ((continuous_subtype_val).comp (continuous_apply x))
    exact measurableSet_lt measurable_const hc.measurable
  · refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    refine Continuous.measurable ?_
    unfold energy sourcePair
    fun_prop

/-- The exponent of the integrand in the rescaled chart variable `v`:
`-½⟨v,K_ν v⟩ - R_β(v) + ⟨g,h⟩ + β^{-1/2}⟨g,v⟩ + β^{-1/2} ∑_x (g_x·h) w_x`. -/
def chartActionExponent (β ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (g : Torus d ℓ → Fin N → ℝ)
    (v : Torus d ℓ → perp h) : ℝ :=
  -(tangentEnergy ν v) - chartRemainder β ν v + sourceConst g h +
    (Real.sqrt β)⁻¹ * sourceTangent g v + (Real.sqrt β)⁻¹ * sourceNormal g h β v

/-- Pointwise form of the rescaling `ξ = β^{-1/2} v` of the restricted integrand. -/
theorem chart_pointwise_restricted {β : ℝ} (hβ : 0 < β) (ν : ℝ) {h : EuclideanSpace ℝ (Fin N)}
    (hh : ‖h‖ = 1) (g : Torus d ℓ → Fin N → ℝ) (v : Torus d ℓ → perp h) :
    (∏ x : Torus d ℓ, ENNReal.ofReal (chartWeight h (((Real.sqrt β)⁻¹ • v) x))) *
        restrictedIntegrand β ν h g (chartCfg h hh ((Real.sqrt β)⁻¹ • v)) =
      ENNReal.ofReal (chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N)))) *
        ENNReal.ofReal (Real.exp (chartActionExponent β ν h g v)) := by
  by_cases hb : ∀ x, ‖v x‖ < Real.sqrt β
  · have hv : ∀ x, ‖v x‖ ^ 2 < β := fun x => by
      have := (Real.lt_sqrt (norm_nonneg _)).1 (hb x)
      exact this
    have hJ : ∏ x : Torus d ℓ, ENNReal.ofReal (chartWeight h (((Real.sqrt β)⁻¹ • v) x)) =
        ENNReal.ofReal (chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N)))) := by
      rw [chartJac_of_lt (w := fun x => (v x : EuclideanSpace ℝ (Fin N))) hb,
        ENNReal.ofReal_prod_of_nonneg (fun x _ => by positivity)]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]
      have hx := hb x
      have hx' : ‖(v x : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := hx
      simp only [hx', ↓reduceIte]
    have hcond : ∀ x, 0 < inner ℝ h
        ((chartCfg h hh ((Real.sqrt β)⁻¹ • v) x : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
          EuclideanSpace ℝ (Fin N)) := fun x => by
      have hlt : ‖((Real.sqrt β)⁻¹ • v) x‖ < 1 := by
        rw [Pi.smul_apply]; exact (norm_inv_sqrt_smul_lt_one_iff hβ (v x)).2 (hb x)
      exact inner_hemiPt_pos h hh hlt
    have hexp : -(β * energy d N ℓ ν h (chartCfg h hh ((Real.sqrt β)⁻¹ • v))) +
        sourcePair g (chartCfg h hh ((Real.sqrt β)⁻¹ • v)) = chartActionExponent β ν h g v := by
      rw [energy_chartCfg hβ hh ν v hv, source_chartCfg hβ hh g v hv, chartActionExponent,
        tangentEnergy_eq]
      ring
    rw [hJ]
    unfold restrictedIntegrand
    simp only [hcond, implies_true, ↓reduceIte, hexp]
  · push Not at hb
    obtain ⟨x₀, hx₀⟩ := hb
    have h0 : chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N))) = 0 :=
      chartJac_eq_zero (x₀ := x₀) (not_lt.2 hx₀)
    have hp : ∏ x : Torus d ℓ, ENNReal.ofReal (chartWeight h (((Real.sqrt β)⁻¹ • v) x)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ x₀) ?_
      rw [Pi.smul_apply, chartWeight_inv_sqrt_smul hβ]
      have hx : ¬ ‖(v x₀ : EuclideanSpace ℝ (Fin N))‖ < Real.sqrt β := not_lt.2 hx₀
      simp only [hx, ↓reduceIte, ENNReal.ofReal_zero]
    rw [hp, h0]; simp

/-- **The restricted partition integrand in the rescaled chart** (LF-BASE-KF0 (A.2)–(A.3), full
torus).  For `β > 0`, `|h| = 1` and a real source `g`,
`∫ 1_{E_h} exp(-βH₀ + ⟨g,φ⟩) d(aprioriMeasure) =
  β^{-(N-1)|Λ|/2} ∫ J_β(v) exp(-½⟨v,K_ν v⟩ - R_β(v) + ⟨g,h⟩ + β^{-1/2}⟨g,v⟩ +
  β^{-1/2} ∑_x (g_x·h) w_x) dv`,
where `β^{-(N-1)|Λ|/2}` is `((√β)⁻¹)^{|Λ|(N-1)}` and `dv` is Lebesgue measure on `∏_x h^⊥`. -/
theorem lintegral_restrictedIntegrand {β : ℝ} (hβ : 0 < β) (ν : ℝ) {h : EuclideanSpace ℝ (Fin N)}
    (hh : ‖h‖ = 1) (g : Torus d ℓ → Fin N → ℝ) :
    ∫⁻ φ, restrictedIntegrand β ν h g φ ∂(aprioriMeasure d N ℓ) =
      ENNReal.ofReal (((Real.sqrt β)⁻¹) ^ (Fintype.card (Torus d ℓ) * (N - 1))) *
        ∫⁻ v : Torus d ℓ → perp h,
          ENNReal.ofReal (chartJac β (fun x => (v x : EuclideanSpace ℝ (Fin N)))) *
            ENNReal.ofReal (Real.exp (chartActionExponent β ν h g v))
          ∂(Measure.pi fun _ => (volume : Measure (perp h))) := by
  have hspos : 0 < (Real.sqrt β)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hβ)
  have hsupp : ∀ φ : Torus d ℓ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∃ x, ¬ 0 < inner ℝ ((fun _ : Torus d ℓ => h) x) (φ x : EuclideanSpace ℝ (Fin N))) →
        restrictedIntegrand β ν h g φ = 0 := by
    intro φ hφ
    unfold restrictedIntegrand
    have hn : ¬ ∀ x, 0 < inner ℝ h (φ x : EuclideanSpace ℝ (Fin N)) := fun H => by
      obtain ⟨x, hx⟩ := hφ
      exact hx (H x)
    simp only [hn, ↓reduceIte]
  have hA := lintegral_sphere_pi_hemisphere (ι := Torus d ℓ) (fun _ => h) (fun _ => hh)
    (restrictedIntegrand β ν h g) (measurable_restrictedIntegrand β ν h g) hsupp
  change ∫⁻ φ, restrictedIntegrand β ν h g φ ∂(Measure.pi fun _ : Torus d ℓ =>
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) = _
  rw [hA]
  set Φ : (Torus d ℓ → perp h) → ENNReal := fun ξ =>
    (∏ x, ENNReal.ofReal (chartWeight h (ξ x))) *
      restrictedIntegrand β ν h g (chartMapPi (fun _ => h) (fun _ => hh) ξ) with hΦ
  have hΦm : Measurable Φ :=
    (Finset.measurable_prod _ fun x _ => ENNReal.measurable_ofReal.comp
      ((measurable_chartWeight h).comp (measurable_pi_apply x))).mul
      ((measurable_restrictedIntegrand β ν h g).comp
        (measurable_chartMapPi (fun _ => h) (fun _ => hh)))
  have hB := lintegral_eq_pow_mul_lintegral_smul
    (Measure.pi fun _ : Torus d ℓ => (volume : Measure (perp h))) hspos hΦm
  rw [show Module.finrank ℝ (Torus d ℓ → perp h) = Fintype.card (Torus d ℓ) * (N - 1) from
    finrank_pi_perp (fun _ : Torus d ℓ => h) (fun _ => hh)] at hB
  refine hB.trans ?_
  congr 1
  refine lintegral_congr fun v => ?_
  exact chart_pointwise_restricted hβ ν hh g v

end

end Balaban.LargeField
