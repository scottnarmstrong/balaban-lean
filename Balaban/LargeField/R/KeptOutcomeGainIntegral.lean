module

public import Balaban.LargeField.R.KeptOutcomeGain23
public import Balaban.LargeField.R.KeptOutcomeWindow

/-!
# Passing the second and third kept gains through the node integral

This is the inequality needed at the inner `hid` input of
`keptKernel_kerBound_of_window`. The nonnegative density `ρ` is the Gaussian
chain integrated by `window_node_integral_eq_of_history`; `hpoint` is the
pointwise kernel comparison required by `window_hid_core_glue`. The latter
comparison is still source input for the kept history instance.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

/-- The gain of Lemma III.5.3 passes through the exact Gaussian node integral.
`hnode` is the bound supplied by `window_node_integral_eq_of_history` after
identifying its Gaussian chain with `ρ`. The conclusion has the factorization
of the `hid` input of `keptKernel_kerBound_of_window`. -/
theorem kept_hid_gain_of_node_integral {J : Type*} [MeasurableSpace J]
    (μ : Measure J) (F ρ : J → ℝ≥0∞) (Gwin Awin : J → ℝ)
    (Core Node : ℝ≥0∞) (bw Lc C γ : ℝ)
    (hpoint : ∀ j, F j ≤
      (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc)) *
        ENNReal.ofReal (Real.exp (-Gwin j - Awin j)) * ρ j)
    (hgain : ∀ j, ρ j ≠ 0 → γ ≤ Gwin j + Awin j + C)
    (hρmeas : Measurable ρ)
    (hnode : ∫⁻ j, ρ j ∂μ ≤ Node) :
    ∫⁻ j, F j ∂μ ≤
      (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc) *
        ENNReal.ofReal (Real.exp (C - γ))) * Node := by
  have hpt : ∀ j, F j ≤
      (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc) *
        ENNReal.ofReal (Real.exp (C - γ))) * ρ j := by
    intro j
    by_cases hz : ρ j = 0
    · simpa [hz] using hpoint j
    · have he : ENNReal.ofReal (Real.exp (-Gwin j - Awin j)) ≤
          ENNReal.ofReal (Real.exp (C - γ)) :=
        ENNReal.ofReal_le_ofReal (kept_two_exp_gain_of_action
          (Gwin j) (Awin j) C γ (hgain j hz))
      exact (hpoint j).trans (by gcongr)
  calc
    ∫⁻ j, F j ∂μ ≤ ∫⁻ j, (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc) *
        ENNReal.ofReal (Real.exp (C - γ))) * ρ j ∂μ := lintegral_mono hpt
    _ = (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc) *
        ENNReal.ofReal (Real.exp (C - γ))) * (∫⁻ j, ρ j ∂μ) :=
      lintegral_const_mul _ hρmeas
    _ ≤ _ := by gcongr

/-- Outside the window, a pointwise vanishing kept kernel gives the `hsupp`
input of `keptKernel_kerBound_of_window`. -/
theorem kept_hsupp_of_pointwise_zero {J : Type*} [MeasurableSpace J]
    (μ : Measure J) (F : J → ℝ≥0∞) (hzero : ∀ j, F j = 0) :
    ∫⁻ j, F j ∂μ = 0 := by
  simp [hzero]

/-- Put the node bound into the core and write the result in the `hid` form
used by `keptKernel_kerBound_of_window`, with `frac = exp (C - γ)`. -/
theorem kept_hid_gain_of_node_integral' {J : Type*} [MeasurableSpace J]
    (μ : Measure J) (F ρ : J → ℝ≥0∞) (Gwin Awin : J → ℝ)
    (Core Node : ℝ≥0∞) (bw Lc C γ : ℝ)
    (hpoint : ∀ j, F j ≤
      (Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc)) *
        ENNReal.ofReal (Real.exp (-Gwin j - Awin j)) * ρ j)
    (hgain : ∀ j, ρ j ≠ 0 → γ ≤ Gwin j + Awin j + C)
    (hρmeas : Measurable ρ)
    (hnode : ∫⁻ j, ρ j ∂μ ≤ Node) :
    ∫⁻ j, F j ∂μ ≤ (Core * Node) *
      ENNReal.ofReal (Real.exp bw * Real.exp Lc * Real.exp (C - γ)) := by
  have h := kept_hid_gain_of_node_integral μ F ρ Gwin Awin Core Node bw Lc C γ
    hpoint hgain hρmeas hnode
  calc
    ∫⁻ j, F j ∂μ ≤ Core * ENNReal.ofReal (Real.exp bw * Real.exp Lc) *
        ENNReal.ofReal (Real.exp (C - γ)) * Node := h
    _ = (Core * Node) *
        ENNReal.ofReal (Real.exp bw * Real.exp Lc * Real.exp (C - γ)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp bw * Real.exp Lc)]
      ac_rfl

/-- The residual factor required by the consumer is bounded once its logarithm
is included in `Fr`. -/
theorem kept_hfrac_of_gain (C γ Fr : ℝ) (hFr : C - γ ≤ Fr) :
    0 ≤ Real.exp (C - γ) ∧ Real.exp (C - γ) ≤ Real.exp Fr :=
  ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr hFr⟩

end Balaban.LargeField
