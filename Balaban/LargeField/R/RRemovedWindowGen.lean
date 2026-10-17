/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The window integral: the integration order (Lemma III.8.7 (1), (3), (4)) (W905)

`notes/phase1/LF4R-PLAN.md`, leaf 6.  The generic measure-theoretic skeleton of the proof of
(III.8.5): after a measure preserving regrouping of the integration variables into
window variables `w`, core variables `c` and Gaussian-only variables `j`, the integral of a
non-negative function `f` is bounded by integrating `j` first (the composition identity and the
pointwise bound of the exponentials, uniformly in the core variables), then the core variables
(by (D5), uniformly in the window variables), then the window variables (volume of the support).

* `lintegral_window_core_le`: if `∫ f(w, c, j) dj ≤ Core(w, c) e^Λ 1_E(w)`, `∫ Core(w, c) dc ≤ e^{-κ}`
  for every `w` and `μ_W(E) ≤ e^V`, then `∫ f ≤ e^{Λ + V - κ}`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory ENNReal

section Gen

variable {Ω Wd Cr Jv : Type*} [MeasurableSpace Ω] [MeasurableSpace Wd] [MeasurableSpace Cr]
  [MeasurableSpace Jv]

/-- **The integration order of Lemma III.8.7**: `Θ` is a measure preserving regrouping of the
integration variables into window variables `w`, core variables `c` and the variables `j`
integrated first.  See the module docstring. -/
theorem lintegral_window_core_le {μ : Measure Ω} {μW : Measure Wd} {μC : Measure Cr}
    {μJ : Measure Jv} [SFinite μW] [SFinite μC] [SFinite μJ]
    (Θ : Ω ≃ᵐ Wd × (Cr × Jv)) (hΘ : MeasurePreserving Θ μ (μW.prod (μC.prod μJ)))
    (f : Ω → ℝ≥0∞) (hf : Measurable f) (Core : Wd → Cr → ℝ≥0∞) (E : Set Wd)
    (hE : MeasurableSet E) (Λ κ V : ℝ)
    (hpt : ∀ w c, ∫⁻ j, f (Θ.symm (w, c, j)) ∂μJ ≤
      Core w c * E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w)
    (hcore : ∀ w, ∫⁻ c, Core w c ∂μC ≤ ENNReal.ofReal (Real.exp (-κ)))
    (hvol : μW E ≤ ENNReal.ofReal (Real.exp V)) :
    ∫⁻ ω, f ω ∂μ ≤ ENNReal.ofReal (Real.exp (Λ + V - κ)) := by
  have hg : Measurable fun p : Wd × (Cr × Jv) => f (Θ.symm p) := hf.comp Θ.symm.measurable
  have h1 : ∫⁻ ω, f ω ∂μ = ∫⁻ p, f (Θ.symm p) ∂(μW.prod (μC.prod μJ)) := by
    rw [← hΘ.lintegral_comp_emb Θ.measurableEmbedding (fun p => f (Θ.symm p))]
    simp
  have h4 : ∀ w, ∫⁻ q, f (Θ.symm (w, q)) ∂(μC.prod μJ) =
      ∫⁻ c, ∫⁻ j, f (Θ.symm (w, c, j)) ∂μJ ∂μC := fun w =>
    lintegral_prod _ (hg.comp measurable_prodMk_left).aemeasurable
  rw [h1, lintegral_prod _ hg.aemeasurable]
  simp_rw [h4]
  have h2 : ∀ w, ∫⁻ c, ∫⁻ j, f (Θ.symm (w, c, j)) ∂μJ ∂μC ≤
      ENNReal.ofReal (Real.exp (-κ)) *
        E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w := by
    intro w
    have hI : E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w ≠ ∞ := by
      by_cases hw : w ∈ E <;> simp [hw]
    calc ∫⁻ c, ∫⁻ j, f (Θ.symm (w, c, j)) ∂μJ ∂μC
        ≤ ∫⁻ c, Core w c * E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w ∂μC :=
          lintegral_mono fun c => hpt w c
      _ = (∫⁻ c, Core w c ∂μC) * E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w :=
          lintegral_mul_const' _ _ hI
      _ ≤ _ := by gcongr; exact hcore w
  calc ∫⁻ w, ∫⁻ c, ∫⁻ j, f (Θ.symm (w, c, j)) ∂μJ ∂μC ∂μW
      ≤ ∫⁻ w, ENNReal.ofReal (Real.exp (-κ)) *
          E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w ∂μW := lintegral_mono h2
    _ = ENNReal.ofReal (Real.exp (-κ)) *
          ∫⁻ w, E.indicator (fun _ => ENNReal.ofReal (Real.exp Λ)) w ∂μW :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (-κ)) * (ENNReal.ofReal (Real.exp Λ) * μW E) := by
        rw [lintegral_indicator_const hE]
    _ ≤ ENNReal.ofReal (Real.exp (-κ)) * (ENNReal.ofReal (Real.exp Λ) *
          ENNReal.ofReal (Real.exp V)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (Λ + V - κ)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add, ← Real.exp_add]
        congr 2; ring

end Gen

end Balaban.LargeField
