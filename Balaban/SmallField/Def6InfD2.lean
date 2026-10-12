/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.TaylorCauchy

/-!
# Def-6: second derivatives along slices

`D2 f c v w` (the second derivative of `TaylorCauchy`) for functions analytic at `c`:
`hasDerivAt_fderiv_line` (the slice formula), `D2_congr_slice` (functions that agree on a slice have
the same `D2` in the slice directions, in possibly different spaces), `D2_sum` (finite sums).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The slice formula**: `s ↦ f'(c + s v) w` is differentiable at `0` with derivative
`D2 f c v w`, for `f` analytic at `c`. -/
theorem hasDerivAt_fderiv_line {f : E → ℂ} {c : E} (hf : AnalyticAt ℂ f c) (v w : E) :
    HasDerivAt (fun s : ℂ => fderiv ℂ f (c + s • v) w) (D2 f c v w) 0 := by
  have hg : DifferentiableAt ℂ (fderiv ℂ f) c := hf.fderiv.differentiableAt
  have h1 : HasDerivAt (fun s : ℂ => c + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add c
  have hgc : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) c)
      ((fun s : ℂ => c + s • v) 0) := by simpa using hg.hasFDerivAt
  have h2 : HasDerivAt (fun s : ℂ => fderiv ℂ f (c + s • v)) (fderiv ℂ (fderiv ℂ f) c v) 0 :=
    hgc.comp_hasDerivAt (0 : ℂ) h1
  have h3 := (ContinuousLinearMap.apply ℂ ℂ w).hasFDerivAt.comp_hasDerivAt (0 : ℂ) h2
  exact h3

/-- **Slice congruence**: if two functions, analytic at `c₁`, `c₂` (in possibly different spaces),
agree on the slices `c₁ + s v₁ + t w₁` and `c₂ + s v₂ + t w₂` for small `s`, `t`, then they have the
same second derivative in the slice directions. -/
theorem D2_congr_slice {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    {f₁ : E → ℂ} {f₂ : E₂ → ℂ} {c₁ v₁ w₁ : E} {c₂ v₂ w₂ : E₂} (h₁ : AnalyticAt ℂ f₁ c₁)
    (h₂ : AnalyticAt ℂ f₂ c₂) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ s t : ℂ, ‖s‖ < δ → ‖t‖ < δ →
      f₁ (c₁ + s • v₁ + t • w₁) = f₂ (c₂ + s • v₂ + t • w₂)) :
    D2 f₁ c₁ v₁ w₁ = D2 f₂ c₂ v₂ w₂ := by
  have key : (fun s : ℂ => fderiv ℂ f₁ (c₁ + s • v₁) w₁) =ᶠ[𝓝 0]
      fun s : ℂ => fderiv ℂ f₂ (c₂ + s • v₂) w₂ := by
    have hs : ∀ᶠ s : ℂ in 𝓝 0, ‖s‖ < δ := by
      have : Metric.ball (0 : ℂ) δ ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ hδ
      filter_upwards [this] with s hs using by simpa using hs
    have hc₁ : Continuous fun s : ℂ => c₁ + s • v₁ := by fun_prop
    have hc₂ : Continuous fun s : ℂ => c₂ + s • v₂ := by fun_prop
    have a₁ : ∀ᶠ s : ℂ in 𝓝 0, AnalyticAt ℂ f₁ (c₁ + s • v₁) :=
      (hc₁.tendsto 0 |>.eventually (by simpa using h₁.eventually_analyticAt))
    have a₂ : ∀ᶠ s : ℂ in 𝓝 0, AnalyticAt ℂ f₂ (c₂ + s • v₂) :=
      (hc₂.tendsto 0 |>.eventually (by simpa using h₂.eventually_analyticAt))
    filter_upwards [hs, a₁, a₂] with s hs a₁ a₂
    have l₁ := hasDerivAt_line (f := f₁) (c := c₁ + s • v₁) (z := w₁) (τ := 0)
      (by simpa using a₁.differentiableAt)
    have l₂ := hasDerivAt_line (f := f₂) (c := c₂ + s • v₂) (z := w₂) (τ := 0)
      (by simpa using a₂.differentiableAt)
    simp only [zero_smul, add_zero] at l₁ l₂
    have heq : (fun t : ℂ => f₁ (c₁ + s • v₁ + t • w₁)) =ᶠ[𝓝 0]
        fun t : ℂ => f₂ (c₂ + s • v₂ + t • w₂) := by
      have : Metric.ball (0 : ℂ) δ ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ hδ
      filter_upwards [this] with t ht
      have := h s t hs (by simpa using ht)
      simpa [add_assoc] using this
    exact l₁.unique (l₂.congr_of_eventuallyEq heq)
  have d₁ := hasDerivAt_fderiv_line h₁ v₁ w₁
  have d₂ := hasDerivAt_fderiv_line h₂ v₂ w₂
  exact d₁.unique (d₂.congr_of_eventuallyEq key)

/-- `D2` of a finite sum of functions analytic at `c` is the sum of the `D2`. -/
theorem D2_sum {ι : Type*} (S : Finset ι) {f : ι → E → ℂ} {c : E}
    (hf : ∀ i ∈ S, AnalyticAt ℂ (f i) c) (v w : E) :
    D2 (fun x => ∑ i ∈ S, f i x) c v w = ∑ i ∈ S, D2 (f i) c v w := by
  have hc : Continuous fun s : ℂ => c + s • v := by fun_prop
  have a : ∀ᶠ s : ℂ in 𝓝 0, ∀ i ∈ S, AnalyticAt ℂ (f i) (c + s • v) := by
    rw [Filter.eventually_all_finset]
    intro i hi
    exact (hc.tendsto 0 |>.eventually (by simpa using (hf i hi).eventually_analyticAt))
  have hsum : HasDerivAt (fun s : ℂ => ∑ i ∈ S, fderiv ℂ (f i) (c + s • v) w)
      (∑ i ∈ S, D2 (f i) c v w) 0 :=
    HasDerivAt.fun_sum fun i hi => hasDerivAt_fderiv_line (hf i hi) v w
  have hanal : AnalyticAt ℂ (fun x => ∑ i ∈ S, f i x) c := by
    exact Finset.analyticAt_fun_sum S hf
  have key : (fun s : ℂ => fderiv ℂ (fun x => ∑ i ∈ S, f i x) (c + s • v) w) =ᶠ[𝓝 0]
      fun s : ℂ => ∑ i ∈ S, fderiv ℂ (f i) (c + s • v) w := by
    filter_upwards [a] with s hs
    rw [fderiv_fun_sum fun i hi => (hs i hi).differentiableAt]
    simp
  exact (hasDerivAt_fderiv_line hanal v w).unique (hsum.congr_of_eventuallyEq key)

end Balaban.SmallField.Def6
