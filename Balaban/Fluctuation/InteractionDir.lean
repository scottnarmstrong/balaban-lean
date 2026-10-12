/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionParam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The directional Cauchy term of an analytic expansion (FLUCTUATION §3.3, P6 (4.13)-(4.21))

Let `f(Θ, z) = ∑_Y Ev_Y(Θ, z)` be an expansion of a function of the data `Θ` and the fluctuation
`z`, with analytic, bounded, local terms.  The term of the localized interaction of Proposition 3.3
built from `f` is the `t'`-integral of the derivative of `f` in the direction `w`, evaluated along
the ray `σ t' x₀`:

`σ ∫₀¹ ω(t') ∂_w f(Θ, σ t' x₀) dt'`.

`dirTerm` is this expression for the term `Ev_Y` (with `∂_w` the derivative `fderiv Ev (Θ,z) (0,w)`);
`dirTerm_sum` shows that the terms add up to the expression for `f`, `dirTerm_analytic` is the joint
analyticity in `(Θ, σ)`, `norm_dirTerm_le` the Cauchy bound `|σ| ‖ω‖ b / r`, `dirTerm_local` the
locality, and `dirTerm_zero` the vanishing at `σ = 0`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section Dir

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The derivative of `Ev` in the fluctuation direction `w` at `(Θ, z)`. -/
noncomputable def dirD (Ev : Λ × F → ℂ) (w : F) (Θ : Λ) (z : F) : ℂ :=
  fderiv ℂ Ev (Θ, z) (0, w)

/-- The directional Cauchy term `σ ∫₀¹ ω(t') ∂_w Ev(Θ, σ t' x₀) dt'`. -/
noncomputable def dirTerm (Ev : Λ × F → ℂ) (ω : ℂ → ℂ) (x₀ w : F) (σ : ℂ) (Θ : Λ) : ℂ :=
  σ * ∫ t in (0 : ℝ)..1, ω (t : ℂ) * dirD Ev w Θ ((σ * (t : ℂ)) • x₀)

/-- The same expression for a function `f` that is only known to be differentiable in the
fluctuation variable: the source form `∂_w f = d/dτ f(Θ, z + τ w)|₀`. -/
noncomputable def dirTermSrc (f : Λ × F → ℂ) (ω : ℂ → ℂ) (x₀ w : F) (σ : ℂ) (Θ : Λ) : ℂ :=
  σ * ∫ t in (0 : ℝ)..1, ω (t : ℂ) * lineD w (fun z => f (Θ, z)) ((σ * (t : ℂ)) • x₀)

theorem dirD_eq_lineD {Ev : Λ × F → ℂ} {Θ : Λ} {z : F} (w : F)
    (h : DifferentiableAt ℂ Ev (Θ, z)) : dirD Ev w Θ z = lineD w (fun z' => Ev (Θ, z')) z := by
  have e : lineD w (fun z' => Ev (Θ, z')) z = lineD ((0 : Λ), w) Ev (Θ, z) := by
    unfold lineD
    congr 1
    funext τ
    simp
  rw [e, lineD_eq_fderiv _ h]
  rfl

theorem lineD_congr_eventually {f g : F → ℂ} {z : F} (h : f =ᶠ[nhds z] g) (w : F) :
    lineD w f z = lineD w g z := by
  unfold lineD
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : Filter.Tendsto (fun τ : ℂ => z + τ • w) (nhds 0) (nhds z) := by
    have : Continuous fun τ : ℂ => z + τ • w := by fun_prop
    simpa using this.tendsto 0
  exact hc.eventually h

/-- The directional derivative of a finite sum. -/
theorem lineD_sum {ι : Type*} (s : Finset ι) {g : ι → F → ℂ} {z : F} (w : F)
    (h : ∀ i ∈ s, DifferentiableAt ℂ (g i) z) :
    lineD w (fun z' => ∑ i ∈ s, g i z') z = ∑ i ∈ s, lineD w (g i) z := by
  unfold lineD
  have hl : Differentiable ℂ fun τ : ℂ => z + τ • w := by fun_prop
  have h1 : ∀ i ∈ s, DifferentiableAt ℂ (fun τ : ℂ => g i (z + τ • w)) 0 := fun i hi => by
    have h2 : DifferentiableAt ℂ (g i) ((fun τ : ℂ => z + τ • w) 0) := by simpa using h i hi
    exact h2.comp (0 : ℂ) (hl 0)
  have := deriv_sum (𝕜 := ℂ) (u := s) (A := fun i τ => g i (z + τ • w)) (x := 0) h1
  have e : (fun τ : ℂ => ∑ i ∈ s, g i (z + τ • w)) = ∑ i ∈ s, fun τ : ℂ => g i (z + τ • w) := by
    funext τ; simp [Finset.sum_apply]
  simp only [e]
  exact this

variable {Ev : Λ × F → ℂ} {S : Set Λ} {B : Set F} {ω : ℂ → ℂ} {x₀ w : F} {Rσ R₁ : ℝ}

/-- **Joint analyticity in `(Θ, σ)`.** -/
theorem dirTerm_analytic (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hdom : ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → (σ * t) • x₀ ∈ B) :
    AnalyticOnNhd ℂ (fun p : Λ × ℂ => dirTerm Ev ω x₀ w p.2 p.1) (S ×ˢ ball (0 : ℂ) Rσ) := by
  have hint : AnalyticOnNhd ℂ (fun p : Λ × ℂ => ∫ t in (0 : ℝ)..1,
      ω (t : ℂ) * dirD Ev w p.1 ((p.2 * (t : ℂ)) • x₀)) (S ×ˢ ball (0 : ℂ) Rσ) := by
    refine analyticOnNhd_unitIntegral (f := fun (p : Λ × ℂ) (t : ℂ) =>
      ω t * dirD Ev w p.1 ((p.2 * t) • x₀)) hR₁ ?_
    rintro ⟨⟨Θ, σ⟩, t⟩ ⟨⟨hΘ, hσ⟩, ht⟩
    have hσ' : ‖σ‖ < Rσ := mem_ball_zero_iff.1 hσ
    have ht' : ‖t‖ < R₁ := mem_ball_zero_iff.1 ht
    have hpt : (Θ, (σ * t) • x₀) ∈ S ×ˢ B := ⟨hΘ, hdom σ hσ' t ht'⟩
    have hm : AnalyticAt ℂ (fun q : (Λ × ℂ) × ℂ => ((q.1.1, (q.1.2 * q.2) • x₀) : Λ × F))
        ((Θ, σ), t) := by
      refine AnalyticAt.prod ?_ ?_
      · exact (analyticAt_fst (𝕜 := ℂ)).comp (analyticAt_fst (𝕜 := ℂ))
      · exact (((analyticAt_snd (𝕜 := ℂ)).comp (analyticAt_fst (𝕜 := ℂ))).mul
          (analyticAt_snd (𝕜 := ℂ))).smul analyticAt_const
    have h1 : AnalyticAt ℂ (fun q : (Λ × ℂ) × ℂ =>
        fderiv ℂ Ev ((q.1.1, (q.1.2 * q.2) • x₀) : Λ × F)) ((Θ, σ), t) :=
      (hEv.fderiv _ hpt).comp_of_eq hm rfl
    have h2 : AnalyticAt ℂ (fun q : (Λ × ℂ) × ℂ =>
        fderiv ℂ Ev ((q.1.1, (q.1.2 * q.2) • x₀) : Λ × F) ((0 : Λ), w)) ((Θ, σ), t) :=
      ((ContinuousLinearMap.apply ℂ ℂ ((0 : Λ), w)).analyticAt _).comp h1
    exact ((hω t ht).comp (analyticAt_snd (𝕜 := ℂ))).mul h2
  intro p hp
  exact (analyticAt_snd (𝕜 := ℂ)).mul (hint p hp)

/-- **The Cauchy bound.** -/
theorem norm_dirTerm_le {b r Mω : ℝ} (hr : 0 < r) (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hb : ∀ u ∈ S ×ˢ B, ‖Ev u‖ ≤ b) {Θ : Λ} (hΘ : Θ ∈ S)
    {σ : ℂ} (hdom : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ B) :
    ‖dirTerm Ev ω x₀ w σ Θ‖ ≤ ‖σ‖ * (Mω * (b / r)) := by
  unfold dirTerm
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖ω (t : ℂ) * dirD Ev w Θ ((σ * (t : ℂ)) • x₀)‖ ≤
      Mω * (b / r) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
    have hz0 : ((σ * (t : ℂ)) • x₀) ∈ B := by simpa using hdom t ht' 0 (by simp [hr.le])
    have hdiff : DifferentiableAt ℂ Ev (Θ, (σ * (t : ℂ)) • x₀) :=
      (hEv _ ⟨hΘ, hz0⟩).differentiableAt
    rw [dirD_eq_lineD w hdiff, norm_mul]
    have hc := norm_lineD_le (f := fun z => Ev (Θ, z)) (x := (σ * (t : ℂ)) • x₀) (w := w)
      (r := r) (B := b) hr
      (fun τ hτ => by
        have hm := hdom t ht' τ hτ
        exact (hEv _ ⟨hΘ, hm⟩).comp (f := fun z : F => ((Θ, z) : Λ × F))
          ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ))))
      (fun τ hτ => hb _ ⟨hΘ, hdom t ht' τ hτ⟩)
    exact mul_le_mul (hωb t ht') hc (norm_nonneg _) hMω
  have := intervalIntegral.norm_integral_le_of_norm_le_const h1
  simpa using this

/-- **Vanishing at `σ = 0`.** -/
theorem dirTerm_zero (Θ : Λ) : dirTerm Ev ω x₀ w 0 Θ = 0 := by
  simp [dirTerm]

/-- **Locality.**  If the terms `Ev` are local for the relations `AgΘ`, `AgF` on the data and the
fluctuation, so are the directional terms (with respect to `Θ`, `x₀` and `w` jointly). -/
theorem dirTerm_local {AgΘ : Λ → Λ → Prop} {AgF : F → F → Prop}
    (hlin : ∀ (a a' b b' : F) (c d : ℂ), AgF a a' → AgF b b' → AgF (c • a + d • b) (c • a' + d • b'))
    (hloc : ∀ Θ ∈ S, ∀ Θ' ∈ S, ∀ z ∈ B, ∀ z' ∈ B, AgΘ Θ Θ' → AgF z z' →
      Ev (Θ, z) = Ev (Θ', z'))
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) {Θ Θ' : Λ} (hΘ : Θ ∈ S) (hΘ' : Θ' ∈ S)
    (hag : AgΘ Θ Θ') {x₀' w' : F} (hx : AgF x₀ x₀') (hw : AgF w w') {σ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdom : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ B ∧ (σ * (t : ℂ)) • x₀' + τ • w' ∈ B) :
    dirTerm Ev ω x₀ w σ Θ = dirTerm Ev ω x₀' w' σ Θ' := by
  unfold dirTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  congr 1
  have hz0 := hdom t ht 0 (by simp [hr.le])
  simp only [zero_smul, add_zero] at hz0
  rw [dirD_eq_lineD w (hEv _ ⟨hΘ, hz0.1⟩).differentiableAt,
    dirD_eq_lineD w' (hEv _ ⟨hΘ', hz0.2⟩).differentiableAt]
  unfold lineD
  refine Filter.EventuallyEq.deriv_eq ?_
  have hc : Continuous fun τ : ℂ => (σ * (t : ℂ)) • x₀ + τ • w := by fun_prop
  have hc' : Continuous fun τ : ℂ => (σ * (t : ℂ)) • x₀' + τ • w' := by fun_prop
  have hn : ∀ᶠ τ : ℂ in nhds 0, ‖τ‖ ≤ r := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
    exact (mem_ball_zero_iff.1 hτ).le
  filter_upwards [hn] with τ hτ
  have hm := hdom t ht τ hτ
  refine hloc Θ hΘ Θ' hΘ' _ hm.1 _ hm.2 hag ?_
  simpa using hlin x₀ x₀' w w' (σ * (t : ℂ)) τ hx hw

/-- Continuity of the integrand of `dirTerm` along the ray. -/
theorem continuousOn_dirD_ray (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) {Θ : Λ} (hΘ : Θ ∈ S) (σ : ℂ)
    (hdom : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (σ * (t : ℂ)) • x₀ ∈ B) :
    ContinuousOn (fun t : ℝ => dirD Ev w Θ ((σ * (t : ℂ)) • x₀)) (Icc (0 : ℝ) 1) := by
  have hg : Continuous fun t : ℝ => ((Θ, (σ * (t : ℂ)) • x₀) : Λ × F) := by fun_prop
  have h1 : ContinuousOn (fun p : Λ × F => fderiv ℂ Ev p) (S ×ˢ B) := hEv.fderiv.continuousOn
  have h2 : ContinuousOn (fun t : ℝ => fderiv ℂ Ev ((Θ, (σ * (t : ℂ)) • x₀) : Λ × F))
      (Icc (0 : ℝ) 1) :=
    h1.comp hg.continuousOn (fun t ht => ⟨hΘ, hdom t ht⟩)
  exact (ContinuousLinearMap.apply ℂ ℂ ((0 : Λ), w)).continuous.comp_continuousOn h2

/-- **The terms add up** to the expression built from `f`. -/
theorem dirTermSrc_sum {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ} {f : Λ × F → ℂ}
    (hBo : IsOpen B) (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z)) (hωc : Continuous ω)
    {Θ : Λ} (hΘ : Θ ∈ S) {σ : ℂ}
    (hdom : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (σ * (t : ℂ)) • x₀ ∈ B) :
    dirTermSrc f ω x₀ w σ Θ = ∑ Y ∈ 𝒴, dirTerm (Evs Y) ω x₀ w σ Θ := by
  unfold dirTermSrc dirTerm
  rw [← Finset.mul_sum]
  congr 1
  have hint : ∀ Y ∈ 𝒴, IntervalIntegrable (fun t : ℝ => ω (t : ℂ) *
      dirD (Evs Y) w Θ ((σ * (t : ℂ)) • x₀)) MeasureTheory.volume 0 1 := by
    intro Y _
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    exact (hωc.comp Complex.continuous_ofReal).continuousOn.mul
      (continuousOn_dirD_ray (hEv Y) hΘ σ hdom)
  rw [← intervalIntegral.integral_finsetSum hint]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [← Finset.mul_sum]
  congr 1
  have hz := hdom t ht
  have hdiff : ∀ Y ∈ 𝒴, DifferentiableAt ℂ (fun z => Evs Y (Θ, z)) ((σ * (t : ℂ)) • x₀) := by
    intro Y _
    exact ((hEv Y _ ⟨hΘ, hz⟩).comp (f := fun z : F => ((Θ, z) : Λ × F))
      ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))).differentiableAt
  have hev : (fun z => f (Θ, z)) =ᶠ[nhds ((σ * (t : ℂ)) • x₀)]
      fun z => ∑ Y ∈ 𝒴, Evs Y (Θ, z) := by
    filter_upwards [hBo.mem_nhds hz] with z hz' using hsum Θ hΘ z hz'
  rw [lineD_congr_eventually hev w, lineD_sum 𝒴 w hdiff]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [dirD_eq_lineD w (hEv Y _ ⟨hΘ, hz⟩).differentiableAt]

end Dir

end Balaban.Fluctuation
