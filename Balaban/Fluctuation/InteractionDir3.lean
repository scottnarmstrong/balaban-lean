/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir
public import Balaban.Fluctuation.InteractionLoc
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The third-derivative term of an analytic expansion (FLUCTUATION §3.3, P6 (4.4)-(4.6))

The potential part of (3.3) is `σ ∫₀¹ ω(t') V'''(σ t' x₀)[w]³ dt'` with `ω(t') = (1-t')²/2` and
`V'''(z)[w]³ = d³/dτ³ V(z + τ w)|₀`.  For an expansion `V(Θ, z) = ∑_Y Ev_Y(Θ, z)` with analytic
terms the third derivative of a term is `lineD v (lineD v (lineD v Ev))` for the direction
`v = (0, w)` (`dirL3`); it is analytic in `(Θ, z)`, it equals the third derivative of the line
function `τ ↦ Ev(Θ, z + τ w)` (`dirL3_eq`, so the Cauchy estimate `6 B / r³` of Liouville's theorem
applies: `norm_dirL3_le`), and it depends on `Θ`, `z`, `w` only through what `Ev` depends on.
`raySrc3` is the same expression for a function `f` which is only known to be the sum of the terms
along the line.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_lineD {f : E → ℂ} {x : E} (v : E) (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (lineD v f) x := by
  have hev : ∀ᶠ y in nhds x, AnalyticAt ℂ f y := hf.eventually_analyticAt
  have ha : AnalyticAt ℂ (fun s => fderiv ℂ f s v) x :=
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt (fderiv ℂ f x)).comp hf.fderiv
  refine ha.congr ?_
  filter_upwards [hev] with y hy
  exact (lineD_eq_fderiv v hy.differentiableAt).symm

/-- The iterated derivative of the line function is the iterated directional derivative, on a
disc around which `f` is analytic. -/
theorem iteratedDeriv_line (a v : E) {r : ℝ} :
    ∀ (n : ℕ) (f : E → ℂ), (∀ τ : ℂ, ‖τ‖ < r → AnalyticAt ℂ f (a + τ • v)) →
      ∀ τ : ℂ, ‖τ‖ < r →
        iteratedDeriv n (fun s : ℂ => f (a + s • v)) τ = (lineD v)^[n] f (a + τ • v) := by
  intro n
  induction n with
  | zero => intro f _ τ _; simp
  | succ n ih =>
    intro f hf τ hτ
    have hderiv : ∀ τ' : ℂ, ‖τ'‖ < r →
        deriv (fun s : ℂ => f (a + s • v)) τ' = lineD v f (a + τ' • v) := by
      intro τ' hτ'
      unfold lineD
      have : (fun s : ℂ => f (a + s • v)) = fun s => (fun u : ℂ => f (a + τ' • v + u • v)) (s - τ') := by
        funext s; congr 1; simp [sub_smul]
      rw [this]
      exact deriv_comp_sub_const (a := τ') (f := fun u : ℂ => f (a + τ' • v + u • v)) (x := τ') |>.trans
        (by simp)
    rw [Function.iterate_succ_apply, iteratedDeriv_succ']
    have hev : (deriv fun s : ℂ => f (a + s • v)) =ᶠ[nhds τ]
        fun s : ℂ => lineD v f (a + s • v) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show τ ∈ ball (0 : ℂ) r by simpa using hτ)] with
        s hs using hderiv s (by simpa using hs)
    rw [hev.iteratedDeriv_eq]
    exact ih (lineD v f) (fun τ' hτ' => analyticAt_lineD v (hf τ' hτ')) τ hτ

end Line

section Dir3

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The third directional derivative of `Ev` in the fluctuation direction `w`
(`lineD v (lineD v (lineD v Ev))`, `v = (0, w)`). -/
noncomputable def dirL3 (Ev : Λ × F → ℂ) (w : F) (Θ : Λ) (z : F) : ℂ :=
  lineD ((0 : Λ), w) (lineD ((0 : Λ), w) (lineD ((0 : Λ), w) Ev)) (Θ, z)

/-- The third derivative of the line function `τ ↦ f(Θ, z + τ w)` at `0`. -/
noncomputable def dirS3 (f : Λ × F → ℂ) (w : F) (Θ : Λ) (z : F) : ℂ :=
  iteratedDeriv 3 (fun τ : ℂ => f (Θ, z + τ • w)) 0

/-- The integral of `g` along the ray `t ↦ σ t x₀`, with weight `ω`. -/
noncomputable def rayTerm (g : Λ × F → ℂ) (ω : ℂ → ℂ) (x₀ : F) (σ : ℂ) (Θ : Λ) : ℂ :=
  σ * ∫ t in (0 : ℝ)..1, ω (t : ℂ) * g (Θ, (σ * (t : ℂ)) • x₀)

/-- The same for the source expression of the third derivative. -/
noncomputable def raySrc3 (f : Λ × F → ℂ) (ω : ℂ → ℂ) (x₀ w : F) (σ : ℂ) (Θ : Λ) : ℂ :=
  σ * ∫ t in (0 : ℝ)..1, ω (t : ℂ) * dirS3 f w Θ ((σ * (t : ℂ)) • x₀)

theorem dirL3_eq {Ev : Λ × F → ℂ} {Θ : Λ} {z w : F} {r : ℝ} (hr : 0 < r)
    (hf : ∀ τ : ℂ, ‖τ‖ < r → AnalyticAt ℂ Ev (Θ, z + τ • w)) :
    dirL3 Ev w Θ z = dirS3 Ev w Θ z := by
  unfold dirL3 dirS3
  have h := iteratedDeriv_line (E := Λ × F) (Θ, z) ((0 : Λ), w) (r := r) 3 Ev
    (fun τ hτ => by simpa using hf τ hτ) 0 (by simpa using hr)
  have e : (fun s : ℂ => Ev (((Θ, z) : Λ × F) + s • ((0 : Λ), w))) =
      fun τ : ℂ => Ev (Θ, z + τ • w) := by
    funext s; simp
  rw [e] at h
  rw [h]
  simp [Function.iterate_succ]

theorem analyticAt_dirL3 {Ev : Λ × F → ℂ} {x : Λ × F} (hx : AnalyticAt ℂ Ev x) (w : F) :
    AnalyticAt ℂ (lineD ((0 : Λ), w) (lineD ((0 : Λ), w) (lineD ((0 : Λ), w) Ev))) x :=
  analyticAt_lineD _ (analyticAt_lineD _ (analyticAt_lineD _ hx))

/-- **The Cauchy estimate for the third directional derivative** (Liouville's theorem). -/
theorem norm_dirL3_le {Ev : Λ × F → ℂ} {Θ : Λ} {z w : F} {r B : ℝ} (hr : 0 < r)
    (hf : ∀ τ : ℂ, ‖τ‖ ≤ r → AnalyticAt ℂ Ev (Θ, z + τ • w))
    (hB : ∀ τ : ℂ, ‖τ‖ ≤ r → ‖Ev (Θ, z + τ • w)‖ ≤ B) :
    ‖dirL3 Ev w Θ z‖ ≤ 6 * B / r ^ 3 := by
  rw [dirL3_eq hr (fun τ hτ => hf τ hτ.le)]
  unfold dirS3
  have hd : DiffContOnCl ℂ (fun τ : ℂ => Ev (Θ, z + τ • w)) (ball (0 : ℂ) r) := by
    refine DifferentiableOn.diffContOnCl fun τ hτ => ?_
    have hτ' : ‖τ‖ ≤ r := by
      have := closure_ball_subset_closedBall hτ
      rwa [mem_closedBall_zero_iff] at this
    exact ((hf τ hτ').comp (f := fun τ : ℂ => ((Θ, z + τ • w) : Λ × F))
      ((analyticAt_const (𝕜 := ℂ)).prod (by fun_prop))).differentiableAt.differentiableWithinAt
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 3 (c := (0 : ℂ)) hr hd
    (fun τ hτ => hB τ (by simpa using hτ.le))
  simpa [Nat.factorial] using this

omit [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] in
theorem dirS3_congr {f g : Λ × F → ℂ} {Θ Θ' : Λ} {z z' w w' : F}
    (h : (fun τ : ℂ => f (Θ, z + τ • w)) =ᶠ[nhds 0] fun τ : ℂ => g (Θ', z' + τ • w')) :
    dirS3 f w Θ z = dirS3 g w' Θ' z' := by
  unfold dirS3
  exact h.iteratedDeriv_eq 3

/-- The third derivative of a finite sum along a line. -/
theorem dirS3_sum {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ} {f : Λ × F → ℂ}
    {Θ : Λ} {z w : F} {r : ℝ} (hr : 0 < r)
    (hf : ∀ Y ∈ 𝒴, ∀ τ : ℂ, ‖τ‖ < r → AnalyticAt ℂ (Evs Y) (Θ, z + τ • w))
    (hsum : ∀ τ : ℂ, ‖τ‖ < r → f (Θ, z + τ • w) = ∑ Y ∈ 𝒴, Evs Y (Θ, z + τ • w)) :
    dirS3 f w Θ z = ∑ Y ∈ 𝒴, dirS3 (Evs Y) w Θ z := by
  unfold dirS3
  have hev : (fun τ : ℂ => f (Θ, z + τ • w)) =ᶠ[nhds 0]
      fun τ : ℂ => ∑ Y ∈ 𝒴, Evs Y (Θ, z + τ • w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ using hsum τ (by simpa using hτ)
  rw [hev.iteratedDeriv_eq]
  have hline : AnalyticAt ℂ (fun τ : ℂ => ((Θ, z + τ • w) : Λ × F)) 0 := by
    refine AnalyticAt.prod analyticAt_const ?_
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hcd : ∀ Y ∈ 𝒴, ContDiffAt ℂ 3 (fun τ : ℂ => Evs Y (Θ, z + τ • w)) 0 := by
    intro Y hY
    have h0 : AnalyticAt ℂ (Evs Y) ((fun τ : ℂ => ((Θ, z + τ • w) : Λ × F)) 0) := by
      simpa using hf Y hY 0 (by simpa using hr)
    exact (h0.comp_of_eq hline rfl).contDiffAt
  have := iteratedDeriv_sum (𝕜 := ℂ) (I := 𝒴) (n := 3) (x := (0 : ℂ))
    (f := fun Y τ => Evs Y (Θ, z + τ • w)) hcd
  have e : (fun τ : ℂ => ∑ Y ∈ 𝒴, Evs Y (Θ, z + τ • w)) =
      ∑ Y ∈ 𝒴, fun τ : ℂ => Evs Y (Θ, z + τ • w) := by
    funext τ; simp [Finset.sum_apply]
  rw [e]
  exact this

/-- The third directional derivative as a function on `Λ × F`. -/
noncomputable def dl3 (Ev : Λ × F → ℂ) (w : F) : Λ × F → ℂ :=
  lineD ((0 : Λ), w) (lineD ((0 : Λ), w) (lineD ((0 : Λ), w) Ev))

theorem dl3_apply (Ev : Λ × F → ℂ) (w : F) (Θ : Λ) (z : F) : dl3 Ev w (Θ, z) = dirL3 Ev w Θ z :=
  rfl

variable {S : Set Λ} {B : Set F} {ω : ℂ → ℂ} {x₀ w : F} {Rσ R₁ : ℝ}

/-- **Joint analyticity in `(Θ, σ)` of the ray integral of an analytic function.** -/
theorem rayTerm_analytic {g : Λ × F → ℂ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hg : AnalyticOnNhd ℂ g (S ×ˢ B))
    (hdom : ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → (σ * t) • x₀ ∈ B) :
    AnalyticOnNhd ℂ (fun p : Λ × ℂ => rayTerm g ω x₀ p.2 p.1) (S ×ˢ ball (0 : ℂ) Rσ) := by
  have hint : AnalyticOnNhd ℂ (fun p : Λ × ℂ => ∫ t in (0 : ℝ)..1,
      ω (t : ℂ) * g (p.1, (p.2 * (t : ℂ)) • x₀)) (S ×ˢ ball (0 : ℂ) Rσ) := by
    refine analyticOnNhd_unitIntegral (f := fun (p : Λ × ℂ) (t : ℂ) =>
      ω t * g (p.1, (p.2 * t) • x₀)) hR₁ ?_
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
    exact ((hω t ht).comp (analyticAt_snd (𝕜 := ℂ))).mul ((hg _ hpt).comp_of_eq hm rfl)
  intro p hp
  exact (analyticAt_snd (𝕜 := ℂ)).mul (hint p hp)

omit [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] in
theorem rayTerm_zero (g : Λ × F → ℂ) (Θ : Λ) : rayTerm g ω x₀ 0 Θ = 0 := by
  simp [rayTerm]

omit [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] in
theorem norm_rayTerm_le {g : Λ × F → ℂ} {b Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {Θ : Λ} {σ : ℂ}
    (hg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖g (Θ, (σ * (t : ℂ)) • x₀)‖ ≤ b) :
    ‖rayTerm g ω x₀ σ Θ‖ ≤ ‖σ‖ * (Mω * b) := by
  unfold rayTerm
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖ω (t : ℂ) * g (Θ, (σ * (t : ℂ)) • x₀)‖ ≤ Mω * b := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
    rw [norm_mul]
    exact mul_le_mul (hωb t ht') (hg t ht') (norm_nonneg _) hMω
  have := intervalIntegral.norm_integral_le_of_norm_le_const h1
  simpa using this

/-- **The sum of the third-derivative terms** is the expression built from `f`. -/
theorem raySrc3_sum {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ} {f : Λ × F → ℂ}
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z)) (hωc : Continuous ω)
    {Θ : Λ} (hΘ : Θ ∈ S) {σ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdom : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r → (σ * (t : ℂ)) • x₀ + τ • w ∈ B) :
    raySrc3 f ω x₀ w σ Θ = ∑ Y ∈ 𝒴, rayTerm (dl3 (Evs Y) w) ω x₀ σ Θ := by
  unfold raySrc3 rayTerm
  rw [← Finset.mul_sum]
  congr 1
  have hint : ∀ Y ∈ 𝒴, IntervalIntegrable (fun t : ℝ => ω (t : ℂ) *
      dl3 (Evs Y) w (Θ, (σ * (t : ℂ)) • x₀)) MeasureTheory.volume 0 1 := by
    intro Y _
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le zero_le_one]
    have hg : ContinuousOn (dl3 (Evs Y) w) (S ×ˢ B) := by
      intro u hu
      exact (analyticAt_dirL3 (hEv Y u hu) w).continuousAt.continuousWithinAt
    have hc : Continuous fun t : ℝ => ((Θ, (σ * (t : ℂ)) • x₀) : Λ × F) := by fun_prop
    exact (hωc.comp Complex.continuous_ofReal).continuousOn.mul
      (hg.comp hc.continuousOn (fun t ht => ⟨hΘ, by simpa using hdom t ht 0 (by simp [hr.le])⟩))
  rw [← intervalIntegral.integral_finsetSum hint]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [← Finset.mul_sum]
  congr 1
  have hz := hdom t ht
  have hfa : ∀ Y ∈ 𝒴, ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ (Evs Y) (Θ, (σ * (t : ℂ)) • x₀ + τ • w) := fun Y _ τ hτ =>
    hEv Y _ ⟨hΘ, hz τ hτ.le⟩
  rw [dirS3_sum 𝒴 hr hfa (fun τ hτ => hsum Θ hΘ _ (hz τ hτ.le))]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [dl3_apply, dirL3_eq hr (hfa Y hY)]

theorem dirS3_eq_sum_dl3 {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ}
    {f : Λ × F → ℂ} (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z))
    {Θ : Λ} (hΘ : Θ ∈ S) {z : F} {r : ℝ} (hr : 0 < r)
    (hdom : ∀ τ : ℂ, ‖τ‖ ≤ r → z + τ • w ∈ B) :
    dirS3 f w Θ z = ∑ Y ∈ 𝒴, dl3 (Evs Y) w (Θ, z) := by
  have hfa : ∀ Y ∈ 𝒴, ∀ τ : ℂ, ‖τ‖ < r → AnalyticAt ℂ (Evs Y) (Θ, z + τ • w) :=
    fun Y _ τ hτ => hEv Y _ ⟨hΘ, hdom τ hτ.le⟩
  rw [dirS3_sum 𝒴 hr hfa (fun τ hτ => hsum Θ hΘ _ (hdom τ hτ.le))]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [dl3_apply, dirL3_eq hr (hfa Y hY)]

/-- A function that is a finite sum of analytic terms is smooth along a line. -/
theorem contDiffAt_line_of_sum {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ}
    {f : Λ × F → ℂ} (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z))
    {Θ : Λ} (hΘ : Θ ∈ S) {z : F} {r : ℝ} (hr : 0 < r)
    (hdom : ∀ τ : ℂ, ‖τ‖ ≤ r → z + τ • w ∈ B) :
    ContDiffAt ℂ 3 (fun τ : ℂ => f (Θ, z + τ • w)) 0 := by
  have hev : (fun τ : ℂ => f (Θ, z + τ • w)) =ᶠ[nhds 0]
      fun τ : ℂ => ∑ Y ∈ 𝒴, Evs Y (Θ, z + τ • w) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ using
      hsum Θ hΘ _ (hdom τ (mem_ball_zero_iff.1 hτ).le)
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hline : AnalyticAt ℂ (fun τ : ℂ => ((Θ, z + τ • w) : Λ × F)) 0 := by
    refine AnalyticAt.prod analyticAt_const ?_
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  refine ContDiffAt.sum fun Y _ => ?_
  have h0 : AnalyticAt ℂ (Evs Y) ((fun τ : ℂ => ((Θ, z + τ • w) : Λ × F)) 0) := by
    simpa using hEv Y _ ⟨hΘ, by simpa using hdom 0 (by simp [hr.le])⟩
  exact (h0.comp_of_eq hline rfl).contDiffAt

/-- The ray integrand of `raySrc3` is integrable. -/
theorem raySrc3_intervalIntegrable {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ}
    {f : Λ × F → ℂ} (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z)) (hωc : Continuous ω)
    {Θ : Λ} (hΘ : Θ ∈ S) {σ : ℂ} {r : ℝ} (hr : 0 < r)
    (hdom : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r → (σ * (t : ℂ)) • x₀ + τ • w ∈ B) :
    IntervalIntegrable (fun t : ℝ => ω (t : ℂ) * dirS3 f w Θ ((σ * (t : ℂ)) • x₀))
      MeasureTheory.volume 0 1 := by
  classical
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le zero_le_one]
  have hcont : ContinuousOn (fun t : ℝ => ∑ Y ∈ 𝒴, ω (t : ℂ) *
      dl3 (Evs Y) w (Θ, (σ * (t : ℂ)) • x₀)) (Icc (0 : ℝ) 1) := by
    refine continuousOn_finsetSum _ fun Y _ => ?_
    have hg : ContinuousOn (dl3 (Evs Y) w) (S ×ˢ B) := by
      intro u hu
      exact (analyticAt_dirL3 (hEv Y u hu) w).continuousAt.continuousWithinAt
    have hc : Continuous fun t : ℝ => ((Θ, (σ * (t : ℂ)) • x₀) : Λ × F) := by fun_prop
    exact (hωc.comp Complex.continuous_ofReal).continuousOn.mul
      (hg.comp hc.continuousOn (fun t ht => ⟨hΘ, by simpa using hdom t ht 0 (by simp [hr.le])⟩))
  refine hcont.congr fun t ht => ?_
  rw [dirS3_eq_sum_dl3 𝒴 hEv hsum hΘ hr (hdom t ht), Finset.mul_sum]

/-- **The third-derivative terms form a localized expansion.** -/
theorem locInt_dir3 {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ} {f : Λ × F → ℂ}
    {b : ι → ℝ} {AgΘ : ι → Λ → Λ → Prop} {AgF : ι → F → F → Prop}
    (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hωc : Continuous ω)
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r : ℝ} (hr : 0 < r) (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hb : ∀ Y, ∀ u ∈ S ×ˢ B, ‖Evs Y u‖ ≤ b Y)
    (hlin : ∀ Y (a a' c c' : F) (p q : ℂ), AgF Y a a' → AgF Y c c' →
      AgF Y (p • a + q • c) (p • a' + q • c'))
    (hloc : ∀ Y, ∀ Θ ∈ S, ∀ Θ' ∈ S, ∀ z ∈ B, ∀ z' ∈ B, AgΘ Y Θ Θ' → AgF Y z z' →
      Evs Y (Θ, z) = Evs Y (Θ', z'))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z)) :
    LocInt S {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
        (σ * t) • xw.1 + τ • xw.2 ∈ B} Rσ 𝒴
      (fun Y x₀ w σ Θ => rayTerm (dl3 (Evs Y) w) ω x₀ σ Θ)
      (fun x₀ w σ Θ => raySrc3 f ω x₀ w σ Θ) (fun Y => Mω * (6 * ‖(b Y : ℝ)‖ / r ^ 3)) AgΘ AgF := by
  have hreal : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hdom0 : ∀ xw ∈ {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
        (σ * t) • xw.1 + τ • xw.2 ∈ B}, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ →
        (σ * t) • xw.1 ∈ B := fun xw hxw σ hσ t ht => by
    simpa using hxw σ hσ t ht 0 (by simp [hr.le])
  refine ⟨fun xw hxw σ hσ Θ hΘ => ?_, fun Y _ xw hxw => ?_, fun Y _ xw hxw σ hσ Θ hΘ => ?_,
    fun Y _ xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3 => ?_, fun Y _ xw hxw Θ hΘ => ?_⟩
  · exact raySrc3_sum 𝒴 hEv hsum hωc hΘ hr (fun t ht τ hτ => hxw σ hσ t (hreal t ht) τ hτ)
  · refine rayTerm_analytic hR₁ hω ?_ (hdom0 xw hxw)
    intro u hu
    exact analyticAt_dirL3 (hEv Y u hu) xw.2
  · refine (norm_rayTerm_le (b := 6 * ‖(b Y : ℝ)‖ / r ^ 3) hMω hωb (fun t ht => ?_)).trans
      (le_of_eq (by ring))
    have hz := fun τ (hτ : ‖τ‖ ≤ r) => hxw σ hσ t (hreal t ht) τ hτ
    have := norm_dirL3_le (Ev := Evs Y) (Θ := Θ) (z := (σ * (t : ℂ)) • xw.1) (w := xw.2) (r := r)
      (B := ‖b Y‖) hr (fun τ hτ => hEv Y _ ⟨hΘ, hz τ hτ⟩)
      (fun τ hτ => (hb Y _ ⟨hΘ, hz τ hτ⟩).trans (le_abs_self _))
    exact this
  · unfold rayTerm
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    congr 1
    have hz := fun τ (hτ : ‖τ‖ ≤ r) => hxw σ hσ t (hreal t ht) τ hτ
    have hz' := fun τ (hτ : ‖τ‖ ≤ r) => hxw' σ hσ t (hreal t ht) τ hτ
    rw [dl3_apply, dl3_apply, dirL3_eq hr (fun τ hτ => hEv Y _ ⟨hΘ, hz τ hτ.le⟩),
      dirL3_eq hr (fun τ hτ => hEv Y _ ⟨hΘ', hz' τ hτ.le⟩)]
    refine dirS3_congr ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
    have hτ' : ‖τ‖ ≤ r := (mem_ball_zero_iff.1 hτ).le
    exact hloc Y Θ hΘ Θ' hΘ' _ (hz τ hτ') _ (hz' τ hτ') h1 (by
      simpa using hlin Y xw.1 xw'.1 xw.2 xw'.2 (σ * (t : ℂ)) τ h2 h3)
  · exact rayTerm_zero _ Θ

end Dir3

end Balaban.Fluctuation
