/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovParam
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Analyticity of parameter integrals over a finite measure with compact support

Mathlib has no statement that an integral of functions analytic in a finite-dimensional complex
parameter is analytic.  `Balaban.Localization.analyticAt_intervalIntegral` is the case of an
interval integral (uniform limit of Riemann sums).  This file treats a finite measure `μ` on a
topological space `X` which is carried by a compact set `K`:

* `continuousOn_integral_of_compact`: continuity in a parameter of a compact set;
* `analyticAt_integral_of_continuousOn`: if `G(e, x)` is jointly continuous on `U × K` and analytic
  in `e ∈ U` for every `x ∈ K`, then `e ↦ ∫ G(e, x) dμ(x)` is analytic at every point of which `U`
  is a neighbourhood.  (The Bochner integral of `x ↦ G(·, x)` in the Banach space of continuous
  functions on a closed ball lies in the closed convex set of the functions analytic inside the
  ball: `Convex.average_mem` and the several-variable Weierstrass theorem
  `Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn`.)
* `exists_open_nhds_analyticAt`, `analyticAt_integral_comp`: the form for an integrand
  `Ĝ(Θ, ι x)` with `Ĝ` jointly analytic near `{Θ₀} × ι(K)`;
* `analyticAt_intervalIntegral_div`, `analyticAt_intervalIntegral_avg`,
  `analyticAt_interpAvg_comp`: the interpolation integrals
  `Θ ↦ ∫₀¹ (∫ ∂_t C(Θ, t ι x) e^{A(Θ, ι x) + B(Θ, t ι x)} dμ) / (∫ e^{A + B} dμ) dt` are analytic at
  every `Θ₀` at which the denominators do not vanish on `[0,1]` (they then do not vanish for
  nearby `Θ`, by compactness).

The integrand is assumed continuous in the integration variable on the compact carrier of the
measure (not only measurable); this is the form used for the fluctuation integrals.
-/

@[expose] public section

namespace Balaban.Analysis

open MeasureTheory Metric Set Filter Topology

section Param

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {K : Set X}

/-- Continuity of a parameter integral over a compact carrier `K` of `μ`, for a parameter in a
compact set `A`. -/
theorem continuousOn_integral_of_compact {T : Type*} [TopologicalSpace T]
    [FirstCountableTopology T] {A : Set T} (hA : IsCompact A) (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {G : T → X → ℂ}
    (hG : ContinuousOn (fun q : T × X => G q.1 q.2) (A ×ˢ K)) :
    ContinuousOn (fun t => ∫ x, G t x ∂μ) A := by
  obtain ⟨M, hM⟩ := (hA.prod hK).exists_bound_of_continuousOn hG
  have hν : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem hμ
  refine continuousOn_of_dominated (bound := fun _ => M) (fun t ht => ?_) (fun t ht => ?_)
    (integrable_const M) ?_
  · have : ContinuousOn (G t) K :=
      hG.comp (f := fun x => (t, x)) (by fun_prop) (fun x hx => ⟨ht, hx⟩)
    have h := this.aestronglyMeasurable hKm (μ := μ)
    rwa [hν] at h
  · filter_upwards [hμ] with x hx
    exact hM (t, x) ⟨ht, hx⟩
  · filter_upwards [hμ] with x hx
    exact hG.comp (f := fun t => (t, x)) (by fun_prop) (fun t ht => ⟨ht, hx⟩)

/-- **A parameter integral of analytic functions is analytic** (finite measure carried by a
compact set, finite-dimensional complex parameter): if `G(e, x)` is jointly continuous on `U × K`
and `e ↦ G(e, x)` is analytic on `U` for every `x ∈ K`, then `e ↦ ∫ G(e, x) dμ(x)` is analytic at
every point `e₀` with `U ∈ 𝓝 e₀`. -/
theorem analyticAt_integral_of_continuousOn [FiniteDimensional ℂ E] (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {G : E → X → ℂ} {e0 : E} {U : Set E}
    (hU : U ∈ 𝓝 e0) (hG : ∀ x ∈ K, AnalyticOnNhd ℂ (fun e => G e x) U)
    (hc : ContinuousOn (fun p : E × X => G p.1 p.2) (U ×ˢ K)) :
    AnalyticAt ℂ (fun e => ∫ x, G e x ∂μ) e0 := by
  classical
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hcbU : closedBall e0 ρ ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hbU : ball e0 ρ ⊆ U := ball_subset_closedBall.trans hcbU
  have : CompactSpace (closedBall e0 ρ) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall e0 ρ)
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let g : C(K × closedBall e0 ρ, ℂ) :=
    ⟨fun p => G (p.2 : E) (p.1 : X),
      hc.comp_continuous (f := fun p : K × closedBall e0 ρ => ((p.2 : E), (p.1 : X)))
        (by fun_prop) (fun p => ⟨hcbU p.2.2, p.1.2⟩)⟩
  let Φ : X → C(closedBall e0 ρ, ℂ) := fun x => if h : x ∈ K then g.curry ⟨x, h⟩ else 0
  have hΦK : ∀ (x : X) (_ : x ∈ K) (z : closedBall e0 ρ), Φ x z = G (z : E) x := by
    intro x hx z
    simp only [Φ, hx, dite_true]
    rfl
  have hΦc : ContinuousOn Φ K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : K.domRestrict Φ = fun x : K => g.curry x := by
      funext x
      show (if h : (x : X) ∈ K then g.curry ⟨x, h⟩ else 0) = g.curry x
      simp only [x.2, ↓reduceDIte, Subtype.coe_eta]
    rw [this]
    exact g.curry.continuous
  have hΦi : Integrable Φ μ := by
    have h := hΦc.integrableOn_compact' hK hKm (μ := μ)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  let A : Set C(closedBall e0 ρ, ℂ) := {f | ∃ h : E → ℂ, AnalyticOnNhd ℂ h (ball e0 ρ) ∧
    ∀ z : closedBall e0 ρ, (z : E) ∈ ball e0 ρ → f z = h z}
  have hAsmul : ∀ (c : ℝ) (f : C(closedBall e0 ρ, ℂ)), f ∈ A → c • f ∈ A := by
    rintro c f ⟨h, hh, hfh⟩
    refine ⟨fun e => (c : ℂ) * h e, analyticOnNhd_const.mul hh, fun z hz => ?_⟩
    rw [ContinuousMap.smul_apply, hfh z hz, Complex.real_smul]
  have hAadd : ∀ f₁ f₂ : C(closedBall e0 ρ, ℂ), f₁ ∈ A → f₂ ∈ A → f₁ + f₂ ∈ A := by
    rintro f₁ f₂ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
    exact ⟨fun e => h₁ e + h₂ e, hh₁.add hh₂, fun z hz => by
      rw [ContinuousMap.add_apply, e₁ z hz, e₂ z hz]⟩
  have hAconv : Convex ℝ A := fun f₁ hf₁ f₂ hf₂ a b _ _ _ =>
    hAadd _ _ (hAsmul a f₁ hf₁) (hAsmul b f₂ hf₂)
  have hAclosed : IsClosed A := by
    refine IsSeqClosed.isClosed fun f f' hfA hlim => ?_
    choose h hh hfh using hfA
    obtain ⟨M, hM⟩ : ∃ M, ∀ n, ‖f n‖ ≤ M := by
      obtain ⟨M, hM⟩ := hlim.norm.bddAbove_range
      exact ⟨M, fun n => hM ⟨n, rfl⟩⟩
    let h' : E → ℂ := fun e => if he : e ∈ closedBall e0 ρ then f' ⟨e, he⟩ else 0
    have hunif : TendstoUniformlyOn h h' atTop (ball e0 ρ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
      filter_upwards [eventually_ge_atTop N] with n hn z hz
      have hz' : z ∈ closedBall e0 ρ := ball_subset_closedBall hz
      have h1 : h' z = f' ⟨z, hz'⟩ := by simp only [h', hz', dite_true]
      rw [h1, ← hfh n ⟨z, hz'⟩ hz, dist_comm]
      exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist _) (hN n hn)
    have han := analyticOnNhd_of_tendstoUniformlyOn (M := M) isOpen_ball hh
      (fun n z hz => by
        have hz' : z ∈ closedBall e0 ρ := ball_subset_closedBall hz
        rw [← hfh n ⟨z, hz'⟩ hz]
        exact (ContinuousMap.norm_coe_le_norm (f n) _).trans (hM n)) hunif
    exact ⟨h', han, fun z _ => by simp only [h', z.2, dite_true]⟩
  have h0A : (0 : C(closedBall e0 ρ, ℂ)) ∈ A :=
    ⟨fun _ => 0, analyticOnNhd_const, fun z _ => rfl⟩
  have hmem : (∫ x, Φ x ∂μ) ∈ A := by
    by_cases hμ0 : μ = 0
    · rw [hμ0, integral_zero_measure]
      exact h0A
    · have : NeZero μ := ⟨hμ0⟩
      have h1 := hAconv.average_mem hAclosed (hμ.mono fun x hx =>
        (⟨fun e => G e x, (hG x hx).mono hbU, fun z _ => hΦK x hx z⟩ : Φ x ∈ A)) hΦi
      have hne : μ.real univ ≠ 0 :=
        ENNReal.toReal_ne_zero.2 ⟨by simpa using hμ0, measure_ne_top μ univ⟩
      have h2 : ∫ x, Φ x ∂μ = (μ.real univ) • ⨍ x, Φ x ∂μ := by
        rw [average_eq, smul_smul, mul_inv_cancel₀ hne, one_smul]
      rw [h2]
      exact hAsmul _ _ h1
  obtain ⟨h, hh, hval⟩ := hmem
  refine (hh e0 (mem_ball_self hρ)).congr ?_
  filter_upwards [ball_mem_nhds e0 hρ] with z hz
  have hz' : z ∈ closedBall e0 ρ := ball_subset_closedBall hz
  rw [← hval ⟨z, hz'⟩ hz]
  have hcomm := (ContinuousMap.evalCLM ℂ (⟨z, hz'⟩ : closedBall e0 ρ)).integral_comp_comm hΦi
  have h3 : (∫ x, Φ x ∂μ) ⟨z, hz'⟩ = ∫ x, Φ x ⟨z, hz'⟩ ∂μ := by
    simpa using hcomm.symm
  rw [h3]
  exact integral_congr_ae (hμ.mono fun x hx => hΦK x hx ⟨z, hz'⟩)

end Param

section Joint

variable {P V X : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {K : Set X}

/-- Restriction of a jointly analytic function to a slice `Θ ↦ G(Θ, v)`. -/
theorem analyticAt_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {G : P × V → F}
    {Θ : P} {v : V} (h : AnalyticAt ℂ G (Θ, v)) : AnalyticAt ℂ (fun Θ' : P => G (Θ', v)) Θ :=
  AnalyticAt.comp (f := fun Θ' : P => (Θ', v)) (x := Θ) h (analyticAt_id.prod analyticAt_const)

/-- A function analytic at the points of a compact slice `{Θ₀} × K_c` is analytic at the points of
`u × K_c` for an open neighbourhood `u` of `Θ₀` (tube lemma). -/
theorem exists_open_nhds_analyticAt {G : P × V → ℂ} {Θ₀ : P} {Kc : Set V} (hKc : IsCompact Kc)
    (h : ∀ v ∈ Kc, AnalyticAt ℂ G (Θ₀, v)) :
    ∃ u : Set P, IsOpen u ∧ Θ₀ ∈ u ∧ ∀ Θ ∈ u, ∀ v ∈ Kc, AnalyticAt ℂ G (Θ, v) := by
  obtain ⟨u, v, hu, -, hΘu, hKv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := Θ₀)) hKc
    (isOpen_analyticAt ℂ G) (by
      rintro ⟨Θ, w⟩ ⟨hΘ, hw⟩
      rw [Set.mem_singleton_iff] at hΘ
      subst hΘ
      exact h w hw)
  exact ⟨u, hu, hΘu rfl, fun Θ hΘ w hw => huv ⟨hΘ, hKv hw⟩⟩

/-- **A parameter integral of a jointly analytic integrand is analytic**: for `Ĝ : P × V → ℂ`
analytic at the points `(Θ₀, ι x)`, `x ∈ K`, with `ι` continuous on the compact carrier `K` of `μ`,
`Θ ↦ ∫ Ĝ(Θ, ι x) dμ(x)` is analytic at `Θ₀`. -/
theorem analyticAt_integral_comp [FiniteDimensional ℂ P] (hK : IsCompact K) (hKm : MeasurableSet K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) {ι : X → V} (hι : ContinuousOn ι K) {G : P × V → ℂ} {Θ₀ : P}
    (hG : ∀ x ∈ K, AnalyticAt ℂ G (Θ₀, ι x)) :
    AnalyticAt ℂ (fun Θ => ∫ x, G (Θ, ι x) ∂μ) Θ₀ := by
  obtain ⟨u, hu, hΘu, han⟩ := exists_open_nhds_analyticAt (hK.image_of_continuousOn hι)
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := hv
      exact hG x hx)
  refine analyticAt_integral_of_continuousOn hK hKm hμ (hu.mem_nhds hΘu)
    (fun x hx Θ hΘ => ?_) (fun p hp => ?_)
  · exact analyticAt_slice (han Θ hΘ (ι x) ⟨x, hx, rfl⟩)
  · have h1 : ContinuousAt G (p.1, ι p.2) := (han p.1 hp.1 (ι p.2) ⟨p.2, hp.2, rfl⟩).continuousAt
    have h2 : ContinuousWithinAt (fun p : P × X => (p.1, ι p.2)) (u ×ˢ K) p :=
      continuousWithinAt_fst.prodMk
        ((hι p.2 hp.2).comp continuousWithinAt_snd (fun q hq => hq.2))
    exact ContinuousAt.comp_continuousWithinAt (f := fun p : P × X => (p.1, ι p.2)) h1 h2

/-- **An interval integral of quotients of analytic functions**: if `N(Θ, t)`, `Z(Θ, t)` are
analytic in `Θ` on a ball around `Θ₀` for `t ∈ [0,1]`, jointly continuous on the closed ball times
`[0,1]`, and `Z(Θ₀, t) ≠ 0` on `[0,1]`, then `Θ ↦ ∫₀¹ N(Θ, t)/Z(Θ, t) dt` is analytic at `Θ₀`. -/
theorem analyticAt_intervalIntegral_div [FiniteDimensional ℂ P] {N Z : P → ℝ → ℂ} {Θ₀ : P} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hN : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun Θ => N Θ t) (ball Θ₀ ρ))
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun Θ => Z Θ t) (ball Θ₀ ρ))
    (hNc : ContinuousOn (fun q : P × ℝ => N q.1 q.2) (closedBall Θ₀ ρ ×ˢ Icc (0 : ℝ) 1))
    (hZc : ContinuousOn (fun q : P × ℝ => Z q.1 q.2) (closedBall Θ₀ ρ ×ˢ Icc (0 : ℝ) 1))
    (hZ0 : ∀ t ∈ Icc (0 : ℝ) 1, Z Θ₀ t ≠ 0) :
    AnalyticAt ℂ (fun Θ => ∫ t in (0 : ℝ)..1, N Θ t / Z Θ t) Θ₀ := by
  have : ProperSpace P := FiniteDimensional.proper_rclike ℂ P
  have hT : IsCompact (closedBall Θ₀ ρ ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hΘ₀ : Θ₀ ∈ closedBall Θ₀ ρ := mem_closedBall_self hρ.le
  obtain ⟨MN, hMN⟩ := hT.exists_bound_of_continuousOn hNc
  have hMN0 : 0 ≤ MN := (norm_nonneg _).trans (hMN (Θ₀, 0) ⟨hΘ₀, left_mem_Icc.2 zero_le_one⟩)
  -- a lower bound for `Z(Θ₀, ·)`
  have hZ0c : ContinuousOn (fun t => ‖Z Θ₀ t‖) (Icc (0 : ℝ) 1) :=
    (hZc.comp (f := fun t => (Θ₀, t)) (by fun_prop) (fun t ht => ⟨hΘ₀, ht⟩)).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hZ0c
  set c₀ : ℝ := ‖Z Θ₀ t₀‖ with hc₀
  have hc₀pos : 0 < c₀ := norm_pos_iff.2 (hZ0 t₀ ht₀)
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, c₀ ≤ ‖Z Θ₀ t‖ := fun t ht => hmin ht
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (hT.uniformContinuousOn_of_continuous hZc) (c₀ / 2) (by positivity)
  set R : ℝ := min δ ρ / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRδ : 2 * R ≤ δ := by rw [hRdef]; linarith [min_le_left δ ρ]
  have hRρ : 2 * R ≤ ρ := by rw [hRdef]; linarith [min_le_right δ ρ]
  have hsub : ball Θ₀ (2 * R) ⊆ ball Θ₀ ρ := ball_subset_ball hRρ
  have hZlow : ∀ t ∈ Icc (0 : ℝ) 1, ∀ Θ ∈ ball Θ₀ (2 * R), c₀ / 2 ≤ ‖Z Θ t‖ := by
    intro t ht Θ hΘ
    have hΘc : Θ ∈ closedBall Θ₀ ρ := ball_subset_closedBall (hsub hΘ)
    have hd : dist ((Θ, t) : P × ℝ) (Θ₀, t) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact lt_of_lt_of_le (mem_ball.1 hΘ) hRδ
    have h1 := hδ' (Θ, t) ⟨hΘc, ht⟩ (Θ₀, t) ⟨hΘ₀, ht⟩ hd
    rw [dist_eq_norm] at h1
    have h2 := hlow t ht
    have h3 : ‖Z Θ₀ t‖ ≤ ‖Z Θ t‖ + ‖Z Θ t - Z Θ₀ t‖ := by
      have := norm_sub_le (Z Θ t) (Z Θ t - Z Θ₀ t)
      simpa using this
    linarith
  have hZne : ∀ t ∈ Icc (0 : ℝ) 1, ∀ Θ ∈ ball Θ₀ (2 * R), Z Θ t ≠ 0 := fun t ht Θ hΘ =>
    norm_pos_iff.1 (lt_of_lt_of_le (by positivity) (hZlow t ht Θ hΘ))
  refine Balaban.Localization.analyticAt_intervalIntegral (G := fun t Θ => N Θ t / Z Θ t)
    (M := MN / (c₀ / 2)) hR (by positivity) zero_le_one (fun t ht => ?_) (fun t ht Θ hΘ => ?_)
    (fun Θ hΘ => ?_)
  · exact ((hN t ht).mono hsub).div ((hZ t ht).mono hsub) (hZne t ht)
  · have hΘc : Θ ∈ closedBall Θ₀ ρ := ball_subset_closedBall (hsub hΘ)
    rw [norm_div]
    exact div_le_div₀ hMN0 (hMN (Θ, t) ⟨hΘc, ht⟩) (by positivity) (hZlow t ht Θ hΘ)
  · have hΘc : Θ ∈ closedBall Θ₀ ρ := ball_subset_closedBall (hsub hΘ)
    exact (hNc.comp (f := fun t => (Θ, t)) (by fun_prop) (fun t ht => ⟨hΘc, ht⟩)).div
      (hZc.comp (f := fun t => (Θ, t)) (by fun_prop) (fun t ht => ⟨hΘc, ht⟩))
      (fun t ht => hZne t ht Θ hΘ)

/-- **Interpolation averages are analytic in a parameter**: for integrands `N_f(Θ, t, x)`,
`Z_f(Θ, t, x)` analytic in `Θ` on an open set `u`, jointly continuous on `u × [0,1] × K`, with
`∫ Z_f(Θ₀, t, ·) dμ ≠ 0` on `[0,1]`, the function
`Θ ↦ ∫₀¹ (∫ N_f(Θ, t, x) dμ) / (∫ Z_f(Θ, t, x) dμ) dt` is analytic at `Θ₀ ∈ u`. -/
theorem analyticAt_intervalIntegral_avg [FiniteDimensional ℂ P] (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {Nf Zf : P → ℝ → X → ℂ} {Θ₀ : P} {u : Set P}
    (hu : IsOpen u) (hΘ₀ : Θ₀ ∈ u)
    (hNa : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticOnNhd ℂ (fun Θ => Nf Θ t x) u)
    (hZa : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticOnNhd ℂ (fun Θ => Zf Θ t x) u)
    (hNc : ContinuousOn (fun q : (P × ℝ) × X => Nf q.1.1 q.1.2 q.2) ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K))
    (hZc : ContinuousOn (fun q : (P × ℝ) × X => Zf q.1.1 q.1.2 q.2) ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K))
    (hZ0 : ∀ t ∈ Icc (0 : ℝ) 1, ∫ x, Zf Θ₀ t x ∂μ ≠ 0) :
    AnalyticAt ℂ (fun Θ => ∫ t in (0 : ℝ)..1,
      (∫ x, Nf Θ t x ∂μ) / (∫ x, Zf Θ t x ∂μ)) Θ₀ := by
  have : ProperSpace P := FiniteDimensional.proper_rclike ℂ P
  obtain ⟨r, hr, hru⟩ := Metric.isOpen_iff.1 hu Θ₀ hΘ₀
  set ρ : ℝ := r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hcb : closedBall Θ₀ ρ ⊆ u := (closedBall_subset_ball (by linarith)).trans hru
  have hT : IsCompact (closedBall Θ₀ ρ ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hsubT : (closedBall Θ₀ ρ ×ˢ Icc (0 : ℝ) 1) ×ˢ K ⊆ (u ×ˢ Icc (0 : ℝ) 1) ×ˢ K :=
    Set.prod_mono (Set.prod_mono hcb subset_rfl) subset_rfl
  have key : ∀ {F : P → ℝ → X → ℂ},
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticOnNhd ℂ (fun Θ => F Θ t x) u) →
      ContinuousOn (fun q : (P × ℝ) × X => F q.1.1 q.1.2 q.2) ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) →
      (∀ t ∈ Icc (0 : ℝ) 1, AnalyticOnNhd ℂ (fun Θ => ∫ x, F Θ t x ∂μ) (ball Θ₀ ρ)) ∧
      ContinuousOn (fun q : P × ℝ => ∫ x, F q.1 q.2 x ∂μ) (closedBall Θ₀ ρ ×ˢ Icc (0 : ℝ) 1) := by
    intro F hFa hFc
    refine ⟨fun t ht Θ hΘ => ?_, ?_⟩
    · have hΘu : Θ ∈ u := hcb (ball_subset_closedBall hΘ)
      refine analyticAt_integral_of_continuousOn hK hKm hμ (hu.mem_nhds hΘu) (hFa t ht) ?_
      exact hFc.comp (f := fun p : P × X => ((p.1, t), p.2)) (by fun_prop)
        (fun p hp => ⟨⟨hp.1, ht⟩, hp.2⟩)
    · exact continuousOn_integral_of_compact (G := fun q : P × ℝ => F q.1 q.2) hT hK hKm hμ
        (hFc.mono hsubT)
  obtain ⟨hN1, hN2⟩ := key hNa hNc
  obtain ⟨hZ1, hZ2⟩ := key hZa hZc
  exact analyticAt_intervalIntegral_div hρ hN1 hZ1 hN2 hZ2 hZ0

/-- **The interpolation average of a jointly analytic exponent is analytic in the parameter**:
for `A, B, C : P × V → ℂ` analytic at the points `(Θ₀, ι x)` (for `A`) and `(Θ₀, t ι x)`,
`t ∈ [0,1]` (for `B`, `C`), `x` in the compact carrier `K` of `μ`, and partition functions
`∫ e^{A(Θ₀, ι x) + B(Θ₀, t ι x)} dμ ≠ 0` on `[0,1]`, the function
`Θ ↦ ∫₀¹ (∫ ∂_t C(Θ, t ι x) e^{A(Θ, ι x) + B(Θ, t ι x)} dμ) / (∫ e^{A(Θ, ι x) + B(Θ, t ι x)} dμ) dt`
is analytic at `Θ₀`. -/
theorem analyticAt_interpAvg_comp [FiniteDimensional ℂ P] (hK : IsCompact K) (hKm : MeasurableSet K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) {ι : X → V} (hι : ContinuousOn ι K) {A B Cm : P × V → ℂ} {Θ₀ : P}
    (hA : ∀ x ∈ K, AnalyticAt ℂ A (Θ₀, ι x))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticAt ℂ B (Θ₀, (t : ℂ) • ι x))
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticAt ℂ Cm (Θ₀, (t : ℂ) • ι x))
    (hZ0 : ∀ t ∈ Icc (0 : ℝ) 1,
      ∫ x, Complex.exp (A (Θ₀, ι x) + B (Θ₀, (t : ℂ) • ι x)) ∂μ ≠ 0) :
    AnalyticAt ℂ (fun Θ => ∫ t in (0 : ℝ)..1,
      (∫ x, deriv (fun r : ℝ => Cm (Θ, (r : ℂ) • ι x)) t *
        Complex.exp (A (Θ, ι x) + B (Θ, (t : ℂ) • ι x)) ∂μ) /
      (∫ x, Complex.exp (A (Θ, ι x) + B (Θ, (t : ℂ) • ι x)) ∂μ)) Θ₀ := by
  -- the compact set of the hat variables of the path
  set Kc : Set V := (fun p : ℝ × X => (p.1 : ℂ) • ι p.2) '' (Icc (0 : ℝ) 1 ×ˢ K) with hKc
  have hKcc : IsCompact Kc := by
    refine (isCompact_Icc.prod hK).image_of_continuousOn ?_
    exact (Complex.continuous_ofReal.comp continuous_fst).continuousOn.smul
      (hι.comp continuousOn_snd (fun p hp => hp.2))
  have hmemKc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, (t : ℂ) • ι x ∈ Kc := fun t ht x hx =>
    ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  obtain ⟨uA, huA, hΘA, hanA⟩ := exists_open_nhds_analyticAt (hK.image_of_continuousOn hι)
    (fun v hv => by
      obtain ⟨x, hx, rfl⟩ := hv
      exact hA x hx)
  obtain ⟨uB, huB, hΘB, hanB⟩ := exists_open_nhds_analyticAt hKcc (fun v hv => by
      obtain ⟨p, hp, rfl⟩ := hv
      exact hB p.1 hp.1 p.2 hp.2)
  obtain ⟨uC, huC, hΘC, hanC⟩ := exists_open_nhds_analyticAt hKcc (fun v hv => by
      obtain ⟨p, hp, rfl⟩ := hv
      exact hC p.1 hp.1 p.2 hp.2)
  set u : Set P := uA ∩ uB ∩ uC with hu
  have huo : IsOpen u := (huA.inter huB).inter huC
  have hΘu : Θ₀ ∈ u := ⟨⟨hΘA, hΘB⟩, hΘC⟩
  have hanA' : ∀ Θ ∈ u, ∀ x ∈ K, AnalyticAt ℂ A (Θ, ι x) := fun Θ hΘ x hx =>
    hanA Θ hΘ.1.1 _ ⟨x, hx, rfl⟩
  have hanB' : ∀ Θ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticAt ℂ B (Θ, (t : ℂ) • ι x) :=
    fun Θ hΘ t ht x hx => hanB Θ hΘ.1.2 _ (hmemKc t ht x hx)
  have hanC' : ∀ Θ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticAt ℂ Cm (Θ, (t : ℂ) • ι x) :=
    fun Θ hΘ t ht x hx => hanC Θ hΘ.2 _ (hmemKc t ht x hx)
  -- the derivative along the ray
  have hderiv : ∀ Θ ∈ u, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      deriv (fun r : ℝ => Cm (Θ, (r : ℂ) • ι x)) t =
        fderiv ℂ Cm (Θ, (t : ℂ) • ι x) (0, ι x) := by
    intro Θ hΘ t ht x hx
    have h1 : HasDerivAt (fun τ : ℂ => ((Θ, τ • ι x) : P × V)) ((0 : P), ι x) (t : ℂ) := by
      have := (hasDerivAt_const (t : ℂ) Θ).prodMk ((hasDerivAt_id (t : ℂ)).smul_const (ι x))
      rw [one_smul] at this
      exact this
    have h2 := ((hanC' Θ hΘ t ht x hx).differentiableAt.hasFDerivAt.comp_hasDerivAt (t : ℂ)
      h1).comp_ofReal
    exact h2.deriv
  -- the two integrands
  set Zf : P → ℝ → X → ℂ := fun Θ t x =>
    Complex.exp (A (Θ, ι x) + B (Θ, (t : ℂ) • ι x)) with hZf
  set Nf : P → ℝ → X → ℂ := fun Θ t x =>
    fderiv ℂ Cm (Θ, (t : ℂ) • ι x) (0, ι x) * Zf Θ t x with hNf
  have hmapA : ∀ q ∈ (u ×ˢ Icc (0 : ℝ) 1) ×ˢ K, ContinuousWithinAt
      (fun q : (P × ℝ) × X => ((q.1.1, ι q.2) : P × V)) ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) q :=
    fun q hq => (continuous_fst.fst.continuousWithinAt).prodMk
      ((hι q.2 hq.2).comp continuousWithinAt_snd (fun q hq => hq.2))
  have hmapB : ∀ q ∈ (u ×ˢ Icc (0 : ℝ) 1) ×ˢ K, ContinuousWithinAt
      (fun q : (P × ℝ) × X => ((q.1.1, (q.1.2 : ℂ) • ι q.2) : P × V))
      ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) q :=
    fun q hq => (continuous_fst.fst.continuousWithinAt).prodMk
      ((Complex.continuous_ofReal.comp continuous_fst.snd).continuousWithinAt.smul
        ((hι q.2 hq.2).comp continuousWithinAt_snd (fun q hq => hq.2)))
  have hZc : ContinuousOn (fun q : (P × ℝ) × X => Zf q.1.1 q.1.2 q.2)
      ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) := by
    intro q hq
    have h1 := ContinuousAt.comp_continuousWithinAt
      (f := fun q : (P × ℝ) × X => ((q.1.1, ι q.2) : P × V))
      (hanA' q.1.1 hq.1.1 q.2 hq.2).continuousAt (hmapA q hq)
    have h2 := ContinuousAt.comp_continuousWithinAt
      (f := fun q : (P × ℝ) × X => ((q.1.1, (q.1.2 : ℂ) • ι q.2) : P × V))
      (hanB' q.1.1 hq.1.1 q.1.2 hq.1.2 q.2 hq.2).continuousAt (hmapB q hq)
    exact (h1.add h2).cexp
  have hNc : ContinuousOn (fun q : (P × ℝ) × X => Nf q.1.1 q.1.2 q.2)
      ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) := by
    intro q hq
    have h1 : ContinuousWithinAt
        (fun q : (P × ℝ) × X => fderiv ℂ Cm (q.1.1, (q.1.2 : ℂ) • ι q.2))
        ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) q :=
      ContinuousAt.comp_continuousWithinAt
        (f := fun q : (P × ℝ) × X => ((q.1.1, (q.1.2 : ℂ) • ι q.2) : P × V))
        (hanC' q.1.1 hq.1.1 q.1.2 hq.1.2 q.2 hq.2).fderiv.continuousAt (hmapB q hq)
    have h2 : ContinuousWithinAt (fun q : (P × ℝ) × X => ((0 : P), ι q.2))
        ((u ×ˢ Icc (0 : ℝ) 1) ×ˢ K) q :=
      continuousWithinAt_const.prodMk
        ((hι q.2 hq.2).comp continuousWithinAt_snd (fun q hq => hq.2))
    exact (h1.clm_apply h2).mul (hZc q hq)
  have hZa : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticOnNhd ℂ (fun Θ => Zf Θ t x) u := by
    intro t ht x hx Θ hΘ
    have h1 : AnalyticAt ℂ (fun Θ : P => A (Θ, ι x)) Θ := analyticAt_slice (hanA' Θ hΘ x hx)
    have h2 : AnalyticAt ℂ (fun Θ : P => B (Θ, (t : ℂ) • ι x)) Θ :=
      analyticAt_slice (hanB' Θ hΘ t ht x hx)
    exact (h1.add h2).cexp
  have hNa : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, AnalyticOnNhd ℂ (fun Θ => Nf Θ t x) u := by
    intro t ht x hx Θ hΘ
    have h1 : AnalyticAt ℂ (fun Θ : P => fderiv ℂ Cm (Θ, (t : ℂ) • ι x)) Θ :=
      analyticAt_slice (hanC' Θ hΘ t ht x hx).fderiv
    have h2 : AnalyticAt ℂ (fun Θ : P => fderiv ℂ Cm (Θ, (t : ℂ) • ι x) (0, ι x)) Θ :=
      ((ContinuousLinearMap.apply ℂ ℂ ((0 : P), ι x)).analyticAt _).comp h1
    exact h2.mul (hZa t ht x hx Θ hΘ)
  have hmain := analyticAt_intervalIntegral_avg hK hKm hμ huo hΘu hNa hZa hNc hZc hZ0
  refine hmain.congr ?_
  filter_upwards [huo.mem_nhds hΘu] with Θ hΘ
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  show (∫ x, Nf Θ t x ∂μ) / (∫ x, Zf Θ t x ∂μ) = _
  congr 1
  refine integral_congr_ae (hμ.mono fun x hx => ?_)
  show Nf Θ t x = deriv (fun r : ℝ => Cm (Θ, (r : ℂ) • ι x)) t *
    Complex.exp (A (Θ, ι x) + B (Θ, (t : ℂ) • ι x))
  rw [hderiv Θ hΘ t ht x hx]

end Joint

end Balaban.Analysis
