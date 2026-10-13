/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MarkedHolo
public import Balaban.Polymer.MayerHolomorphic
public import Balaban.Analysis.ParamIntegralAnalytic
public import Balaban.Analysis.Cauchy

/-!
# Holomorphy of the marked local terms in a finite-dimensional parameter

`Balaban.Polymer.holo_of_KP` proves, for activities `K u Z l` depending on ONE complex parameter
`u ∈ U ⊆ ℂ` and on the marks `l ∈ polydisc 0 r`, that `u ↦ PY (K u · 0) Y` and
`u ↦ D1 i (Ff (K u) Y)` are holomorphic, under a Kotecký–Preiss majorant `κ` for `‖K u Z l‖`
uniform in `u` and `l`.

## Survey (where one-dimensionality was used)

* The first part uses `pe_PY_analyticOnNhd`, which is already stated for an arbitrary complex
  normed space of parameters.  Nothing is one-dimensional there.
* The second part (derivative in the mark at `l = 0`) writes `D1 i` as a Cauchy integral over a
  circle in the mark variable and differentiates under the integral sign with
  `differentiableOn_integral_of_bound`, which is a theorem about a parameter in `ℂ`.  This is the
  only place where the parameter is one-dimensional.

So the minimal change replaces that step by `analyticAt_integral_of_continuousOn`
(finite-dimensional parameter space).  That lemma needs joint continuity of the integrand in
(parameter, circle angle); it is obtained here from analyticity in the parameter, a uniform bound
and continuity in the angle (`continuousOn_prod_of_analytic_bdd`), by the Cauchy estimate in the
parameter.  The hypotheses of `holo_of_KP_param` are those of `holo_of_KP` with `ℂ` replaced by a
finite-dimensional complex normed space `E` and "differentiable" by "analytic".  For `E = ℂ` it
gives back `holo_of_KP` (`holo_of_KP_param_complex`).

## Scope

Only the analysis of the expansion objects is treated.  Producing a parameter family from the
physical step (the actual activities and marks, and the determinant term) is not done here.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory Metric Balaban.Analysis Filter Topology

namespace Balaban.Polymer

section Continuity

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace X]

/-- **Joint continuity from separate regularity.**  If `G(·, x)` is analytic on an open set `V`
for each `x` of `Kc`, `G(e, ·)` is continuous on `Kc` for each `e ∈ V`, and `‖G‖ ≤ M` on
`V × Kc`, then `G` is jointly continuous on `V × Kc`.  (Cauchy estimate in the parameter gives
a Lipschitz bound uniform in `x`.) -/
theorem continuousOn_prod_of_analytic_bdd {V : Set E} (hV : IsOpen V) {Kc : Set X}
    {G : E → X → ℂ} {M : ℝ}
    (hG : ∀ x ∈ Kc, AnalyticOnNhd ℂ (fun e => G e x) V)
    (hx : ∀ e ∈ V, ContinuousOn (G e) Kc) (hb : ∀ e ∈ V, ∀ x ∈ Kc, ‖G e x‖ ≤ M) :
    ContinuousOn (fun p : E × X => G p.1 p.2) (V ×ˢ Kc) := by
  rintro ⟨e0, x0⟩ ⟨he0, hx0⟩
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.1 hV e0 he0
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb e0 he0 x0 hx0)
  have hlip : ∀ e, dist e e0 < R / 2 → ∀ x ∈ Kc, ‖G e x - G e0 x‖ ≤ 2 * M / R * dist e e0 := by
    intro e he x hxK
    have hmem : e ∈ ball e0 R := by rw [mem_ball]; linarith
    have h := norm_sub_le_of_ball (z₀ := e0) (R := R) (M := M)
      ((hG x hxK).differentiableOn.mono hRV) (fun z hz => hb z (hRV hz) x hxK) hmem
    refine h.trans ?_
    set t := dist e e0
    have ht : 0 ≤ t := dist_nonneg
    have : R / 2 ≤ R - t := by linarith
    rw [div_le_iff₀ (by linarith)]
    calc M * t ≤ 2 * M / R * t * (R / 2) := by field_simp; linarith
      _ ≤ 2 * M / R * t * (R - t) := by gcongr
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set δ : ℝ := min (R / 2) (ε * R / (4 * M + 4)) with hδ
  have hδpos : 0 < δ := by
    refine lt_min (by positivity) (by positivity)
  have h1 : ∀ᶠ p in 𝓝[V ×ˢ Kc] (e0, x0), dist p.1 e0 < δ :=
    Metric.tendsto_nhds.1 ((continuous_fst.tendsto (e0, x0)).mono_left nhdsWithin_le_nhds) δ
      hδpos
  have h2 : ∀ᶠ p in 𝓝[V ×ˢ Kc] (e0, x0), p ∈ V ×ˢ Kc := self_mem_nhdsWithin
  have h3 : ∀ᶠ p in 𝓝[V ×ˢ Kc] (e0, x0), dist (G e0 p.2) (G e0 x0) < ε / 2 := by
    have hc : ContinuousWithinAt (fun p : E × X => G e0 p.2) (V ×ˢ Kc) (e0, x0) :=
      ((hx e0 he0) x0 hx0).comp continuousWithinAt_snd (fun p hp => hp.2)
    exact Metric.tendsto_nhds.1 hc (ε / 2) (by positivity)
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3
  have hl := hlip p.1 (lt_of_lt_of_le hp1 (min_le_left _ _)) p.2 hp2.2
  have hq : 2 * M / R * dist p.1 e0 < ε / 2 := by
    have hd : dist p.1 e0 < ε * R / (4 * M + 4) := lt_of_lt_of_le hp1 (min_le_right _ _)
    calc 2 * M / R * dist p.1 e0 ≤ 2 * M / R * (ε * R / (4 * M + 4)) := by gcongr
      _ < ε / 2 := by
        rw [show 2 * M / R * (ε * R / (4 * M + 4)) = ε * (2 * M / (4 * M + 4)) by
          field_simp]
        have : 2 * M / (4 * M + 4) < 1 / 2 := by
          rw [div_lt_iff₀ (by linarith)]; linarith
        nlinarith
  rw [dist_eq_norm] at hp3 ⊢
  calc ‖G p.1 p.2 - G e0 x0‖ = ‖(G p.1 p.2 - G e0 p.2) + (G e0 p.2 - G e0 x0)‖ := by ring_nf
    _ ≤ ‖G p.1 p.2 - G e0 p.2‖ + ‖G e0 p.2 - G e0 x0‖ := norm_add_le _ _
    _ < ε := by linarith

end Continuity

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Several-parameter form of `differentiableOn_deriv_zero`: if `(u, l) ↦ f u l` is analytic in
`u ∈ V` for each `l`, analytic in `l` on the disc of radius `r` for each `u`, and bounded, then
`u ↦ ∂_l f u 0` is analytic on `V`. -/
theorem analyticOnNhd_deriv_zero {V : Set E} (hV : IsOpen V) {f : E → ℂ → ℂ} {r M : ℝ}
    (hr : 0 < r) (hdu : ∀ l : ℂ, ‖l‖ < r → AnalyticOnNhd ℂ (fun u => f u l) V)
    (hdl : ∀ u ∈ V, DifferentiableOn ℂ (f u) (ball 0 r))
    (hbd : ∀ u ∈ V, ∀ l : ℂ, ‖l‖ < r → ‖f u l‖ ≤ M) :
    AnalyticOnNhd ℂ (fun u => deriv (f u) 0) V := by
  set R : ℝ := r / 2 with hRdef
  have hR : 0 < R := by positivity
  have hRr : R < r := by rw [hRdef]; linarith
  have hnorm : ∀ θ : ℝ, ‖circleMap 0 R θ‖ = R := fun θ => by
    simp [norm_circleMap_zero, abs_of_pos hR]
  set F : E → ℝ → ℂ := fun u θ =>
    (circleMap 0 R θ * Complex.I) • (((circleMap 0 R θ - 0) ^ 2)⁻¹ • f u (circleMap 0 R θ)) with hF
  have hcirc : ∀ u ∈ V, deriv (f u) 0 =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∫ θ in Set.Ioc 0 (2 * Real.pi), F u θ := by
    intro u hu
    have h := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      (isOpen_ball (x := (0 : ℂ)) (ε := r)) (c := 0) (w₀ := 0) (R := R)
      (closedBall_subset_ball hRr) (hdl u hu) (mem_ball_self hR)
    rw [← h]
    congr 1
    unfold circleIntegral
    rw [intervalIntegral.integral_of_le (by positivity)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
    simp only [deriv_circleMap, hF]
  have hcont : ∀ u ∈ V, Continuous (fun θ : ℝ => f u (circleMap 0 R θ)) := by
    intro u hu
    have h1 : ContinuousOn (f u) (ball 0 r) := (hdl u hu).continuousOn
    exact h1.comp_continuous (continuous_circleMap 0 R) (fun θ => by simp [hnorm θ, hRr])
  have hFc : ∀ u ∈ V, Continuous (F u) := by
    intro u hu
    simp only [hF]
    have hs : Continuous (fun θ : ℝ => ((circleMap 0 R θ - 0) ^ 2)⁻¹) :=
      Continuous.inv₀ (((continuous_circleMap 0 R).sub continuous_const).pow 2) (fun θ => by
        simp [hR.ne'])
    exact ((continuous_circleMap 0 R).mul continuous_const).smul (hs.smul (hcont u hu))
  have hdiff : ∀ θ, AnalyticOnNhd ℂ (fun u => F u θ) V := by
    intro θ
    have h1 : AnalyticOnNhd ℂ (fun u => f u (circleMap 0 R θ)) V :=
      hdu (circleMap 0 R θ) (by simp [hnorm θ, hRr])
    simp only [hF, smul_eq_mul]
    exact analyticOnNhd_const.mul (analyticOnNhd_const.mul h1)
  have hbd' : ∀ u ∈ V, ∀ θ, ‖F u θ‖ ≤ M / R := by
    intro u hu θ
    simp only [hF, norm_smul, norm_mul, Complex.norm_I, mul_one, hnorm θ, sub_zero, norm_inv,
      norm_pow]
    have h2 := hbd u hu (circleMap 0 R θ) (by simp [hnorm θ, hRr])
    calc R * ((R ^ 2)⁻¹ * ‖f u (circleMap 0 R θ)‖) ≤ R * ((R ^ 2)⁻¹ * M) := by gcongr
      _ = M / R := by field_simp
  have hcjoint : ContinuousOn (fun p : E × ℝ => F p.1 p.2) (V ×ˢ Set.Icc 0 (2 * Real.pi)) :=
    continuousOn_prod_of_analytic_bdd hV (fun θ _ => hdiff θ)
      (fun u hu => (hFc u hu).continuousOn) (fun u hu θ _ => hbd' u hu θ)
  have : IsFiniteMeasure (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  intro u hu
  have hint : AnalyticAt ℂ
      (fun u => ∫ θ, F u θ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) u :=
    analyticAt_integral_of_continuousOn (isCompact_Icc) measurableSet_Icc
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => Set.Ioc_subset_Icc_self hx))
      (hV.mem_nhds hu) (fun θ _ => hdiff θ) hcjoint
  refine (hint.const_smul (c := (2 * Real.pi * Complex.I : ℂ)⁻¹)).congr ?_
  exact Filter.eventuallyEq_of_mem (hV.mem_nhds hu) (fun u hu => (hcirc u hu).symm)

end Deriv

section Mayer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  [∀ b, TopologicalSpace (Ω b)] [∀ b, OpensMeasurableSpace (Ω b)]
  [∀ b, SecondCountableTopology (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {T : Type*} [Fintype T] (sup : T → Finset B)

/-- **Analyticity of the Mayer activities in a finite-dimensional parameter** (several-parameter
form of `differentiableOn_mayerK`): if the potentials `H e t Φ` are analytic in `e ∈ V` for every
configuration `Φ` of a compact set `Kc` carrying the measure, and jointly continuous on
`V × Kc`, then `e ↦ mayerK μ sup (H e) Y` is analytic on `V`. -/
theorem analyticOnNhd_mayerK_param {V : Set E} (hV : IsOpen V) {Kc : Set (∀ b, Ω b)}
    (hK : IsCompact Kc) (hKm : MeasurableSet Kc) (hμ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Kc)
    {H : E → T → (∀ b, Ω b) → ℂ}
    (hanal : ∀ t, ∀ Φ ∈ Kc, AnalyticOnNhd ℂ (fun e => H e t Φ) V)
    (hcont : ∀ t, ContinuousOn (fun p : E × (∀ b, Ω b) => H p.1 t p.2) (V ×ˢ Kc))
    (Y : NePoly B) : AnalyticOnNhd ℂ (fun e => mayerK μ sup (H e) Y) V := by
  intro e0 he0
  unfold mayerK
  refine analyticAt_integral_of_continuousOn hK hKm hμ (hV.mem_nhds he0)
    (G := fun e Φ => mayerAct sup (H e) Y Φ) (fun Φ hΦ => ?_) ?_
  · unfold mayerAct polyAct
    refine Finset.analyticOnNhd_fun_sum _ (fun C _ => Finset.analyticOnNhd_fun_prod _
      (fun t _ => ?_))
    exact (AnalyticOnNhd.cexp (hanal t Φ hΦ)).sub analyticOnNhd_const
  · unfold mayerAct polyAct
    refine continuousOn_finsetSum _ (fun C _ => continuousOn_finsetProd _ (fun t _ => ?_))
    exact (Complex.continuous_exp.comp_continuousOn (hcont t)).sub continuousOn_const

end Mayer

section Parameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {P : Type*} [Fintype P] (inc : P → P → Prop) {B : Type*} (supp : P → Finset B)
  {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℝ} {κ a : P → ℝ}

/-- **Analyticity in a finite-dimensional parameter** of `P(Y)` and of `∂_i P(Y)` at `l = 0`
(several-parameter form of `holo_of_KP`): the activities `K u Z l` are analytic in the parameter
`u ∈ V` for each fixed mark `l`, analytic in the marks for each `u`, and obey a Kotecký–Preiss
majorant `κ` uniform in `u ∈ V` and `l`. -/
theorem holo_of_KP_param [FiniteDimensional ℂ E] (h : KPCond inc κ a) (hr : ∀ i, 0 < r i)
    {V : Set E} (hV : IsOpen V) (K : E → P → (ι → ℂ) → ℂ)
    (hKl : ∀ u ∈ V, ∀ Z, AnalyticOnNhd ℂ (K u Z) (polydisc 0 r))
    (hKu : ∀ Z, ∀ l ∈ polydisc (0 : ι → ℂ) r, AnalyticOnNhd ℂ (fun u => K u Z l) V)
    (hb : ∀ u ∈ V, ∀ Z, ∀ l ∈ polydisc (0 : ι → ℂ) r, ‖K u Z l‖ ≤ κ Z) (Y : Finset B) :
    AnalyticOnNhd ℂ (fun u => PY inc supp (fun Z => K u Z 0) Y) V ∧
      ∀ i, AnalyticOnNhd ℂ (fun u => D1 i (Ff inc supp (K u) Y)) V := by
  have h0 : (0 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r := fun k => by simpa using hr k
  have hPu : ∀ l ∈ polydisc (0 : ι → ℂ) r,
      AnalyticOnNhd ℂ (fun u => PY inc supp (fun Z => K u Z l) Y) V := fun l hl =>
    pe_PY_analyticOnNhd inc supp h hV (fun Z u => K u Z l) (fun Z => hKu Z l hl)
      (fun Z u hu => hb u hu Z l hl) Y
  refine ⟨hPu 0 h0, fun i => ?_⟩
  set M : ℝ := ∑' n, sp inc κ (fun _ => True) n with hM
  have key := analyticOnNhd_deriv_zero hV (hr i)
    (f := fun u l => Ff inc supp (K u) Y (l • (Pi.single i 1 : ι → ℂ))) (M := M)
    (fun l hl => hPu _ (mem_polydisc_line hr i hl))
    (fun u hu => by
      intro l hl
      have hmem : l • (Pi.single i 1 : ι → ℂ) ∈ polydisc (0 : ι → ℂ) r :=
        mem_polydisc_line hr i (by simpa using hl)
      have hF := (analyticOnNhd_Ff inc supp h (hKl u hu) (fun Z l hl => hb u hu Z l hl) Y _ hmem)
      have hlin : DifferentiableAt ℂ (fun t : ℂ => t • (Pi.single i 1 : ι → ℂ)) l :=
        (differentiableAt_id.smul_const _)
      exact (hF.differentiableAt.comp l hlin).differentiableWithinAt)
    (fun u hu l hl => norm_PY_le inc supp h _ (fun Z => hb u hu Z _
      (mem_polydisc_line hr i hl)) Y)
  intro u hu
  refine (key u hu).congr ?_
  refine Filter.eventuallyEq_of_mem (hV.mem_nhds hu) (fun u hu => ?_)
  exact (deriv_line (Ff inc supp (K u) Y)
    ((analyticOnNhd_Ff inc supp h (hKl u hu) (fun Z l hl => hb u hu Z l hl) Y 0
      h0).differentiableAt) i)

/-- Reduction to the one-parameter theorem: for `E = ℂ` the conclusion of `holo_of_KP_param`
gives that of `holo_of_KP`. -/
theorem holo_of_KP_param_complex (h : KPCond inc κ a) (hr : ∀ i, 0 < r i) {U : Set ℂ}
    (hU : IsOpen U) (K : ℂ → P → (ι → ℂ) → ℂ)
    (hKl : ∀ u ∈ U, ∀ Z, AnalyticOnNhd ℂ (K u Z) (polydisc 0 r))
    (hKu : ∀ Z, ∀ l ∈ polydisc (0 : ι → ℂ) r, DifferentiableOn ℂ (fun u => K u Z l) U)
    (hb : ∀ u ∈ U, ∀ Z, ∀ l ∈ polydisc (0 : ι → ℂ) r, ‖K u Z l‖ ≤ κ Z) (Y : Finset B) :
    DifferentiableOn ℂ (fun u => PY inc supp (fun Z => K u Z 0) Y) U ∧
      ∀ i, DifferentiableOn ℂ (fun u => D1 i (Ff inc supp (K u) Y)) U :=
  let H := holo_of_KP_param inc supp h hr hU K hKl (fun Z l hl => (hKu Z l hl).analyticOnNhd hU)
    hb Y
  ⟨H.1.differentiableOn, fun i => (H.2 i).differentiableOn⟩

end Parameter

end Balaban.Polymer
