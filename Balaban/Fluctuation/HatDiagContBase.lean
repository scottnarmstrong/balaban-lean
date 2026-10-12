/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir3
public import Balaban.Fluctuation.InteractionLocDir
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Continuity of the diagonal terms of an analytic expansion

The terms of the localized expansion of Proposition 3.3 are, along the diagonal `x₀ = w = ψ̂`
of the hat variable, the ray integrals `σ ∫₀¹ ω(t) ∂_ψ̂ Ev(Θ, σ t ψ̂) dt` (`dirTerm`) and
`σ ∫₀¹ ω(t) ∂³_ψ̂ Ev(Θ, σ t ψ̂) dt` (`rayTerm (dl3 ·)`) of functions `Ev` analytic on a
neighbourhood of `S × B`.  Such an expression is continuous in `ψ̂` on the set of `ψ̂` whose rays
stay in `B` (`diagCont_dirTerm`, `diagCont_rayTerm`), by the joint continuity in the base point and
the direction of the iterated Fréchet derivatives of an analytic function (`lineD_three`).

`DiagCont` is this property for an arbitrary family of terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section LineThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Congruence of the directional derivative for functions that agree near a point. -/
theorem lineD_eventuallyEq {φ φ' : E → ℂ} {x : E} (h : φ =ᶠ[nhds x] φ') (v : E) :
    lineD v φ =ᶠ[nhds x] lineD v φ' := by
  filter_upwards [h.eventually_nhds] with y hy using lineD_congr_eventually hy v

/-- The derivative of a function of `(u, v)` in the direction `(v, 0)`: the directional
derivative in `u` along `v`, jointly in `(u, v)`. -/
noncomputable def dirDv (G : E × E → ℂ) : E × E → ℂ := fun p => fderiv ℂ G p (p.2, 0)

theorem analyticAt_dirDv {G : E × E → ℂ} {p : E × E} (hG : AnalyticAt ℂ G p) :
    AnalyticAt ℂ (dirDv G) p := by
  have hb : AnalyticAt ℂ (fun q : (E × E →L[ℂ] ℂ) × (E × E) => (ContinuousLinearMap.id ℂ
      (E × E →L[ℂ] ℂ)) q.1 q.2) (fderiv ℂ G p, (p.2, 0)) :=
    ContinuousLinearMap.analyticAt_bilinear _ _
  have h2 : AnalyticAt ℂ (fun q : E × E => (q.2, (0 : E))) p :=
    analyticAt_snd.prod analyticAt_const
  exact AnalyticAt.comp₂ (h := fun q : (E × E →L[ℂ] ℂ) × (E × E) => (ContinuousLinearMap.id ℂ
      (E × E →L[ℂ] ℂ)) q.1 q.2) hb hG.fderiv h2

/-- The directional derivative of `u ↦ G (u, v)` is `dirDv G` near an analytic point. -/
theorem lineD_dirDv_eventually {G : E × E → ℂ} {u v : E} (hG : AnalyticAt ℂ G (u, v)) :
    lineD v (fun u' => G (u', v)) =ᶠ[nhds u] fun u' => dirDv G (u', v) := by
  have hc : Filter.Tendsto (fun u' : E => (u', v)) (nhds u) (nhds (u, v)) :=
    (continuous_id.prodMk continuous_const).tendsto u
  filter_upwards [hc.eventually hG.eventually_analyticAt] with u' hu'
  have hd : DifferentiableAt ℂ G (u', v) := hu'.differentiableAt
  have hm : HasFDerivAt (fun u'' : E => (u'', v)) ((ContinuousLinearMap.id ℂ E).prod
      (0 : E →L[ℂ] E)) u' := (hasFDerivAt_id u').prodMk (hasFDerivAt_const v u')
  have hcomp : HasFDerivAt (fun u'' : E => G (u'', v))
      ((fderiv ℂ G (u', v)).comp ((ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] E))) u' :=
    hd.hasFDerivAt.comp u' hm
  rw [lineD_eq_fderiv v hcomp.differentiableAt, hcomp.fderiv]
  simp [dirDv]

/-- The third directional derivative of an analytic function, jointly in the base point and the
direction. -/
theorem lineD_three {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) (v : E) :
    lineD v (lineD v (lineD v f)) x = dirDv (dirDv (dirDv (fun p : E × E => f p.1))) (x, v) ∧
    AnalyticAt ℂ (dirDv (dirDv (dirDv (fun p : E × E => f p.1)))) (x, v) := by
  have a0 : AnalyticAt ℂ (fun p : E × E => f p.1) (x, v) := hf.comp (analyticAt_fst (𝕜 := ℂ))
  have a1 := analyticAt_dirDv a0
  have a2 := analyticAt_dirDv a1
  have a3 := analyticAt_dirDv a2
  refine ⟨?_, a3⟩
  have s1 := lineD_dirDv_eventually (u := x) a0
  have s2 := (lineD_eventuallyEq s1 v).trans (lineD_dirDv_eventually (u := x) a1)
  have s3 := (lineD_eventuallyEq s2 v).trans (lineD_dirDv_eventually (u := x) a2)
  exact s3.self_of_nhds

end LineThree

section Cont

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The third directional derivative `dl3` of a function analytic at `u` is, jointly in
`(u, w)`, an analytic function of `(u, (0, w))`. -/
theorem dl3_eq_dirDv3 {Ev : Λ × F → ℂ} {u : Λ × F} (h : AnalyticAt ℂ Ev u) (w : F) :
    dl3 Ev w u = dirDv (dirDv (dirDv (fun p : (Λ × F) × (Λ × F) => Ev p.1))) (u, ((0 : Λ), w)) ∧
    AnalyticAt ℂ (dirDv (dirDv (dirDv (fun p : (Λ × F) × (Λ × F) => Ev p.1)))) (u, ((0 : Λ), w)) :=
  lineD_three h _

/-- Continuity in `ψ` of a parametric interval integral over `[0, 1]`, when the integrand is
continuous on `D × [0, 1]`. -/
theorem continuousOn_intervalIntegral_param {X : Type*} [TopologicalSpace X] {D : Set X}
    {Φ : X → ℝ → ℂ} (h : ContinuousOn (fun p : X × ℝ => Φ p.1 p.2) (D ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..1, Φ x t) D := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hmap : Continuous (fun p : D × ℝ =>
      ((p.1.1, (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) : X × ℝ)) := by fun_prop
  have hΨ : Continuous (fun p : D × ℝ => Φ p.1.1 (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) :=
    h.comp_continuous hmap (fun p => ⟨p.1.2, (Set.projIcc (0 : ℝ) 1 zero_le_one p.2).2⟩)
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume)
    (f := fun (x : D) (t : ℝ) => Φ x.1 (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ))
    (by exact hΨ) 0 1
  refine hc.congr fun x => ?_
  simp only [Set.domRestrict_apply]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp [Set.projIcc_of_mem _ ht]

variable {S : Set Λ} {B : Set F} {ω : ℂ → ℂ} {Rσ R₁ r : ℝ}

/-- The set of hat variables whose diagonal ray pair is admissible. -/
def DiagDom {E F : Type*} (e : E → F) (XW : Set (F × F)) : Set E := {ψ | (e ψ, e ψ) ∈ XW}

/-- **Continuity of the diagonal terms.**  For every label `Y`, `‖σ‖ < R_σ` and `Θ ∈ S`, the
function `ψ ↦ T_Y(e ψ, e ψ, σ, Θ)` is continuous on the set of `ψ` whose diagonal pair is
admissible. -/
def DiagCont {E F Λ ι : Type*} [TopologicalSpace E] (e : E → F) (XW : Set (F × F)) (S : Set Λ)
    (Rσ : ℝ) (𝒴 : Finset ι) (T : ι → F → F → ℂ → Λ → ℂ) : Prop :=
  ∀ Y ∈ 𝒴, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S,
    ContinuousOn (fun ψ => T Y (e ψ) (e ψ) σ Θ) (DiagDom e XW)

/-- The ray stays in `B` along the diagonal of an admissible pair. -/
theorem ray_mem_of_diag {ψ : F} (hR₁ : 1 < R₁) (hr : 0 < r)
    (h : (ψ, ψ) ∈ {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
        (σ * t) • xw.1 + τ • xw.2 ∈ B}) {σ : ℂ} (hσ : ‖σ‖ < Rσ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (σ * (t : ℂ)) • ψ ∈ B := by
  have hreal : ‖(t : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  simpa using h σ hσ t hreal 0 (by simp [hr.le])

/-- **The first-derivative terms are continuous along the diagonal.** -/
theorem diagCont_dirTerm {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ}
    (hR₁ : 1 < R₁) (hωc : Continuous ω) (hr : 0 < r)
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B)) :
    DiagCont (id : F → F) {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ,
        ‖τ‖ ≤ r → (σ * t) • xw.1 + τ • xw.2 ∈ B} S Rσ 𝒴
      (fun Y x₀ w σ Θ => dirTerm (Evs Y) ω x₀ w σ Θ) := by
  intro Y _ σ hσ Θ hΘ
  unfold dirTerm
  refine continuousOn_const.mul ?_
  refine continuousOn_intervalIntegral_param (Φ := fun ψ t =>
    ω (t : ℂ) * dirD (Evs Y) ψ Θ ((σ * (t : ℂ)) • ψ)) ?_
  have hq : Continuous (fun p : F × ℝ => ((Θ, (σ * (p.2 : ℂ)) • p.1) : Λ × F)) := by fun_prop
  have hmem : ∀ p ∈ DiagDom (id : F → F) {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ →
      ∀ τ : ℂ, ‖τ‖ ≤ r → (σ * t) • xw.1 + τ • xw.2 ∈ B} ×ˢ Icc (0 : ℝ) 1,
      ((Θ, (σ * (p.2 : ℂ)) • p.1) : Λ × F) ∈ S ×ˢ B := fun p hp =>
    ⟨hΘ, ray_mem_of_diag (Rσ := Rσ) hR₁ hr hp.1 hσ hp.2⟩
  have h1 := ((hEv Y).fderiv.continuousOn).comp hq.continuousOn hmem
  have h2 := (continuous_const.prodMk continuous_fst : Continuous (fun p : F × ℝ => ((0 : Λ), p.1))).continuousOn
    (s := DiagDom (id : F → F) {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ,
        ‖τ‖ ≤ r → (σ * t) • xw.1 + τ • xw.2 ∈ B} ×ˢ Icc (0 : ℝ) 1)
  exact (hωc.comp (Complex.continuous_ofReal.comp continuous_snd)).continuousOn.mul
    (h1.clm_apply h2)

/-- **The third-derivative terms are continuous along the diagonal.** -/
theorem diagCont_rayTerm {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ}
    (hR₁ : 1 < R₁) (hωc : Continuous ω) (hr : 0 < r)
    (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B)) :
    DiagCont (id : F → F) {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ,
        ‖τ‖ ≤ r → (σ * t) • xw.1 + τ • xw.2 ∈ B} S Rσ 𝒴
      (fun Y x₀ w σ Θ => rayTerm (dl3 (Evs Y) w) ω x₀ σ Θ) := by
  intro Y _ σ hσ Θ hΘ
  unfold rayTerm
  refine continuousOn_const.mul ?_
  set D : Set F := DiagDom (id : F → F) {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ →
    ∀ τ : ℂ, ‖τ‖ ≤ r → (σ * t) • xw.1 + τ • xw.2 ∈ B} with hD
  set H : (Λ × F) × (Λ × F) → ℂ :=
    dirDv (dirDv (dirDv (fun p : (Λ × F) × (Λ × F) => Evs Y p.1))) with hH
  have hq : Continuous (fun p : F × ℝ =>
      (((Θ, (σ * (p.2 : ℂ)) • p.1) : Λ × F), ((0 : Λ), p.1))) := by fun_prop
  have hmem : ∀ p ∈ D ×ˢ Icc (0 : ℝ) 1,
      ((Θ, (σ * (p.2 : ℂ)) • p.1) : Λ × F) ∈ S ×ˢ B := fun p hp =>
    ⟨hΘ, ray_mem_of_diag (Rσ := Rσ) hR₁ hr hp.1 hσ hp.2⟩
  have hHc : ContinuousOn (fun p : F × ℝ => H (((Θ, (σ * (p.2 : ℂ)) • p.1) : Λ × F),
      ((0 : Λ), p.1))) (D ×ˢ Icc (0 : ℝ) 1) := by
    intro p hp
    exact ((dl3_eq_dirDv3 (hEv Y _ (hmem p hp)) p.1).2.continuousAt.comp_of_eq
      hq.continuousAt rfl).continuousWithinAt
  have hint := continuousOn_intervalIntegral_param (D := D) (Φ := fun ψ t => ω (t : ℂ) *
      H (((Θ, (σ * (t : ℂ)) • ψ) : Λ × F), ((0 : Λ), ψ)))
      ((hωc.comp (Complex.continuous_ofReal.comp continuous_snd)).continuousOn.mul hHc)
  refine hint.congr fun ψ hψ => ?_
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hu : ((Θ, (σ * (t : ℂ)) • ψ) : Λ × F) ∈ S ×ˢ B :=
    ⟨hΘ, ray_mem_of_diag (Rσ := Rσ) hR₁ hr hψ hσ ht⟩
  simp only [id, (dl3_eq_dirDv3 (hEv Y _ hu) ψ).1, hH]

end Cont

end Balaban.Fluctuation
