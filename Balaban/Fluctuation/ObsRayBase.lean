/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir3

/-!
# Analyticity of the direct terms in a parameter, and along the complex hat ray (base file)

The parameter and ray statements of `ObsRayAnalytic` for the first-order direct term `dirTerm` and
the cubic potential term `rayTerm (dl3 Ev w)`, placed below the sharp assembly so that the
construction of the direct terms can carry them.  `analyticAt_param_H`, `dirL3_param_eq` and
`analyticOnNhd_rayTerm_dl3_param` come from `MarkedCubicJoint`, and the remaining statements from
`ObsRayAnalytic`, unchanged.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section Abstract

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
variable {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {R₁ r : ℝ}
  {V : Set Q} {Θf : Q → Λ} {wf : Q → F}

/-- The function `(σ, q) ↦ Ev(Θ(q), σ w(q))` is analytic at `(σ, q)` for `q ∈ V`, `‖σ‖ < R₁ + r`,
when `Θ`, `w` are analytic on `V`, `Θ(q) ∈ S` and the disc `σ w(q)` stays in `B`. -/
theorem analyticAt_param_H (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : AnalyticOnNhd ℂ Θf V)
    (hw : AnalyticOnNhd ℂ wf V) (hmem : ∀ q ∈ V, Θf q ∈ S)
    (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • wf q ∈ B) {x : ℂ × Q}
    (hx1 : ‖x.1‖ < R₁ + r) (hx2 : x.2 ∈ V) :
    AnalyticAt ℂ (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2)) x := by
  have hm : AnalyticAt ℂ (fun x : ℂ × Q => ((Θf x.2, x.1 • wf x.2) : Λ × F)) x :=
    AnalyticAt.prod ((hΘ x.2 hx2).comp analyticAt_snd)
      (analyticAt_fst.smul ((hw x.2 hx2).comp analyticAt_snd))
  exact (hEv _ ⟨hmem x.2 hx2, hdom x.2 hx2 x.1 hx1⟩).comp_of_eq hm rfl

/-- The third directional derivative of `Ev` at `s w(q)` in the direction `w(q)` is the third
`σ`-derivative of `(σ, q) ↦ Ev(Θ(q), σ w(q))` at `σ = s`. -/
theorem dirL3_param_eq (hr : 0 < r) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : AnalyticOnNhd ℂ Θf V) (hw : AnalyticOnNhd ℂ wf V) (hmem : ∀ q ∈ V, Θf q ∈ S)
    (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • wf q ∈ B) {q : Q} (hq : q ∈ V) {s : ℂ}
    (hs : ‖s‖ < R₁) :
    dirL3 Ev (wf q) (Θf q) (s • wf q) =
      (lineD ((1 : ℂ), (0 : Q)))^[3] (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2)) (s, q) := by
  have hr' : ∀ τ : ℂ, ‖τ‖ < r → ‖s + τ‖ < R₁ + r := fun τ hτ =>
    (norm_add_le _ _).trans_lt (add_lt_add hs hτ)
  have hf : ∀ τ : ℂ, ‖τ‖ < r → AnalyticAt ℂ Ev (Θf q, s • wf q + τ • wf q) := fun τ hτ => by
    rw [← add_smul]
    exact hEv _ ⟨hmem q hq, hdom q hq _ (hr' τ hτ)⟩
  rw [dirL3_eq hr hf]
  unfold dirS3
  have e : (fun τ : ℂ => Ev (Θf q, s • wf q + τ • wf q)) =
      fun τ : ℂ => (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2))
        ((s, q) + τ • ((1 : ℂ), (0 : Q))) := by
    funext τ
    have h2 : ((s, q) + τ • ((1 : ℂ), (0 : Q)) : ℂ × Q) = (s + τ, q) := by ext <;> simp
    rw [h2]
    show Ev (Θf q, s • wf q + τ • wf q) = Ev (Θf q, (s + τ) • wf q)
    rw [add_smul]
  rw [e]
  have := iteratedDeriv_line (E := ℂ × Q) (s, q) ((1 : ℂ), (0 : Q)) (r := r) 3
    (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2))
    (fun τ hτ => analyticAt_param_H hEv hΘ hw hmem hdom (by simpa using hr' τ hτ)
      (by simpa using hq)) 0 (by simpa using hr)
  simpa using this

/-- **The cubic Taylor term is analytic in a parameter.**  Let `Ev` be analytic on `S × B`, `V` an
open set of a parameter space, `q ↦ Θ(q)` and `q ↦ w(q)` analytic on `V` with `Θ(q) ∈ S` and
`σ w(q) ∈ B` for `‖σ‖ < R₁ + r` (`R₁ > 1`, `r > 0`), and `ω` analytic on `‖σ‖ < R₁`.  Then
`q ↦ ∫₀¹ ω(s) D³Ev(Θ(q), s w(q))[w(q), w(q), w(q)] ds` is analytic on `V`. -/
theorem analyticOnNhd_rayTerm_dl3_param (hV : IsOpen V) (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : AnalyticOnNhd ℂ Θf V) (hw : AnalyticOnNhd ℂ wf V) (hmem : ∀ q ∈ V, Θf q ∈ S)
    (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • wf q ∈ B) :
    AnalyticOnNhd ℂ (fun q => rayTerm (dl3 Ev (wf q)) ω (wf q) 1 (Θf q)) V := by
  set H : ℂ × Q → ℂ := fun x => Ev (Θf x.2, x.1 • wf x.2) with hHdef
  have hK : ∀ x : ℂ × Q, ‖x.1‖ < R₁ + r → x.2 ∈ V →
      AnalyticAt ℂ ((lineD ((1 : ℂ), (0 : Q)))^[3] H) x := by
    intro x h1 h2
    exact analyticAt_lineD _ (analyticAt_lineD _ (analyticAt_lineD _
      (analyticAt_param_H hEv hΘ hw hmem hdom h1 h2)))
  have hint : AnalyticOnNhd ℂ (fun q : Q => ∫ s in (0 : ℝ)..1,
      ω (s : ℂ) * ((lineD ((1 : ℂ), (0 : Q)))^[3] H) ((s : ℂ), q)) V := by
    refine analyticOnNhd_unitIntegral (f := fun (q : Q) (s : ℂ) =>
      ω s * ((lineD ((1 : ℂ), (0 : Q)))^[3] H) (s, q)) hR₁ ?_
    rintro ⟨q, s⟩ ⟨hq, hs⟩
    have hs' : ‖s‖ < R₁ := mem_ball_zero_iff.1 hs
    have hm : AnalyticAt ℂ (fun p : Q × ℂ => (p.2, p.1)) (q, s) :=
      analyticAt_snd.prod analyticAt_fst
    exact ((hω s hs).comp (analyticAt_snd (𝕜 := ℂ))).mul
      ((hK (s, q) (by simp only; linarith) hq).comp_of_eq hm rfl)
  refine hint.congr hV fun q hq => ?_
  unfold rayTerm
  rw [one_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hs' : ‖(s : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
  rw [dl3_apply, one_mul, dirL3_param_eq hr hEv hΘ hw hmem hdom hq hs']

end Abstract

section Param

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
variable {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {R₁ : ℝ}
  {V : Set Q} {Θf : Q → Λ} {xf wf : Q → F}

/-- **The first-order direct term is analytic in a parameter.**  Let `Ev` be analytic on `S × B`,
`ω` analytic on `‖t‖ < R₁` (`R₁ > 1`), `q ↦ Θ(q)`, `q ↦ x₀(q)`, `q ↦ w(q)` analytic on `V` with
`V` open, `Θ(q) ∈ S` and `t x₀(q) ∈ B` for `‖t‖ < R₁`.  Then
`q ↦ ∫₀¹ ω(t) ∂_{w(q)} Ev(Θ(q), t x₀(q)) dt` (`dirTerm` at `σ = 1`) is analytic on `V`.  The
premise `σ x₀(q) ∈ B` for `‖σ‖ < R₁ + r`, `r > 0`, implies the one used here. -/
theorem analyticOnNhd_dirTerm_param (hV : IsOpen V) (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : AnalyticOnNhd ℂ Θf V) (hx : AnalyticOnNhd ℂ xf V) (hw : AnalyticOnNhd ℂ wf V)
    (hmem : ∀ q ∈ V, Θf q ∈ S) (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ → σ • xf q ∈ B) :
    AnalyticOnNhd ℂ (fun q => dirTerm Ev ω (xf q) (wf q) 1 (Θf q)) V := by
  have hint : AnalyticOnNhd ℂ (fun q : Q => ∫ t in (0 : ℝ)..1,
      ω (t : ℂ) * fderiv ℂ Ev (Θf q, (t : ℂ) • xf q) ((0 : Λ), wf q)) V := by
    refine analyticOnNhd_unitIntegral (f := fun (q : Q) (t : ℂ) =>
      ω t * fderiv ℂ Ev (Θf q, t • xf q) ((0 : Λ), wf q)) hR₁ ?_
    rintro ⟨q, t⟩ ⟨hq, ht⟩
    have ht' : ‖t‖ < R₁ := mem_ball_zero_iff.1 ht
    have hpt : (Θf q, t • xf q) ∈ S ×ˢ B := ⟨hmem q hq, hdom q hq t ht'⟩
    have hm : AnalyticAt ℂ (fun p : Q × ℂ => ((Θf p.1, p.2 • xf p.1) : Λ × F)) (q, t) :=
      AnalyticAt.prod ((hΘ q hq).comp analyticAt_fst)
        (analyticAt_snd.smul ((hx q hq).comp analyticAt_fst))
    have h1 : AnalyticAt ℂ (fun p : Q × ℂ => fderiv ℂ Ev ((Θf p.1, p.2 • xf p.1) : Λ × F))
        (q, t) := (hEv.fderiv _ hpt).comp_of_eq hm rfl
    have h2 : AnalyticAt ℂ (fun p : Q × ℂ =>
        fderiv ℂ Ev ((Θf p.1, p.2 • xf p.1) : Λ × F) ((0 : Λ), wf p.1)) (q, t) :=
      ((ContinuousLinearMap.id ℂ ((Λ × F) →L[ℂ] ℂ)).analyticAt_bilinear _).comp_of_eq
        (h1.prod (analyticAt_const.prod ((hw q hq).comp analyticAt_fst))) rfl
    exact ((hω t ht).comp (analyticAt_snd (𝕜 := ℂ))).mul h2
  refine hint.congr hV fun q _ => ?_
  simp [dirTerm, dirD]

end Param

section Ray

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {R₁ r : ℝ}

/-- **The linear direct term along the diagonal complex ray.**  At a constant datum `Θ ∈ S`, the
map `z ↦ dirTerm Ev ω (z ψ̂) (z ψ̂) 1 Θ` is differentiable on `‖z‖ < 3/2`, provided `Ev` is analytic
on `S × B` and `u ψ̂ ∈ B` for `‖u‖ < R₁ · (3/2)`. -/
theorem differentiableOn_dirTerm_ray (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    {Θ : Λ} (hΘ : Θ ∈ S) (ψ : F)
    (hdom : ∀ u : ℂ, ‖u‖ < R₁ * (3 / 2) → u • ψ ∈ B) :
    DifferentiableOn ℂ (fun z : ℂ => dirTerm Ev ω (z • ψ) (z • ψ) 1 Θ) (ball (0 : ℂ) (3 / 2)) := by
  refine (analyticOnNhd_dirTerm_param (V := ball (0 : ℂ) (3 / 2)) (Θf := fun _ => Θ)
    (xf := fun z => z • ψ) (wf := fun z => z • ψ) isOpen_ball hR₁ hω hEv
    (fun _ _ => analyticAt_const) (fun z _ => analyticAt_id.smul analyticAt_const)
    (fun z _ => analyticAt_id.smul analyticAt_const) (fun _ _ => hΘ) ?_).differentiableOn
  intro z hz σ hσ
  rw [smul_smul]
  refine hdom _ ?_
  rw [norm_mul]
  have hz' : ‖z‖ < 3 / 2 := mem_ball_zero_iff.1 hz
  exact mul_lt_mul'' hσ hz' (norm_nonneg _) (norm_nonneg _)

/-- **The cubic potential term along the diagonal complex ray.**  At a constant datum `Θ ∈ S`,
`z ↦ rayTerm (dl3 Ev (z ψ̂)) ω (z ψ̂) 1 Θ` is differentiable on `‖z‖ < 3/2`, provided `Ev` is
analytic on `S × B`, `R₁ > 1`, `r > 0`, and `u ψ̂ ∈ B` for `‖u‖ < (R₁ + r) · (3/2)`. -/
theorem differentiableOn_rayTerm_dl3_ray (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    {Θ : Λ} (hΘ : Θ ∈ S) (ψ : F)
    (hdom : ∀ u : ℂ, ‖u‖ < (R₁ + r) * (3 / 2) → u • ψ ∈ B) :
    DifferentiableOn ℂ (fun z : ℂ => rayTerm (dl3 Ev (z • ψ)) ω (z • ψ) 1 Θ)
      (ball (0 : ℂ) (3 / 2)) := by
  refine (analyticOnNhd_rayTerm_dl3_param (V := ball (0 : ℂ) (3 / 2)) (Θf := fun _ => Θ)
    (wf := fun z => z • ψ) isOpen_ball hR₁ hr hω hEv
    (fun _ _ => analyticAt_const) (fun z _ => analyticAt_id.smul analyticAt_const)
    (fun _ _ => hΘ) ?_).differentiableOn
  intro z hz σ hσ
  rw [smul_smul]
  refine hdom _ ?_
  rw [norm_mul]
  have hz' : ‖z‖ < 3 / 2 := mem_ball_zero_iff.1 hz
  exact mul_lt_mul'' hσ hz' (norm_nonneg _) (norm_nonneg _)

end Ray

section RayPi

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {ι : Type*} [Fintype ι]
variable {S : Set Λ} {Ev : Λ × (ι → ℂ) → ℂ} {ω : ℂ → ℂ} {R₁ r cψ : ℝ}

omit [Fintype ι] in
/-- The sup-norm bound `(R₁ + r) · (3/2) · ‖ψ̂ p‖ ≤ cψ` puts `u ψ̂` in the closed `cψ`-ball for
`‖u‖ < (R₁ + r) · (3/2)`. -/
theorem smul_mem_closedBall_of_bound (ψ : ι → ℂ)
    (hψ : ∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) (u : ℂ) (hu : ‖u‖ < (R₁ + r) * (3 / 2)) :
    u • ψ ∈ {ψh : ι → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := fun p => by
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right hu.le (norm_nonneg _)).trans (hψ p)

/-- `differentiableOn_dirTerm_ray` for the closed `cψ`-ball of the hat variable. -/
theorem differentiableOn_dirTerm_ray_ball (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ {ψh : ι → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {Θ : Λ} (hΘ : Θ ∈ S) (ψ : ι → ℂ) (hψ : ∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) :
    DifferentiableOn ℂ (fun z : ℂ => dirTerm Ev ω (z • ψ) (z • ψ) 1 Θ) (ball (0 : ℂ) (3 / 2)) :=
  differentiableOn_dirTerm_ray hR₁ hω hEv hΘ ψ fun u hu =>
    smul_mem_closedBall_of_bound ψ hψ u
      (hu.trans_le (mul_le_mul_of_nonneg_right (by linarith) (by norm_num)))

/-- `differentiableOn_rayTerm_dl3_ray` for the closed `cψ`-ball of the hat variable. -/
theorem differentiableOn_rayTerm_dl3_ray_ball (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ {ψh : ι → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {Θ : Λ} (hΘ : Θ ∈ S) (ψ : ι → ℂ) (hψ : ∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) :
    DifferentiableOn ℂ (fun z : ℂ => rayTerm (dl3 Ev (z • ψ)) ω (z • ψ) 1 Θ)
      (ball (0 : ℂ) (3 / 2)) :=
  differentiableOn_rayTerm_dl3_ray hR₁ hr hω hEv hΘ ψ
    (smul_mem_closedBall_of_bound ψ hψ)

end RayPi

end Balaban.Fluctuation
