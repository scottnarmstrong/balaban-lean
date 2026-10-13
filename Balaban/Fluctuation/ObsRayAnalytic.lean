/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedCubicJoint

/-!
# Analyticity of the first-order direct term in a parameter, and along the complex hat ray

The observable exponent is evaluated along the ray `r ↦ r ψ̂` in the hat field, so the direct terms
must be holomorphic in a complex parameter `z` that scales the hat pair.  The landed analytic
families vary the datum and the ray-integral variable at a fixed hat pair; this file supplies the
parameter versions for the two kinds of building blocks of the sharp direct terms:

* `analyticOnNhd_dirTerm_param`: the first-order term `dirTerm Ev ω (x₀ q) (w q) 1 (Θ q)` is analytic
  in a parameter `q` (the analogue of `analyticOnNhd_rayTerm_dl3_param` for the first derivative);
* `differentiableOn_dirTerm_ray`, `differentiableOn_rayTerm_dl3_ray`: along the diagonal complex ray
  `z ↦ (z ψ̂, z ψ̂)` at a constant datum, for the linear source term and the cubic potential term.

Nothing here asserts an activity, a label statement or an identity with the physical exponent.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

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

end Balaban.Fluctuation
