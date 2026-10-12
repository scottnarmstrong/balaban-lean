/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ParameterAnalytic
public import Balaban.Localization.I5Param
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Parameter integrals and directional Cauchy estimates (FLUCTUATION §3.3, P6 (4.4)-(4.6), (4.15))

Two generic tools for the localized interaction `𝒰_{t,u}` of Proposition 3.3:

* `analyticOnNhd_unitIntegral`: `a ↦ ∫₀¹ f(a, t) dt` is analytic on `S` when `f` is analytic on
  `S × {|t| < R}`, `R > 1` (the `t'`-integral of (3.3)); no openness of `S` and no bound is
  assumed (the local bound comes from compactness and the tube lemma, as in
  `analyticOnNhd_coef_of_analyticOnNhd`);
* `norm_lineD_le`: the Cauchy estimate `|∂_w f(x)| ≤ B / r` for the derivative of `f` at `x`
  in the direction `w` when `f` is analytic and bounded by `B` on the closed disc
  `{x + τ w : |τ| ≤ r}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section UnitIntegral

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **The `t'`-integral of an analytic family is analytic.** -/
theorem analyticOnNhd_unitIntegral {S : Set Λ} {R : ℝ} (hR : 1 < R) {f : Λ → ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ (fun p : Λ × ℂ => f p.1 p.2) (S ×ˢ ball (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (fun a => ∫ t in (0 : ℝ)..1, f a (t : ℂ)) S := by
  intro a ha
  set R' : ℝ := (1 + R) / 2 with hR'
  have hR'1 : 1 < R' := by rw [hR']; linarith
  have hR'R : R' < R := by rw [hR']; linarith
  set K : Set ℂ := closedBall (0 : ℂ) R' with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hKball : K ⊆ ball (0 : ℂ) R := fun s hs => by
    rw [mem_ball_zero_iff]; rw [hK, mem_closedBall_zero_iff] at hs; linarith
  set Φ : Λ × ℂ → ℂ := fun p => f p.1 p.2 with hΦ
  have hanK : ∀ s ∈ K, AnalyticAt ℂ Φ (a, s) := fun s hs => hf (a, s) ⟨ha, hKball hs⟩
  set U : Set (Λ × ℂ) := {x | AnalyticAt ℂ Φ x} with hU
  have hUo : IsOpen U := isOpen_analyticAt ℂ Φ
  have hcont : ContinuousOn Φ U := fun x hx =>
    (hx : AnalyticAt ℂ Φ x).continuousAt.continuousWithinAt
  have hcontK : ContinuousOn (fun s : ℂ => Φ (a, s)) K := fun s hs =>
    ((hanK s hs).continuousAt.comp (f := fun s' : ℂ => (a, s')) (by fun_prop)).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn hcontK
  set n : Set (Λ × ℂ) := U ∩ {x | ‖Φ x‖ < ‖M₀‖ + 1} with hn
  have hno : IsOpen n := by
    have := hcont.norm.isOpen_inter_preimage hUo (isOpen_Iio : IsOpen (Set.Iio (‖M₀‖ + 1)))
    convert this using 1
    ext x; simp [hn, hU]
  have hsub : ({a} : Set Λ) ×ˢ K ⊆ n := by
    rintro ⟨a', s⟩ ⟨ha', hs⟩
    rw [Set.mem_singleton_iff] at ha'
    subst ha'
    refine ⟨hanK s hs, ?_⟩
    have h2 : ‖Φ (a', s)‖ ≤ ‖M₀‖ := (hM₀ s hs).trans (by rw [Real.norm_eq_abs]; exact le_abs_self _)
    show ‖Φ (a', s)‖ < ‖M₀‖ + 1
    linarith
  obtain ⟨u, v, hu, hv, hau, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hKc hno hsub
  have hVsub : u ×ˢ ball (0 : ℂ) R' ⊆ n := by
    refine (Set.prod_mono subset_rfl ?_).trans huv
    refine fun s hs => hKv ?_
    rw [hK, mem_closedBall_zero_iff]
    exact (mem_ball_zero_iff.1 hs).le
  -- the one-coordinate version of `analyticOnNhd_integral_step`
  set Q : Λ × (Unit → ℂ) → ℂ := fun x => f x.1 (x.2 ()) with hQ
  have hQa : AnalyticOnNhd ℂ Q (Dom u R' ([] : List Unit)) := by
    intro x hx
    have hx2 : ‖x.2 ()‖ < R' := hx.2 () (by simp)
    have hmem : (x.1, x.2 ()) ∈ u ×ˢ ball (0 : ℂ) R' := ⟨hx.1, mem_ball_zero_iff.2 hx2⟩
    have h1 : AnalyticAt ℂ Φ (x.1, x.2 ()) := (hVsub hmem).1
    exact h1.comp (f := fun y : Λ × (Unit → ℂ) => (y.1, y.2 ()))
      ((analyticAt_fst (𝕜 := ℂ)).prod
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Unit => ℂ) ()).analyticAt x.2).comp
          (analyticAt_snd (𝕜 := ℂ))))
  have hQb : ∀ x ∈ Dom u R' ([] : List Unit), ‖Q x‖ ≤ ‖M₀‖ + 1 := by
    intro x hx
    have hx2 : ‖x.2 ()‖ < R' := hx.2 () (by simp)
    exact (hVsub (show (x.1, x.2 ()) ∈ u ×ˢ ball (0 : ℂ) R' from
      ⟨hx.1, mem_ball_zero_iff.2 hx2⟩)).2.le
  have hint := (analyticOnNhd_integral_step hR'1 hu ([] : List Unit) () hQa hQb).1
  have hmem : ((a, fun _ => (0 : ℂ)) : Λ × (Unit → ℂ)) ∈ Dom u R' [()] :=
    ⟨hau rfl, fun i hi => absurd (by simp) hi⟩
  have h1 := (hint _ hmem).comp (f := fun a' : Λ => (a', (fun _ : Unit => (0 : ℂ))))
    ((analyticAt_id (𝕜 := ℂ)).prod (analyticAt_const (𝕜 := ℂ)))
  refine h1.congr ?_
  filter_upwards [hu.mem_nhds (hau rfl)] with a' _
  simp only [Function.comp, hQ]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp

end UnitIntegral

section Cauchy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The Cauchy estimate for a directional derivative.** -/
theorem norm_lineD_le {f : E → ℂ} {x w : E} {r B : ℝ} (hr : 0 < r)
    (hf : ∀ τ : ℂ, ‖τ‖ ≤ r → AnalyticAt ℂ f (x + τ • w))
    (hB : ∀ τ : ℂ, ‖τ‖ ≤ r → ‖f (x + τ • w)‖ ≤ B) : ‖lineD w f x‖ ≤ B / r := by
  have hd : DiffContOnCl ℂ (fun τ : ℂ => f (x + τ • w)) (ball (0 : ℂ) r) := by
    refine DifferentiableOn.diffContOnCl fun τ hτ => ?_
    have hτ' : ‖τ‖ ≤ r := by
      have := closure_ball_subset_closedBall hτ
      rwa [mem_closedBall_zero_iff] at this
    exact ((hf τ hτ').comp (f := fun τ : ℂ => x + τ • w) (by fun_prop)).differentiableAt.differentiableWithinAt
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) hr hd
    (fun τ hτ => hB τ (by simpa using hτ.le))
  have hder : lineD w f x = deriv (fun τ : ℂ => f (x + τ • w)) 0 := rfl
  rw [hder]; exact this

end Cauchy

end Balaban.Fluctuation
