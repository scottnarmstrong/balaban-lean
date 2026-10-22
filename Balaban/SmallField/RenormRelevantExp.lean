/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpCauchy
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Positivity

/-!
# Analyticity and bounds of the relevant parts of a localized expansion

For a localized expansion `f D ξ = ∑_{Y ∈ 𝒴} f_Y((Ψ, h̃), ξ)` (`IsLocExp`, Theorem 3.1 (g), (h) of
FLUCTUATION.md), the relevant parts of the density, taken as functions of the renormalization
parameter `ξ`, are analytic on the polydisc and bounded by the total size of the terms.  The value
at a datum `D` is bounded by `∑_Y B e^{-κ d(Y)}`; the derivative of `s ↦ f (γ s) ξ` along an
analytic path of data at `s₀` is analytic in `ξ`, and bounded by `∑_Y B e^{-κ d(Y)} / ρ` by Cauchy's
estimate on a circle of radius `ρ` around `s₀`.  The derivatives along `ψ = (1+t) e` and in `h` are
paths of this kind.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Metric

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {Dom : BgData G N → Prop} {r B κ : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {f : BgData G N → (Fin 3 → ℂ) → ℂ}
  {term : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → ℂ}

/-- The total size `∑_{Y ∈ 𝒴} B e^{-κ d(Y)}` of the terms of an expansion. -/
noncomputable def expTotal (Ys : Finset (Finset (Torus d (N₀ * L ^ k))))
    (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ) (κ B : ℝ) : ℝ :=
  ∑ Y ∈ Ys, B * Real.exp (-κ * dY Y)

/-- The value of an expansion is bounded by the total size of its terms. -/
theorem IsLocExp.norm_le_expTotal (h : IsLocExp G Dom r Ys dY κ B f term) {D : BgData G N}
    (hD : Dom D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r) : ‖f D ξ‖ ≤ expTotal Ys dY κ B := by
  rw [h.sum_eq D hD ξ hξ]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun Y hY => h.bound Y hY _ ⟨D, hD, rfl, hξ⟩)

/-- The value of an expansion at a fixed datum is analytic in `ξ` on the polydisc. -/
theorem IsLocExp.differentiableOn_xi (h : IsLocExp G Dom r Ys dY κ B f term) {D : BgData G N}
    (hD : Dom D) : DifferentiableOn ℂ (f D) (ball 0 r) := by
  have : Set.EqOn (f D) (fun ξ => ∑ Y ∈ Ys, term Y ((D.Ψ, D.h), ξ)) (ball 0 r) :=
    fun ξ hξ => h.sum_eq D hD ξ (mem_ball_zero_iff.1 hξ)
  refine DifferentiableOn.congr (fun ξ hξ => ?_) this
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (Finset.analyticAt_fun_sum Ys ?_ ).differentiableAt
  intro Y hY
  exact ((h.analytic Y hY _ ⟨D, hD, rfl, mem_ball_zero_iff.1 hξ⟩).comp
    (AnalyticAt.prod analyticAt_const analyticAt_id))

/-- The raw data of a path of data. -/
def rawPath (γ : ℂ → BgData G N) (s : ℂ) : RawData d L N₀ k N := ((γ s).Ψ, (γ s).h)

/-- **Joint analyticity** of the expansion along an analytic path of data: `(s, ξ) ↦ f (γ s) ξ` is
analytic on `ball s₀ ρ' × ball 0 r`. -/
theorem IsLocExp.analyticOnNhd_path (h : IsLocExp G Dom r Ys dY κ B f term) {γ : ℂ → BgData G N}
    {s₀ : ℂ} {ρ' : ℝ} (hD : ∀ s ∈ ball s₀ ρ', Dom (γ s))
    (hγ : AnalyticOnNhd ℂ (rawPath γ) (ball s₀ ρ')) :
    AnalyticOnNhd ℂ (fun p : ℂ × (Fin 3 → ℂ) => f (γ p.1) p.2) (ball s₀ ρ' ×ˢ ball 0 r) := by
  intro p hp
  have hs := hp.1
  have hx := mem_ball_zero_iff.1 hp.2
  have hsum : AnalyticAt ℂ (fun p : ℂ × (Fin 3 → ℂ) => ∑ Y ∈ Ys, term Y (rawPath γ p.1, p.2)) p := by
    refine Finset.analyticAt_fun_sum Ys ?_
    intro Y hY
    have hmap : AnalyticAt ℂ (fun p : ℂ × (Fin 3 → ℂ) => (rawPath γ p.1, p.2)) p :=
      AnalyticAt.prod ((hγ _ hs).comp_of_eq analyticAt_fst rfl) analyticAt_snd
    exact (h.analytic Y hY (rawPath γ p.1, p.2) ⟨γ p.1, hD _ hs, rfl, hx⟩).comp_of_eq hmap rfl
  refine hsum.congr ?_
  have : (ball s₀ ρ' ×ˢ ball (0 : Fin 3 → ℂ) r) ∈ nhds p :=
    (isOpen_ball.prod isOpen_ball).mem_nhds hp
  filter_upwards [this] with q hq
  exact (h.sum_eq (γ q.1) (hD _ hq.1) q.2 (mem_ball_zero_iff.1 hq.2)).symm

/-- **The derivative along a path of data is analytic in `ξ`.** -/
theorem IsLocExp.differentiableOn_deriv_path (h : IsLocExp G Dom r Ys dY κ B f term)
    {γ : ℂ → BgData G N} {s₀ : ℂ} {ρ' : ℝ} (hρ' : 0 < ρ') (hD : ∀ s ∈ ball s₀ ρ', Dom (γ s))
    (hγ : AnalyticOnNhd ℂ (rawPath γ) (ball s₀ ρ')) :
    DifferentiableOn ℂ (fun ξ => deriv (fun s => f (γ s) ξ) s₀) (ball 0 r) := by
  have hA := h.analyticOnNhd_path hD hγ
  intro ξ hξ
  have hmem : (s₀, ξ) ∈ ball s₀ ρ' ×ˢ ball (0 : Fin 3 → ℂ) r := ⟨mem_ball_self hρ', hξ⟩
  have hF := (hA _ hmem).fderiv
  have key : ∀ η ∈ ball (0 : Fin 3 → ℂ) r,
      deriv (fun s => f (γ s) η) s₀ = fderiv ℂ (fun p : ℂ × (Fin 3 → ℂ) => f (γ p.1) p.2) (s₀, η) (1, 0) := by
    intro η hη
    have hm : (s₀, η) ∈ ball s₀ ρ' ×ˢ ball (0 : Fin 3 → ℂ) r := ⟨mem_ball_self hρ', hη⟩
    have hd := ((hA _ hm).differentiableAt).hasFDerivAt
    have hp : HasDerivAt (fun s : ℂ => (s, η)) ((1 : ℂ), (0 : Fin 3 → ℂ)) s₀ :=
      (hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ η)
    exact (hd.comp_hasDerivAt s₀ hp).deriv
  have hev : (fun η => deriv (fun s => f (γ s) η) s₀) =ᶠ[nhds ξ]
      fun η => fderiv ℂ (fun p : ℂ × (Fin 3 → ℂ) => f (γ p.1) p.2) (s₀, η) (1, 0) := by
    filter_upwards [isOpen_ball.mem_nhds hξ] with η hη using key η hη
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have h1 : DifferentiableAt ℂ (fun η : Fin 3 → ℂ =>
      fderiv ℂ (fun p : ℂ × (Fin 3 → ℂ) => f (γ p.1) p.2) (s₀, η)) ξ :=
    hF.differentiableAt.comp ξ (differentiableAt_const s₀ |>.prodMk differentiableAt_id)
  exact h1.clm_apply (differentiableAt_const _)

/-- **Cauchy's estimate for the derivative along a path of data**: if the path stays in the domain
on the ball of radius `ρ' > ρ` around `s₀`, then the derivative at `s₀` is bounded by the total size
of the terms divided by `ρ`. -/
theorem IsLocExp.norm_deriv_path_le (h : IsLocExp G Dom r Ys dY κ B f term)
    {γ : ℂ → BgData G N} {s₀ : ℂ} {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    (hD : ∀ s ∈ ball s₀ ρ', Dom (γ s)) (hγ : AnalyticOnNhd ℂ (rawPath γ) (ball s₀ ρ'))
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r) :
    ‖deriv (fun s => f (γ s) ξ) s₀‖ ≤ expTotal Ys dY κ B / ρ := by
  have hA := h.analyticOnNhd_path hD hγ
  have hsub : closedBall s₀ ρ ⊆ ball s₀ ρ' := closedBall_subset_ball hρρ'
  have hdiff : DifferentiableOn ℂ (fun s => f (γ s) ξ) (closedBall s₀ ρ) := fun s hs => by
    have h1 := (hA (s, ξ) ⟨hsub hs, mem_ball_zero_iff.2 hξ⟩).differentiableAt.hasFDerivAt
    have h2 := h1.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s ξ))
    exact h2.differentiableAt.differentiableWithinAt
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    (hdiff.diffContOnCl_ball (subset_refl _) |>.mono (by simp))
    (fun s hs => h.norm_le_expTotal (hD s (hsub (sphere_subset_closedBall hs))) hξ)

end Balaban.Fluctuation
