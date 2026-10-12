/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir3
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Equivariance of the ray terms (FLUCTUATION.md Proposition 3.3, symmetry)

The terms of the localized interaction are `rayTerm (dl3 Ev w) ω x₀ σ Θ`.  If `Ev` is analytic on
`S × B` and invariant under a pair `(fΛ, fF)` of maps (additive and homogeneous in the fluctuation
variable) preserving `S × B`, the term is transported: the term at `(fF x₀, fF w, σ, fΛ Θ)` is the
term at `(x₀, w, σ, Θ)`.  Reality: if `conj Ev (Θ, z) = Ev (Θ, z)` ... see `rayTerm_conj`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric

section Ray

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Transport of the ray terms under a symmetry of `Ev`.** -/
theorem rayTerm_dl3_equiv {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ}
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (fΛ : Λ → Λ) (fF : F → F)
    (hadd : ∀ x y, fF (x + y) = fF x + fF y) (hsm : ∀ (c : ℂ) x, fF (c • x) = c • fF x)
    (hinv : ∀ Θ ∈ S, ∀ z ∈ B, Ev (fΛ Θ, fF z) = Ev (Θ, z))
    (hS : ∀ Θ ∈ S, fΛ Θ ∈ S) (hB : ∀ z ∈ B, fF z ∈ B)
    {ω : ℂ → ℂ} {x₀ w : F} {σ : ℂ} {r : ℝ} (hr : 0 < r) {Θ : Λ} (hΘ : Θ ∈ S)
    (hline : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r → (σ * (t : ℂ)) • x₀ + τ • w ∈ B) :
    rayTerm (dl3 Ev (fF w)) ω (fF x₀) σ (fΛ Θ) = rayTerm (dl3 Ev w) ω x₀ σ Θ := by
  unfold rayTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  congr 1
  have hz := hline t ht
  have h1 : (σ * (t : ℂ)) • fF x₀ = fF ((σ * (t : ℂ)) • x₀) := (hsm _ _).symm
  rw [h1, dl3_apply, dl3_apply]
  have hA : ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w) := fun τ hτ =>
    hEv _ ⟨hΘ, hz τ hτ.le⟩
  have hA' : ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (fΛ Θ, fF ((σ * (t : ℂ)) • x₀) + τ • fF w) := fun τ hτ => by
    have : fF ((σ * (t : ℂ)) • x₀) + τ • fF w = fF ((σ * (t : ℂ)) • x₀ + τ • w) := by
      rw [hadd, hsm τ w]
    rw [this]
    exact hEv _ ⟨hS Θ hΘ, hB _ (hz τ hτ.le)⟩
  rw [dirL3_eq hr hA', dirL3_eq hr hA]
  refine dirS3_congr ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
  have hτ' : ‖τ‖ ≤ r := by simpa using (mem_ball_zero_iff.1 hτ).le
  have : fF ((σ * (t : ℂ)) • x₀) + τ • fF w = fF ((σ * (t : ℂ)) • x₀ + τ • w) := by
    rw [hadd, hsm τ w]
  rw [this]
  exact hinv Θ hΘ _ (hz τ hτ')

theorem iteratedDeriv_conj_conj_aux (n : ℕ) :
    ∀ (f g : ℂ → ℂ) (x : ℂ), (∀ᶠ τ in nhds x, g τ = starRingEnd ℂ (f (starRingEnd ℂ τ))) →
      iteratedDeriv n g x = starRingEnd ℂ (iteratedDeriv n f (starRingEnd ℂ x)) := by
  induction n with
  | zero =>
    intro f g x h
    simpa using h.self_of_nhds
  | succ n ih =>
    intro f g x h
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    refine ih (deriv f) (deriv g) x ?_
    filter_upwards [h.eventually_nhds] with y hy
    have h1 : deriv g y = deriv (starRingEnd ℂ ∘ f ∘ starRingEnd ℂ) y := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hy] with z hz using hz
    rw [h1, deriv_conj_conj]
    rfl

/-- **Reality of the ray terms**: for an analytic `Ev` with `conj Ev (Θ, z) = Ev (Θ, cF z)` (`cF`
the conjugation of the fluctuation variable), real directions and real `σ`, `ω`, the ray term is
real. -/
theorem rayTerm_dl3_conj {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ}
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (cF : F → F)
    (hadd : ∀ x y, cF (x + y) = cF x + cF y)
    (hsm : ∀ (c : ℂ) x, cF (c • x) = (starRingEnd ℂ c) • cF x)
    {Θ : Λ} (hreal : ∀ z ∈ B, starRingEnd ℂ (Ev (Θ, z)) = Ev (Θ, cF z))
    {ω : ℂ → ℂ} {x₀ w : F} {σ : ℂ} {r : ℝ} (hr : 0 < r) (hΘ : Θ ∈ S)
    (hσ : starRingEnd ℂ σ = σ) (hx : cF x₀ = x₀) (hw : cF w = w)
    (hω : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → starRingEnd ℂ (ω (t : ℂ)) = ω (t : ℂ))
    (hline : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r → (σ * (t : ℂ)) • x₀ + τ • w ∈ B) :
    starRingEnd ℂ (rayTerm (dl3 Ev w) ω x₀ σ Θ) = rayTerm (dl3 Ev w) ω x₀ σ Θ := by
  unfold rayTerm
  rw [map_mul, hσ]
  congr 1
  have hcI : ∀ G : ℝ → ℂ, starRingEnd ℂ (∫ t in (0 : ℝ)..1, G t) =
      ∫ t in (0 : ℝ)..1, starRingEnd ℂ (G t) := fun G => by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      integral_conj]
  rw [hcI]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [map_mul]
  rw [hω t ht]
  congr 1
  have hz := hline t ht
  have hA : ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w) := fun τ hτ =>
    hEv _ ⟨hΘ, hz τ hτ.le⟩
  rw [dl3_apply, dirL3_eq hr hA]
  unfold dirS3
  have hcz : cF ((σ * (t : ℂ)) • x₀) = (σ * (t : ℂ)) • x₀ := by
    rw [hsm, hx]
    simp [hσ]
  have := iteratedDeriv_conj_conj_aux 3 (fun τ : ℂ => Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w))
    (fun τ : ℂ => Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w)) 0 ?_
  · simpa using this.symm
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
    have hτ' : ‖τ‖ ≤ r := by simpa using (mem_ball_zero_iff.1 hτ).le
    have hτ'' : ‖starRingEnd ℂ τ‖ ≤ r := by simpa using hτ'
    have h1 := hreal _ (hz _ hτ'')
    rw [h1, hadd ((σ * (t : ℂ)) • x₀) (starRingEnd ℂ τ • w), hcz, hsm (starRingEnd ℂ τ) w, hw]
    simp

end Ray

end Balaban.Fluctuation
