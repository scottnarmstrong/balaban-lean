/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic

/-!
# The identity theorem from the totally real subspace

An analytic function `P : (ι → ℂ) → ℂ` which vanishes on the real points near a real point `z₀`
vanishes on a whole neighbourhood of `z₀` (`eventually_eq_zero_of_real`).  Proof: induction on
the set of coordinates allowed to be complex, using the one-variable identity theorem along
coordinate discs.
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.Symmetry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem analyticAt_update_line (P : (ι → ℂ) → ℂ) (z : ι → ℂ) (a : ι) (l : ℂ)
    (hP : AnalyticAt ℂ P (Function.update z a l)) :
    AnalyticAt ℂ (fun l' : ℂ => P (Function.update z a l')) l := by
  have h : AnalyticAt ℂ (fun l' : ℂ => Function.update z a l') l := by
    rw [analyticAt_pi_iff]
    intro k
    by_cases hk : k = a
    · subst hk; simp only [Function.update_self]; exact analyticAt_id
    · simpa [Function.update_of_ne hk] using analyticAt_const
  exact hP.comp h

theorem eq_zero_of_real_aux {P : (ι → ℂ) → ℂ} {z₀ : ι → ℂ} (hz₀ : ∀ i, (z₀ i).im = 0)
    {ε : ℝ} (hε : 0 < ε) (hP : AnalyticOnNhd ℂ P (ball z₀ ε))
    (h0 : ∀ z ∈ ball z₀ ε, (∀ i, (z i).im = 0) → P z = 0) (S : Finset ι) :
    ∀ z ∈ ball z₀ ε, (∀ i ∉ S, (z i).im = 0) → P z = 0 := by
  induction S using Finset.induction_on with
  | empty => intro z hz hr; exact h0 z hz (fun i => hr i (by simp))
  | insert a S ha ih =>
    intro z hz hr
    have hmem : ∀ l ∈ ball (z₀ a) ε, Function.update z a l ∈ ball z₀ ε := by
      intro l hl
      rw [mem_ball, dist_pi_lt_iff hε] at hz ⊢
      intro k
      by_cases hk : k = a
      · subst hk; simpa [Function.update_self, mem_ball] using hl
      · simpa [Function.update_of_ne hk] using hz k
    set φ : ℂ → ℂ := fun l => P (Function.update z a l) with hφ
    have hφan : AnalyticOnNhd ℂ φ (ball (z₀ a) ε) := fun l hl =>
      analyticAt_update_line P z a l (hP _ (hmem l hl))
    have hreal : ∀ l ∈ ball (z₀ a) ε, l.im = 0 → φ l = 0 := by
      intro l hl hl0
      apply ih _ (hmem l hl)
      intro k hk
      by_cases hka : k = a
      · subst hka; simpa using hl0
      · rw [Function.update_of_ne hka]
        exact hr k (by simp [hka, hk])
    have hz0 : z₀ a ∈ ball (z₀ a) ε := mem_ball_self hε
    have hfreq : ∃ᶠ l in 𝓝[≠] (z₀ a), φ l = 0 := by
      rw [(nhdsWithin_hasBasis (Metric.nhds_basis_ball) {z₀ a}ᶜ).frequently_iff]
      intro δ hδ
      refine ⟨z₀ a + ((min δ ε / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]
        have := min_le_left δ ε
        linarith [lt_min hδ hε]
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have : ((min δ ε / 2 : ℝ) : ℂ) = 0 := by linear_combination h
        have h2 : (min δ ε / 2 : ℝ) = 0 := by exact_mod_cast this
        have := lt_min hδ hε
        linarith
      · apply hreal
        · rw [mem_ball, dist_eq_norm]
          simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
          rw [abs_of_pos (by have := lt_min hδ hε; positivity)]
          have := min_le_right δ ε
          linarith [lt_min hδ hε]
        · simp [hz₀ a]
    have := hφan.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball (z₀ a) ε).isPreconnected hz0 hfreq
    have hza : z a ∈ ball (z₀ a) ε := by
      rw [mem_ball, dist_pi_lt_iff hε] at hz
      simpa [mem_ball] using hz a
    have := this hza
    simpa [hφ] using this

/-- **Identity theorem from the real points**: if `P` is analytic at a real point `z₀` and
vanishes at all real points near `z₀`, it vanishes in a neighbourhood of `z₀`. -/
theorem eventually_eq_zero_of_real {P : (ι → ℂ) → ℂ} {z₀ : ι → ℂ} (hz₀ : ∀ i, (z₀ i).im = 0)
    (hP : AnalyticAt ℂ P z₀)
    (h0 : ∀ᶠ z in 𝓝 z₀, (∀ i, (z i).im = 0) → P z = 0) : ∀ᶠ z in 𝓝 z₀, P z = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hP.eventually_analyticAt.and h0)
  have hε' := hε
  have hana : AnalyticOnNhd ℂ P (ball z₀ ε) := fun z hz => (hball z hz).1
  have hall := eq_zero_of_real_aux hz₀ hε hana (fun z hz hr => (hball z hz).2 hr) Finset.univ
  exact Metric.eventually_nhds_iff_ball.mpr ⟨ε, hε, fun z hz => hall z hz (by simp)⟩

end Balaban.Symmetry
