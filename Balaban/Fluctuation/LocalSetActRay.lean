/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir3

/-!
# The ray integral of the third derivative depends only on the term along the ray

The potential part of the zero-source term of a domain is `σ ∫₀¹ ω(t) ∂_w³ Ev(Θ, σ t x₀) dt`
(`rayTerm (dl3 Ev w) ω x₀ σ Θ`).  The third derivative at a point of the ray only reads `Ev` on a
segment through that point in the direction `w`, when `Ev` is analytic there (`dirL3_eq`).  Hence two
terms `Ev`, `Ev'` read at two data `Θ`, `Θ'` give the same ray integral as soon as they agree near
the ray:

* `rayTerm_dl3_congr_of_line`: if at every point `σ t x₀`, `t ∈ [0, 1]`, both terms are analytic on
  a segment `σ t x₀ + τ w`, `|τ| < r`, and agree there, the two ray integrals are equal;
* `exists_segment_of_norm_lt`: in a space of functions on a finite set, if `|σ| |x₀ q| < c` for
  every `q`, then for every `t ∈ [0, 1]` a segment `σ t x₀ + τ w`, `|τ| < r`, lies in the box
  `|ψ q| ≤ c`;
* `rayTerm_dl3_congr_of_box`: the two together, for terms analytic on `{Θ} × box` and
  `{Θ'} × box` that agree there.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric Topology

section Ray

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The ray integral of the third derivative reads the term only along the ray.**  If at every
point `σ t x₀` of the ray (`t ∈ [0, 1]`) there is a segment `σ t x₀ + τ w`, `|τ| < r`, on which `Ev`
(at `Θ`) and `Ev'` (at `Θ'`) are analytic and agree, then
`rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ'`. -/
theorem rayTerm_dl3_congr_of_line {Ev Ev' : Λ × F → ℂ} (ω : ℂ → ℂ) {x₀ w : F} {σ : ℂ}
    {Θ Θ' : Λ}
    (h : ∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 → ∃ r : ℝ, 0 < r ∧ ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w) ∧
        AnalyticAt ℂ Ev' (Θ', (σ * (t : ℂ)) • x₀ + τ • w) ∧
        Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w) = Ev' (Θ', (σ * (t : ℂ)) • x₀ + τ • w)) :
    rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ' := by
  unfold rayTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  obtain ⟨r, hr, hτ⟩ := h t ht
  rw [dl3_apply, dl3_apply, dirL3_eq hr (fun τ hτ' => (hτ τ hτ').1),
    dirL3_eq hr (fun τ hτ' => (hτ τ hτ').2.1)]
  congr 1
  refine dirS3_congr ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ'
  exact (hτ τ (by simpa using hτ')).2.2

end Ray

section Box

variable {Q : Type*} [Fintype Q]

/-- **A segment through each point of the ray lies in the box.**  If `|σ| |x₀ q| < c` for every
`q`, there is `r > 0` such that `|(σ t x₀ + τ w) q| ≤ c` for all `q`, `t ∈ [0, 1]` and `|τ| < r`. -/
theorem exists_segment_of_norm_lt {x₀ w : Q → ℂ} {σ : ℂ} {c : ℝ}
    (hσx : ∀ q, ‖σ‖ * ‖x₀ q‖ < c) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ < r →
      ∀ q, ‖((σ * (t : ℂ)) • x₀ + τ • w) q‖ ≤ c := by
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ q, ‖σ‖ * ‖x₀ q‖ + r * ‖w q‖ < c := by
    refine Filter.eventually_all.2 fun q => ?_
    have hc : ContinuousAt (fun r : ℝ => ‖σ‖ * ‖x₀ q‖ + r * ‖w q‖) 0 :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hσx q)
  obtain ⟨r, hr, hr0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  refine ⟨r, hr0, fun t ht τ hτ q => ?_⟩
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  have htn : ‖(t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]
    exact ht'.2
  have h1 : ‖σ * (t : ℂ)‖ * ‖x₀ q‖ ≤ ‖σ‖ * ‖x₀ q‖ := by
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left htn (norm_nonneg σ)
    nlinarith [norm_nonneg (x₀ q)]
  have h2 : ‖τ‖ * ‖w q‖ ≤ r * ‖w q‖ :=
    mul_le_mul_of_nonneg_right hτ.le (norm_nonneg _)
  calc ‖((σ * (t : ℂ)) • x₀ + τ • w) q‖ = ‖(σ * (t : ℂ)) * x₀ q + τ * w q‖ := by
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    _ ≤ ‖σ * (t : ℂ)‖ * ‖x₀ q‖ + ‖τ‖ * ‖w q‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul (σ * (t : ℂ)), norm_mul τ]
    _ ≤ c := by linarith [hr q]

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **The ray integrals agree for terms that agree on the box.**  Let `Ev` be analytic at the
points `(Θ, ψ)` and `Ev'` at the points `(Θ', ψ)` with `|ψ q| ≤ c` for all `q`, and let them agree
there.  If `|σ| |x₀ q| < c` for every `q`, then
`rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ'`. -/
theorem rayTerm_dl3_congr_of_box {Ev Ev' : Λ × (Q → ℂ) → ℂ} (ω : ℂ → ℂ) {x₀ w : Q → ℂ} {σ : ℂ}
    {Θ Θ' : Λ} {c : ℝ}
    (hEv : ∀ ψ : Q → ℂ, (∀ q, ‖ψ q‖ ≤ c) → AnalyticAt ℂ Ev (Θ, ψ))
    (hEv' : ∀ ψ : Q → ℂ, (∀ q, ‖ψ q‖ ≤ c) → AnalyticAt ℂ Ev' (Θ', ψ))
    (heq : ∀ ψ : Q → ℂ, (∀ q, ‖ψ q‖ ≤ c) → Ev (Θ, ψ) = Ev' (Θ', ψ))
    (hσx : ∀ q, ‖σ‖ * ‖x₀ q‖ < c) :
    rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ' := by
  obtain ⟨r, hr, hseg⟩ := exists_segment_of_norm_lt (w := w) hσx
  exact rayTerm_dl3_congr_of_line ω fun t ht => ⟨r, hr, fun τ hτ =>
    ⟨hEv _ (hseg t ht τ hτ), hEv' _ (hseg t ht τ hτ), heq _ (hseg t ht τ hτ)⟩⟩

end Box

end Balaban.Fluctuation
