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
(`rayTerm (dl3 Ev w) ω x₀ σ Θ`).  The directional derivative `lineD v f x` is the derivative of the
line function `t ↦ f(x + t v)` at `0`, so the third derivative at a point only reads the term on a
segment through that point in the direction `v = (0, w)`.  Hence two terms `Ev`, `Ev'` read at two
data `Θ`, `Θ'` give the same ray integral as soon as they agree near the ray (no analyticity is
needed):

* `lineD_congr_line`, `dl3_congr_line`: if `f(x + τ v) = g(x' + τ v)` for `|τ| < r`, the iterated
  directional derivatives agree on the same segments;
* `rayTerm_dl3_congr_of_line`: if at every point `σ t x₀`, `t ∈ [0, 1]`, the two terms agree on a
  segment `σ t x₀ + τ w`, `|τ| < r`, the two ray integrals are equal;
* `exists_segment_of_norm_lt`: in a space of functions on a finite set, if `|σ| |x₀ q| < c` for
  every `q`, then for every `t ∈ [0, 1]` a segment `σ t x₀ + τ w`, `|τ| < r`, lies in the box
  `|ψ q| ≤ c`;
* `rayTerm_dl3_congr_of_box`: the two together, for terms that agree on `{Θ} × box` and
  `{Θ'} × box`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Localization Set Filter Metric Topology

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The directional derivative reads the function only on the line.**  If `f(x + τ v)` and
`g(x' + τ v)` agree for `|τ| < r`, so do `lineD v f (x + τ v)` and `lineD v g (x' + τ v)`. -/
theorem lineD_congr_line {f g : E → ℂ} {x x' v : E} {r : ℝ}
    (h : ∀ τ : ℂ, ‖τ‖ < r → f (x + τ • v) = g (x' + τ • v)) :
    ∀ τ : ℂ, ‖τ‖ < r → lineD v f (x + τ • v) = lineD v g (x' + τ • v) := by
  intro τ hτ
  unfold lineD
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {s : ℂ | ‖τ + s‖ < r} :=
    isOpen_lt (continuous_const.add continuous_id).norm continuous_const
  filter_upwards [hopen.mem_nhds (by simpa using hτ)] with s hs
  have e1 : x + τ • v + s • v = x + (τ + s) • v := by rw [add_smul, add_assoc]
  have e2 : x' + τ • v + s • v = x' + (τ + s) • v := by rw [add_smul, add_assoc]
  rw [e1, e2]
  exact h _ hs

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The third derivative reads the term only on the segment.**  If `Ev(Θ, z + τ w)` and
`Ev'(Θ', z + τ w)` agree for `|τ| < r` (`r > 0`), then `dl3 Ev w (Θ, z) = dl3 Ev' w (Θ', z)`. -/
theorem dl3_congr_line {Ev Ev' : Λ × F → ℂ} {Θ Θ' : Λ} {z w : F} {r : ℝ} (hr : 0 < r)
    (h : ∀ τ : ℂ, ‖τ‖ < r → Ev (Θ, z + τ • w) = Ev' (Θ', z + τ • w)) :
    dl3 Ev w (Θ, z) = dl3 Ev' w (Θ', z) := by
  have hline : ∀ (Θ₀ : Λ) (τ : ℂ), ((Θ₀, z) : Λ × F) + τ • ((0 : Λ), w) = (Θ₀, z + τ • w) := by
    intro Θ₀ τ
    ext <;> simp
  have h0 : ∀ τ : ℂ, ‖τ‖ < r → Ev (((Θ, z) : Λ × F) + τ • ((0 : Λ), w)) =
      Ev' (((Θ', z) : Λ × F) + τ • ((0 : Λ), w)) := fun τ hτ => by
    rw [hline, hline]; exact h τ hτ
  have h3 := lineD_congr_line (lineD_congr_line (lineD_congr_line h0)) 0 (by simpa using hr)
  simpa [dl3] using h3

/-- **The ray integral of the third derivative reads the term only along the ray.**  If at every
point `σ t x₀` of the ray (`t ∈ [0, 1]`) there is a segment `σ t x₀ + τ w`, `|τ| < r`, on which `Ev`
(at `Θ`) and `Ev'` (at `Θ'`) agree, then
`rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ'`. -/
theorem rayTerm_dl3_congr_of_line {Ev Ev' : Λ × F → ℂ} (ω : ℂ → ℂ) {x₀ w : F} {σ : ℂ}
    {Θ Θ' : Λ}
    (h : ∀ t : ℝ, t ∈ uIcc (0 : ℝ) 1 → ∃ r : ℝ, 0 < r ∧ ∀ τ : ℂ, ‖τ‖ < r →
      Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w) = Ev' (Θ', (σ * (t : ℂ)) • x₀ + τ • w)) :
    rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ' := by
  unfold rayTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  obtain ⟨r, hr, hτ⟩ := h t ht
  exact congrArg _ (dl3_congr_line hr hτ)

end Line

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

/-- **The ray integrals agree for terms that agree on the box.**  If `Ev(Θ, ψ) = Ev'(Θ', ψ)` for
every `ψ` with `|ψ q| ≤ c` for all `q`, and `|σ| |x₀ q| < c` for every `q`, then
`rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ'`. -/
theorem rayTerm_dl3_congr_of_box {Ev Ev' : Λ × (Q → ℂ) → ℂ} (ω : ℂ → ℂ) {x₀ w : Q → ℂ} {σ : ℂ}
    {Θ Θ' : Λ} {c : ℝ} (heq : ∀ ψ : Q → ℂ, (∀ q, ‖ψ q‖ ≤ c) → Ev (Θ, ψ) = Ev' (Θ', ψ))
    (hσx : ∀ q, ‖σ‖ * ‖x₀ q‖ < c) :
    rayTerm (dl3 Ev w) ω x₀ σ Θ = rayTerm (dl3 Ev' w) ω x₀ σ Θ' := by
  obtain ⟨r, hr, hseg⟩ := exists_segment_of_norm_lt (w := w) hσx
  exact rayTerm_dl3_congr_of_line ω fun t ht =>
    ⟨r, hr, fun τ hτ => heq _ (hseg t ht τ hτ)⟩

end Box

end Balaban.Fluctuation
