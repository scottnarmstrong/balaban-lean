/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpLemma35
public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Localized expansions in the renormalization parameters, and the Cauchy factor `ε`

FLUCTUATION.md v2.3 §3.6, proof of Theorem 3.1 (g), (h).  The renormalization parameters
`ξ ∈ ℂ³` range over a polydisc; the expansions of (g), (h) have terms analytic jointly in the
fields and `ξ`.  The factor `ε` (the radius of the polydisc `𝒫_ε`) in the bounds of the old-term
differences comes from Cauchy's estimate in the source ("the `τ`-derivative is bounded by Cauchy on
`|τ| = c_r/ε`"): a function of `ξ` analytic on the polydisc `|ξ|_∞ < r₀`, bounded by `M` there and
vanishing at `ξ = 0`, is bounded by `M |ξ|_∞ / r₀` (Schwarz's lemma, `norm_le_of_vanish`).

* `IsLocExp` — an expansion `f(ψ, ξ) = ∑_{Y ∈ 𝒴} f_Y(ψ, ξ)` over localization domains `Y` with
  terms analytic jointly in the raw data and `ξ` on `𝒟 × {|ξ|_∞ < r}`, depending on the data only
  through their values on `Y`, and bounded by `B e^{-κ d(Y)}`;
* `IsLocExp.add`, `IsLocExp.mono`, `IsLocExp.mono_radius`, `IsLocExp.mono_rate`: algebra;
* `IsLocExp.cauchy`: an expansion on the polydisc of radius `r₀` whose terms vanish at `ξ = 0`
  is, on the polydisc of radius `r ≤ r₀`, an expansion with the bound `B r / r₀`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Metric

section Schwarz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- **Schwarz's lemma for a function vanishing at the origin** (several variables, any normed
target): analytic on `‖x‖ < r`, bounded by `M`, `f 0 = 0` give `‖f x‖ ≤ (M / r) ‖x‖`. -/
theorem norm_le_of_vanish {f : E → F} {r M : ℝ} (hd : DifferentiableOn ℂ f (ball 0 r))
    (hM : ∀ x ∈ ball (0 : E) r, ‖f x‖ ≤ M) (h0 : f 0 = 0) {x : E} (hx : x ∈ ball (0 : E) r) :
    ‖f x‖ ≤ M / r * ‖x‖ := by
  have hmaps : Set.MapsTo f (ball 0 r) (closedBall (f 0) M) := fun y hy => by
    rw [h0, mem_closedBall_zero_iff]; exact hM y hy
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmaps hx
  rwa [h0, dist_zero_right, dist_zero_right] at h

/-- The difference form: `‖f x - f 0‖ ≤ (2 M / r) ‖x‖` for `f` analytic and bounded by `M` on the
ball of radius `r`. -/
theorem norm_sub_le_two_mul_of_ball {f : E → F} {r M : ℝ} (hd : DifferentiableOn ℂ f (ball 0 r))
    (hM : ∀ x ∈ ball (0 : E) r, ‖f x‖ ≤ M) {x : E} (hx : x ∈ ball (0 : E) r) :
    ‖f x - f 0‖ ≤ 2 * M / r * ‖x‖ := by
  have h0 : (0 : E) ∈ ball (0 : E) r := mem_ball_self (pos_of_mem_ball hx)
  have := norm_le_of_vanish (f := fun y => f y - f 0) (M := 2 * M)
    (hd.sub (differentiableOn_const (f 0)))
    (fun y hy => (norm_sub_le _ _).trans (by linarith [hM y hy, hM 0 h0])) (by simp) hx
  simpa using this

end Schwarz

section Expansion

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (G) in
/-- The domain `𝒟 × {|ξ|_∞ < r}` of the expansions, as a set of `((Ψ, h̃), ξ)`. -/
def expDom (Dom : BgData G N → Prop) (r : ℝ) : Set (RawData d L N₀ k N × (Fin 3 → ℂ)) :=
  {q | ∃ D : BgData G N, Dom D ∧ q.1 = (D.Ψ, D.h) ∧ ‖q.2‖ < r}

/-- Two raw data agree on the set of sites `Y`. -/
def RawAgree (Y : Finset (Torus d (N₀ * L ^ k))) (p p' : RawData d L N₀ k N) : Prop :=
  ∀ x ∈ Y, p.1 x = p'.1 x ∧ p.2 x = p'.2 x

variable (G) in
/-- **A localized expansion** (FLUCTUATION.md Theorem 3.1): on the data `D` with `Dom D` and the
polydisc `|ξ|_∞ < r`, `f D ξ = ∑_{Y ∈ 𝒴} f_Y((Ψ, h̃), ξ)`, every term `f_Y` is analytic jointly in
`((Ψ, h̃), ξ)` on that domain, depends on the data only through their values on `Y`, and is
bounded by `B e^{-κ d(Y)}`. -/
structure IsLocExp (Dom : BgData G N → Prop) (r : ℝ) (Ys : Finset (Finset (Torus d (N₀ * L ^ k))))
    (dY : Finset (Torus d (N₀ * L ^ k)) → ℝ) (κ B : ℝ) (f : BgData G N → (Fin 3 → ℂ) → E)
    (term : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E) : Prop where
  sum_eq : ∀ D : BgData G N, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
    f D ξ = ∑ Y ∈ Ys, term Y ((D.Ψ, D.h), ξ)
  analytic : ∀ Y ∈ Ys, AnalyticOnNhd ℂ (term Y) (expDom G Dom r)
  local_ : ∀ Y ∈ Ys, ∀ q ∈ expDom G Dom r, ∀ q' ∈ expDom G Dom r, q.2 = q'.2 →
    RawAgree Y q.1 q'.1 → term Y q = term Y q'
  bound : ∀ Y ∈ Ys, ∀ q ∈ expDom G Dom r, ‖term Y q‖ ≤ B * Real.exp (-κ * dY Y)

variable {Dom : BgData G N → Prop} {r r' r₀ κ κ' B B' : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {f g : BgData G N → (Fin 3 → ℂ) → E}
  {term term' : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E}

theorem expDom_mono {r r' : ℝ} (h : r ≤ r') : expDom G Dom r ⊆ expDom (N := N) G Dom r' := by
  rintro q ⟨D, hD, h1, h2⟩
  exact ⟨D, hD, h1, h2.trans_le h⟩

/-- The sum of two expansions over the same domains. -/
theorem IsLocExp.add (h₁ : IsLocExp G Dom r Ys dY κ B f term)
    (h₂ : IsLocExp G Dom r Ys dY κ B' g term') :
    IsLocExp G Dom r Ys dY κ (B + B') (fun D ξ => f D ξ + g D ξ)
      (fun Y q => term Y q + term' Y q) where
  sum_eq D hD ξ hξ := by rw [h₁.sum_eq D hD ξ hξ, h₂.sum_eq D hD ξ hξ, Finset.sum_add_distrib]
  analytic Y hY q hq := (h₁.analytic Y hY q hq).add (h₂.analytic Y hY q hq)
  local_ Y hY q hq q' hq' h2 hag := by
    rw [h₁.local_ Y hY q hq q' hq' h2 hag, h₂.local_ Y hY q hq q' hq' h2 hag]
  bound Y hY q hq := by
    have := h₁.bound Y hY q hq
    have := h₂.bound Y hY q hq
    calc ‖term Y q + term' Y q‖ ≤ ‖term Y q‖ + ‖term' Y q‖ := norm_add_le _ _
      _ ≤ B * Real.exp (-κ * dY Y) + B' * Real.exp (-κ * dY Y) := add_le_add ‹_› ‹_›
      _ = (B + B') * Real.exp (-κ * dY Y) := by ring

/-- A larger bound. -/
theorem IsLocExp.mono (h : IsLocExp G Dom r Ys dY κ B f term) (hB : B ≤ B') :
    IsLocExp G Dom r Ys dY κ B' f term :=
  { h with
    bound := fun Y hY q hq =>
      (h.bound Y hY q hq).trans (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le) }

/-- A smaller polydisc. -/
theorem IsLocExp.mono_radius (h : IsLocExp G Dom r Ys dY κ B f term) (hr : r' ≤ r) :
    IsLocExp G Dom r' Ys dY κ B f term where
  sum_eq D hD ξ hξ := h.sum_eq D hD ξ (hξ.trans_le hr)
  analytic Y hY := (h.analytic Y hY).mono (expDom_mono hr)
  local_ Y hY q hq q' hq' := h.local_ Y hY q (expDom_mono hr hq) q' (expDom_mono hr hq')
  bound Y hY q hq := h.bound Y hY q (expDom_mono hr hq)

/-- A smaller rate, for nonnegative sizes. -/
theorem IsLocExp.mono_rate (h : IsLocExp G Dom r Ys dY κ B f term) (hκ : κ' ≤ κ) (hB : 0 ≤ B)
    (hd : ∀ Y ∈ Ys, 0 ≤ dY Y) : IsLocExp G Dom r Ys dY κ' B f term :=
  { h with
    bound := fun Y hY q hq => (h.bound Y hY q hq).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [hd Y hY])) hB) }

/-- **The Cauchy factor** (FLUCTUATION.md §3.6, proof of (g): "the `τ`-derivative is bounded by
Cauchy"): if the terms of an expansion on the polydisc of radius `r₀` vanish at `ξ = 0`, then on
the polydisc of radius `r ≤ r₀` the expansion holds with the bound `B r / r₀`. -/
theorem IsLocExp.cauchy (h : IsLocExp G Dom r₀ Ys dY κ B f term) (hr₀ : 0 < r₀) (hr : r ≤ r₀)
    (h0 : ∀ Y ∈ Ys, ∀ D : BgData G N, Dom D → term Y ((D.Ψ, D.h), 0) = 0) :
    IsLocExp G Dom r Ys dY κ (B * (r / r₀)) f term where
  sum_eq D hD ξ hξ := h.sum_eq D hD ξ (hξ.trans_le hr)
  analytic Y hY := (h.analytic Y hY).mono (expDom_mono hr)
  local_ Y hY q hq q' hq' := h.local_ Y hY q (expDom_mono hr hq) q' (expDom_mono hr hq')
  bound Y hY q hq := by
    obtain ⟨D, hD, hq1, hq2⟩ := hq
    have hmem : ∀ ξ ∈ ball (0 : Fin 3 → ℂ) r₀, ((D.Ψ, D.h), ξ) ∈ expDom G Dom r₀ :=
      fun ξ hξ => ⟨D, hD, rfl, mem_ball_zero_iff.1 hξ⟩
    have hdiff : DifferentiableOn ℂ (fun ξ : Fin 3 → ℂ => term Y ((D.Ψ, D.h), ξ))
        (ball 0 r₀) := fun ξ hξ =>
      ((h.analytic Y hY _ (hmem ξ hξ)).comp
        (analyticAt_const.prod analyticAt_id)).differentiableAt.differentiableWithinAt
    have hS := norm_le_of_vanish hdiff (fun ξ hξ => h.bound Y hY _ (hmem ξ hξ)) (h0 Y hY D hD)
      (mem_ball_zero_iff.2 (hq2.trans_le hr))
    have hq : q = ((D.Ψ, D.h), q.2) := Prod.ext hq1 rfl
    rw [hq]
    have hB : 0 ≤ B * Real.exp (-κ * dY Y) := by
      have := (norm_nonneg _).trans (h.bound Y hY _ (hmem 0 (mem_ball_self hr₀)))
      exact this
    calc ‖term Y ((D.Ψ, D.h), q.2)‖ ≤ B * Real.exp (-κ * dY Y) / r₀ * ‖q.2‖ := hS
      _ ≤ B * Real.exp (-κ * dY Y) / r₀ * r := by
          exact mul_le_mul_of_nonneg_left (hq2.le) (by positivity)
      _ = B * (r / r₀) * Real.exp (-κ * dY Y) := by ring

end Expansion

end Balaban.Fluctuation
