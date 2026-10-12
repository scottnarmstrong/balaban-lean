/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir
public import Balaban.Fluctuation.InteractionLoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The first-derivative terms of an analytic expansion form a localized expansion

The abstract version of `eterm_locInt`: if `f(Θ, z) = ∑_Y Ev_Y(Θ, z)` on `S × B` with analytic,
bounded, local terms, then `σ ∫₀¹ ω(t') ∂_w f(Θ, σ t' x₀) dt'` is a localized expansion
(`LocInt`) over the same domains with the bound `|σ| M_ω b_Y / r`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section LocDir

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {S : Set Λ} {B : Set F} {ω : ℂ → ℂ} {Rσ R₁ : ℝ}

theorem locInt_dir1 {ι : Type*} (𝒴 : Finset ι) {Evs : ι → Λ × F → ℂ} {f : Λ × F → ℂ}
    {b : ι → ℝ} {AgΘ : ι → Λ → Λ → Prop} {AgF : ι → F → F → Prop}
    (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hωc : Continuous ω)
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r : ℝ} (hr : 0 < r) (hBo : IsOpen B) (hEv : ∀ Y, AnalyticOnNhd ℂ (Evs Y) (S ×ˢ B))
    (hb : ∀ Y, ∀ u ∈ S ×ˢ B, ‖Evs Y u‖ ≤ b Y)
    (hlin : ∀ Y (a a' c c' : F) (p q : ℂ), AgF Y a a' → AgF Y c c' →
      AgF Y (p • a + q • c) (p • a' + q • c'))
    (hloc : ∀ Y, ∀ Θ ∈ S, ∀ Θ' ∈ S, ∀ z ∈ B, ∀ z' ∈ B, AgΘ Y Θ Θ' → AgF Y z z' →
      Evs Y (Θ, z) = Evs Y (Θ', z'))
    (hsum : ∀ Θ ∈ S, ∀ z ∈ B, f (Θ, z) = ∑ Y ∈ 𝒴, Evs Y (Θ, z)) :
    LocInt S {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
        (σ * t) • xw.1 + τ • xw.2 ∈ B} Rσ 𝒴
      (fun Y x₀ w σ Θ => dirTerm (Evs Y) ω x₀ w σ Θ)
      (fun x₀ w σ Θ => dirTermSrc f ω x₀ w σ Θ) (fun Y => Mω * (b Y / r)) AgΘ AgF := by
  have hreal : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hdom0 : ∀ xw ∈ {xw : F × F | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
        (σ * t) • xw.1 + τ • xw.2 ∈ B}, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ →
        (σ * t) • xw.1 ∈ B := fun xw hxw σ hσ t ht => by
    simpa using hxw σ hσ t ht 0 (by simp [hr.le])
  refine ⟨fun xw hxw σ hσ Θ hΘ => ?_, fun Y _ xw hxw => ?_, fun Y _ xw hxw σ hσ Θ hΘ => ?_,
    fun Y _ xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3 => ?_, fun Y _ xw hxw Θ hΘ => ?_⟩
  · exact dirTermSrc_sum 𝒴 hBo hEv hsum hωc hΘ (fun t ht => hdom0 xw hxw σ hσ t (hreal t ht))
  · exact dirTerm_analytic hR₁ hω (hEv Y) (hdom0 xw hxw)
  · refine (norm_dirTerm_le hr hMω hωb (hEv Y) (fun u hu => hb Y u hu) hΘ
      (fun t ht τ hτ => hxw σ hσ t (hreal t ht) τ hτ)).trans (le_of_eq (by ring))
  · exact dirTerm_local (hlin Y) (fun Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' =>
      hloc Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2') (hEv Y) hΘ hΘ' h1 h2 h3 hr
      (fun t ht τ hτ => ⟨hxw σ hσ t (hreal t ht) τ hτ, hxw' σ hσ t (hreal t ht) τ hτ⟩)
  · exact dirTerm_zero Θ

end LocDir

end Balaban.Fluctuation
