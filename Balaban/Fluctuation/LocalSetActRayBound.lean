/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir3
public import Balaban.Fluctuation.InteractionHatV

/-!
# The ray integral of the third derivative of a bounded analytic term

The potential part of the zero-source term of a domain is the ray integral
`σ ∫₀¹ ω(t) ∂_w³ Ev(Θ, σ t x₀) dt` (`rayTerm (dl3 Ev w) ω x₀ σ Θ`) of a term `Ev` of the localization
expansion of the block energy.  When the term is analytic and bounded by `b` on `S × B`, and the
pair `(x₀, w)` is an admissible ray (`(σ t) x₀ + τ w ∈ B` for `|σ| < R_σ`, `|t| < R₁`, `|τ| ≤ r`),
the ray integral is analytic in `(Θ, σ)` on `S × {|σ| < R_σ}` and bounded by
`|σ| M_ω 6 b / r³` there (Cauchy estimate for the third derivative):

* `rayTerm_dl3_analytic_bound`: the two statements, from `rayTerm_analytic`, `norm_rayTerm_le` and
  `norm_dirL3_le`; nothing about the term is used except analyticity and the bound on `S × B`;
* `norm_smul_lt_of_mem_hatRays`: on an admissible ray of the box `|ψ̂ q| ≤ c_ψ`, `c_ψ > 0`,
  `|σ| |x₀ q| < c_ψ` for `|σ| < R_σ` (the hypothesis of the replacement identities of the ray
  integrals, `rayTerm_dl3_congr_of_box`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Localization Set Metric

section RayBound

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Analyticity and bound of the ray integral of the third derivative.**  If `Ev` is analytic and
bounded by `b` on `S × B`, `ω` is analytic on `|t| < R₁` (`R₁ > 1`) and bounded by `M_ω` on `[0, 1]`,
and `(σ t) x₀ + τ w ∈ B` for `|σ| < R_σ`, `|t| < R₁`, `|τ| ≤ r` (`r > 0`), then
`(Θ, σ) ↦ σ ∫₀¹ ω(t) ∂_w³ Ev(Θ, σ t x₀) dt` is analytic on `S × {|σ| < R_σ}` and bounded there by
`|σ| M_ω 6 b / r³`. -/
theorem rayTerm_dl3_analytic_bound {Ev : Λ × F → ℂ} {S : Set Λ} {B : Set F} {b : ℝ}
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hb : ∀ u ∈ S ×ˢ B, ‖Ev u‖ ≤ b)
    {ω : ℂ → ℂ} {R₁ : ℝ} (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r Rσ : ℝ} (hr : 0 < r) {x₀ w : F}
    (hxw : ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * t) • x₀ + τ • w ∈ B) :
    AnalyticOnNhd ℂ (fun p : Λ × ℂ => rayTerm (dl3 Ev w) ω x₀ p.2 p.1) (S ×ˢ ball (0 : ℂ) Rσ) ∧
    ∀ Θ ∈ S, ∀ σ : ℂ, ‖σ‖ < Rσ →
      ‖rayTerm (dl3 Ev w) ω x₀ σ Θ‖ ≤ ‖σ‖ * (Mω * (6 * b / r ^ 3)) := by
  have hreal : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  refine ⟨rayTerm_analytic hR₁ hω (fun u hu => analyticAt_dirL3 (hEv u hu) w)
    (fun σ hσ t ht => by simpa using hxw σ hσ t ht 0 (by simp [hr.le])), fun Θ hΘ σ hσ => ?_⟩
  refine norm_rayTerm_le (b := 6 * b / r ^ 3) hMω hωb (fun t ht => ?_)
  have hz := fun τ (hτ : ‖τ‖ ≤ r) => hxw σ hσ t (hreal t ht) τ hτ
  rw [dl3_apply]
  exact norm_dirL3_le hr (fun τ hτ => hEv _ ⟨hΘ, hz τ hτ⟩) (fun τ hτ => hb _ ⟨hΘ, hz τ hτ⟩)

/-- **A finite sum of ray integrals of bounded analytic terms** (`rayTerm_dl3_analytic_bound` term
by term): for terms `Ev z` analytic and bounded by `b z` on `S × B` for the indices `z` with `P z`,
the sum `∑_z [P z] σ ∫₀¹ ω(t) ∂_w³ Ev_z(Θ, σ t x₀) dt` over an admissible ray is analytic in `(Θ, σ)`
on `S × {|σ| < R_σ}` and bounded there by `|σ| ∑_z [P z] M_ω 6 b_z / r³`. -/
theorem sum_rayTerm_dl3_analytic_bound {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    {Ev : ι → Λ × F → ℂ} {S : Set Λ} {B : Set F} {b : ι → ℝ}
    (hEv : ∀ z, P z → AnalyticOnNhd ℂ (Ev z) (S ×ˢ B))
    (hb : ∀ z, P z → ∀ u ∈ S ×ˢ B, ‖Ev z u‖ ≤ b z)
    {ω : ℂ → ℂ} {R₁ : ℝ} (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r Rσ : ℝ} (hr : 0 < r) {x₀ w : F}
    (hxw : ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * t) • x₀ + τ • w ∈ B) :
    AnalyticOnNhd ℂ (fun p : Λ × ℂ => ∑ z, if P z then rayTerm (dl3 (Ev z) w) ω x₀ p.2 p.1 else 0)
      (S ×ˢ ball (0 : ℂ) Rσ) ∧
    ∀ Θ ∈ S, ∀ σ : ℂ, ‖σ‖ < Rσ →
      ‖∑ z, if P z then rayTerm (dl3 (Ev z) w) ω x₀ σ Θ else 0‖ ≤
        ‖σ‖ * ∑ z, if P z then Mω * (6 * b z / r ^ 3) else 0 := by
  refine ⟨fun p hp => Finset.analyticAt_fun_sum _ fun z _ => ?_, fun Θ hΘ σ hσ => ?_⟩
  · by_cases hz : P z
    · simp only [hz, ↓reduceIte]
      exact (rayTerm_dl3_analytic_bound (hEv z hz) (hb z hz) hR₁ hω hMω hωb hr hxw).1 p hp
    · simp only [hz, ↓reduceIte]
      exact analyticAt_const
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases hz : P z
    · simp only [hz, ↓reduceIte]
      exact (rayTerm_dl3_analytic_bound (hEv z hz) (hb z hz) hR₁ hω hMω hωb hr hxw).2 Θ hΘ σ hσ
    · simp [hz]

end RayBound

section HatRays

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **On an admissible ray of the box the base point stays strictly inside.**  For
`(x₀, w) ∈ HatRays Gp c_ψ R₁ R_σ r` with `R₁ > 1`, `r ≥ 0`, `c_ψ > 0`, every `|σ| < R_σ` has
`|σ| |x₀ q| < c_ψ` for every `q`. -/
theorem norm_smul_lt_of_mem_hatRays {cψ R₁ Rσ r : ℝ} (hcψ : 0 < cψ) (hR₁ : 1 < R₁) (hr : 0 ≤ r)
    {xw : (unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)}
    (hxw : xw ∈ HatRays (N := N) Gp cψ R₁ Rσ r) {σ : ℂ} (hσ : ‖σ‖ < Rσ)
    (q : unitPts Gp × Fin N) : ‖σ‖ * ‖xw.1 q‖ < cψ := by
  set t₀ : ℝ := (1 + R₁) / 2 with ht₀
  have ht₀1 : 1 < t₀ := by rw [ht₀]; linarith
  have ht₀R : ‖(t₀ : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; rw [ht₀]; linarith
  have h := hxw σ hσ (t₀ : ℂ) ht₀R 0 (by simpa using hr) q
  simp only [zero_smul, add_zero, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < t₀)] at h
  by_cases h0 : ‖σ‖ * ‖xw.1 q‖ = 0
  · rw [h0]; exact hcψ
  · have hpos : 0 < ‖σ‖ * ‖xw.1 q‖ := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have : ‖σ‖ * ‖xw.1 q‖ < ‖σ‖ * t₀ * ‖xw.1 q‖ := by nlinarith
    linarith

end HatRays

end Balaban.Fluctuation
