/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0FRHeavy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRProd`: the product bound of the Mayer weights of route FR (M)

`notes/phase1/KF0-FR.md` (M). With the ordinary bounds (`frEps`: `3(ρ² + Z)` for a site term,
`βρ⁴/2` for a bond term) and the heavy bound `Θ = 8^k e η` (`frHeavy_le`), the marks product bound
(`norm_integral_prod_le_marks`) gives, for every family `C` of terms
(`norm_integral_prod_frF_le`):

`|∫ ∏_{t∈C} (F_t - 1) dμ| ≤ ∏_{t∈C} (1+√Θ)^{|S_t|} (ε_t + Θ^{1/(2k)} |S_t|)`,

and the product `∏_{t∈C} (F_t - 1)` is integrable (`integrable_prod_frF`).
-/

@[expose] public section

open MeasureTheory Set Matrix Balaban.Green Balaban.Polymer
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

open SphereChart

noncomputable section

variable {N : ℕ} (h : EuclideanSpace ℝ (Fin N))

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The ordinary bounds of the terms. -/
def frEps (β ν ρ G θ p : ℝ) : FRTerm d ℓ → ℝ
  | Sum.inl _ => 3 * (ρ ^ 2 + (β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2))
  | Sum.inr _ => β * ρ ^ 4 / 2

omit [NeZero ℓ] in
theorem frEps_nonneg {β ν ρ G θ p : ℝ} (hβ : 0 ≤ β) (hν : 0 ≤ ν) (hρ : 0 ≤ ρ) (hG : 0 ≤ G)
    (hθ : 0 ≤ θ) (t : FRTerm d ℓ) : 0 ≤ frEps β ν ρ G θ p t := by
  rcases t with x | x <;> simp only [frEps] <;> positivity

/-- **The ordinary bounds** (O5) for all terms. -/
theorem frF_ord_le (hh : ‖h‖ = 1) {β ν ε G θ p ρ : ℝ} (hβ : 0 < β) (hν : 0 < ν) (hp : 0 ≤ p)
    (R : ℕ) (g : Torus d ℓ → Fin N → ℂ) (hg : ∀ x, ∑ i, ‖g x i‖ ≤ G)
    (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ)
    (hρ : (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) ≤ ρ) (hρ2 : ρ ≤ 1 / 2)
    (hZ : β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2 ≤ 1) (t : FRTerm d ℓ)
    (ω : Torus d ℓ → perp h × Bool) (hω : ∀ x ∈ frSupp R t, ω x ∈ frOrd h p) :
    ‖frF h hh β ν ε R g t ω - 1‖ ≤ frEps β ν ρ G θ p t := by
  rcases t with x | ⟨x, μ⟩
  · exact norm_frSite_sub_one_le h hh hβ hν hp R g x hρ hρ2 (hQ x) (hg x) hZ hω
  · exact norm_frBond_sub_one_le h hβ.le hν hp R x μ hρ (by linarith) hω

/-- **The product bound of route FR.** -/
theorem norm_integral_prod_frF_le (hh : ‖h‖ = 1) {β ν ε G θ p ρ K₀ Wc η : ℝ}
    (hβ : 0 < β) (hν : 0 < ν) (hε : 0 < ε) (hp : 0 ≤ p) (R : ℕ) (g : Torus d ℓ → Fin N → ℂ)
    (hg : ∀ x, ∑ i, ‖g x i‖ ≤ G) (hQ : ∀ x, ∑ y, |frQ d ℓ ν R x y| ≤ θ)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4)
    (ha : 2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ ≤ p / 8)
    (hK₀ : Real.exp (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹ * p + θ / 2 * p ^ 2) ≤ K₀)
    (hWc : ∫⁻ v, ENNReal.ofReal (chartWeight h v) ≤ ENNReal.ofReal Wc)
    (hJord : (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) * Real.exp (-(β * ν / 128)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ 1)
    (hη1 : 2 * (2 ^ Module.finrank ℝ (perp h) * Real.exp (-p ^ 2 / 8)) +
      2 * Real.exp (-(β * ν / 2) + 2 * G) * (2 ^ Module.finrank ℝ (perp h) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η)
    (hη2 : 2 ^ Module.finrank ℝ (perp h) * Real.exp (-p ^ 2 / 8) +
      ε * (2 ^ Module.finrank ℝ (perp h) *
        Real.exp (2 * (2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2)) ≤ η)
    (hη3 : (2 * Real.pi) ^ (-(Module.finrank ℝ (perp h) : ℝ) / 2) *
      Real.exp ((2 * G * (Real.sqrt β)⁻¹ * (Real.sqrt ν)⁻¹) ^ 2) *
        (Real.exp (-(β * ν / 128)) + Real.exp (-(β * ν / 2) + 2 * G)) *
      (((Real.sqrt β)⁻¹ * ((1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹))⁻¹ ^ (N - 1) *
        Wc) ≤ η)
    (hρ : (Real.sqrt β)⁻¹ * ((Real.sqrt ν)⁻¹ * p) ≤ ρ) (hρ2 : ρ ≤ 1 / 2)
    (hZ : β * ν / 2 * ρ ^ 4 + 2 * G * ρ + θ * p ^ 2 / 2 ≤ 1)
    {k s₁ : ℕ} (hk : 1 ≤ k) (C : Finset (FRTerm d ℓ))
    (hmult : ∀ x, (C.filter (fun t => x ∈ frSupp R t)).card ≤ k)
    (hs₁ : ∀ x : Torus d ℓ, (frSupp R (Sum.inl x)).card ≤ s₁)
    (hK : K₀ ^ (k * s₁) ≤ Real.exp 1) (hΘ1 : 8 ^ k * Real.exp 1 * η ≤ 1) :
    Integrable (fun ω => ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1))
        (Measure.pi fun _ => frSiteMeasure h ε) ∧
    ‖∫ ω, ∏ t ∈ C, (frF h hh β ν ε R g t ω - 1) ∂(Measure.pi fun _ => frSiteMeasure h ε)‖ ≤
      ∏ t ∈ C, ((1 + Real.sqrt (8 ^ k * Real.exp 1 * η)) ^ (frSupp R t).card *
        (frEps β ν ρ G θ p t +
          (8 ^ k * Real.exp 1 * η) ^ ((1 : ℝ) / (2 * k)) * (frSupp R t).card)) := by
  have hG : 0 ≤ G := by
    have : (0 : ℝ) ≤ ∑ i, ‖g 0 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [hg 0]
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hheavy := frHeavy_le h hh hβ hν hε hp R g hg hQ hθ0 hθ ha hK₀ hWc hJord hη1 hη2 hη3 C
    hmult hs₁ hK
  have hfm : ∀ t, Measurable fun ω => frF h hh β ν ε R g t ω - 1 := fun t =>
    (measurable_frF h hh β ν ε R g t).sub_const 1
  have hord : ∀ t (ω : Torus d ℓ → perp h × Bool), (∀ x ∈ frSupp R t, ω x ∈ frOrd h p) →
      ‖frF h hh β ν ε R g t ω - 1‖ ≤ frEps β ν ρ G θ p t := fun t ω hω =>
    frF_ord_le h hh hβ hν hp R g hg hQ hρ hρ2 hZ t ω hω
  have hε0 := frEps_nonneg (d := d) (ℓ := ℓ) hβ.le hν.le hρ0 hG hθ0 (p := p)
  have hprob := isProbabilityMeasure_frSiteMeasure h hε.le
  refine ⟨integrable_prod_of_marks (fun _ => frSiteMeasure h ε) (fun _ => frOrd h p)
    (fun _ => measurableSet_frOrd h p) (frSupp R) (fun t ω => frF h hh β ν ε R g t ω - 1) hfm C
    (frEps β ν ρ G θ p) hε0 hord (fun H _ => hheavy H), ?_⟩
  have hηpos : 0 < η := lt_of_lt_of_le (by positivity) hη2
  exact norm_integral_prod_le_marks (fun _ => frSiteMeasure h ε) (fun _ => frOrd h p)
    (fun _ => measurableSet_frOrd h p) (frSupp R) (fun t ω => frF h hh β ν ε R g t ω - 1) hfm C
    (frEps β ν ρ G θ p) hε0 hord (by positivity) hΘ1 hk hmult (fun H _ => hheavy H)

end

end Balaban.LargeField.KF0FR
