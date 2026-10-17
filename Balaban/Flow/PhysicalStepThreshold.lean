/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.Flow.RGInfty
import Mathlib.Tactic.Positivity

/-!
# Numerical closing condition for a physical RG step

The explicit large-coupling threshold in P4 (5.27), (5.29) implies the numerical
contraction condition used by `rg_step_infty`. The decay estimate (5.29) remains
an explicitly named input.
-/

@[expose] public section

namespace Balaban.Flow

open Metric Set

/-- The bound `β ≥ 1344 B max(84κ,1/c₁₀)/α₀²` closes the numerical condition
of `rg_step_infty`, provided the physical forcing satisfies (5.29). -/
theorem physical_step_contraction_condition {B α₀ β q κ η c₁₀ : ℝ} {k : ℕ}
    (hB : 0 ≤ B) (hα : 0 < α₀) (hβ : 0 < β) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc : 0 < c₁₀)
    (hηbd : η ≤ B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (k + 1))))
    (hlarge : 1344 * B * max (84 * κ) (1 / c₁₀) / α₀ ^ 2 ≤ β) :
    16 * (42 * η) * max (2 * (42 * κ)) (1 / c₁₀) ≤ 1 := by
  have hM : 0 ≤ max (84 * κ) (1 / c₁₀) :=
    le_trans (by positivity) (le_max_right _ _)
  have hq : q ^ (k + 1) ≤ 1 := pow_le_one₀ hq0 hq1
  have hη' : η ≤ B * (2 / α₀ ^ 2 * β⁻¹) := by
    calc
      η ≤ B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (k + 1))) := hηbd
      _ ≤ B * (2 / α₀ ^ 2 * β⁻¹) := by
        calc
          B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (k + 1))) =
              (B * (2 / α₀ ^ 2 * β⁻¹)) * q ^ (k + 1) := by ring
          _ ≤ (B * (2 / α₀ ^ 2 * β⁻¹)) * 1 :=
            mul_le_mul_of_nonneg_left hq (by positivity)
          _ = B * (2 / α₀ ^ 2 * β⁻¹) := by ring
  have htop : 1344 * B * max (84 * κ) (1 / c₁₀) / α₀ ^ 2 / β ≤ 1 :=
    (div_le_iff₀ hβ).2 (by simpa using hlarge)
  calc
    16 * (42 * η) * max (2 * (42 * κ)) (1 / c₁₀) =
        672 * η * max (84 * κ) (1 / c₁₀) := by ring_nf
    _ ≤ 672 * (B * (2 / α₀ ^ 2 * β⁻¹)) * max (84 * κ) (1 / c₁₀) := by gcongr
    _ = 1344 * B * max (84 * κ) (1 / c₁₀) / α₀ ^ 2 / β := by
      rw [inv_eq_one_div]
      ring
    _ ≤ 1 := htop

/-- The one-step physical coefficient solution under the explicit coupling
threshold. All analytic, matrix, symmetry, and forcing estimates are retained
as named hypotheses; only the numerical contraction premise is discharged. -/
theorem physical_rg_step_of_large_beta {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {A : G → Matrix (Fin 3) (Fin 3) ℂ} {ε : ℝ} {P : Set G}
    (hP : IsOpen P) (hAan : ∀ i j, AnalyticOnNhd ℂ (fun p => A p i j) P)
    (hA : ∀ p ∈ P, TriangularBounds (A p) ε) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)} {κ η c₁₀ : ℝ}
    (hκ : 0 < κ) (hη : 0 ≤ η) (hc₁₀ : 0 < c₁₀)
    (hc : AnalyticOnNhd ℂ c (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hcb : ∀ p ∈ P, ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ c₁₀ → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ ≤ ε' → ‖c (ξ, p)‖ ≤ κ * ε' ^ 2)
    (hfb : ∀ p ∈ P, ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ c₁₀ → ‖f (ξ, p)‖ ≤ η)
    {B α₀ β q : ℝ} {k : ℕ} (hB : 0 ≤ B) (hα : 0 < α₀) (hβ : 0 < β)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hηbd : η ≤ B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (k + 1))))
    (hlarge : 1344 * B * max (84 * κ) (1 / c₁₀) / α₀ ^ 2 ≤ β)
    {σ : G → G} (hσP : ∀ p ∈ P, σ p ∈ P)
    (hAσ : ∀ p ∈ P, A (σ p) = (A p).map (starRingEnd ℂ))
    (hcσ : ∀ p ∈ P, ∀ ξ, c (conjVec ξ, σ p) = conjVec (c (ξ, p)))
    (hfσ : ∀ p ∈ P, ∀ ξ, f (conjVec ξ, σ p) = conjVec (f (ξ, p))) :
    ∃ ξs : G → (Fin 3 → ℂ),
      (∀ p ∈ P, ‖ξs p‖ ≤ rgRadius (42 * κ) c₁₀ ∧
        (A p).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
        (∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ rgRadius (42 * κ) c₁₀ →
          (A p).mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p) ∧
        ‖ξs p‖ ≤ rgCxi B α₀ * (β⁻¹ * q ^ (k + 1)) ∧
        (σ p = p → ∀ i, (ξs p i).im = 0)) ∧
      AnalyticOnNhd ℂ ξs P := by
  exact rg_step_infty hP hAan hA hε0 hε1 hκ hη hc₁₀
    (physical_step_contraction_condition hB hα hβ hq0 hq1 hc₁₀ hηbd hlarge)
    hc hf hcb hfb hηbd hσP hAσ hcσ hfσ

end Balaban.Flow
