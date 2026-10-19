/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0HaloAffine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `KF0SmallUniform`: the majorants of the all-plus pieces are small, uniformly in the torus

For the cutoff `p = log β` the radius `ρ = kf0Rho d g γ κ p β` of the walk expansion tends to `0`
(F.13); `kf0_small_uniform` collects, for one `ε > 0`, a single `β₁` (depending only on
`d, n, g, γ, κ, ε`, not on the torus, the source or the basis) after which `ρ ≤ 1`,
`n ρ² ≤ 1/4` and the three majorants `n² (ρ² + β ρ⁴)` (site pieces without source),
`2 n² β ρ⁴` (bond pieces) and `n ρ² + n ρ` (source pieces) are at most `ε`. The landed
`f1_weighted_small` gives such a `β₁` for one torus at a time.
-/

@[expose] public section

open Finset Filter Balaban.Green Balaban.LargeField Balaban.LargeField.KF0F1 Balaban.LargeField.KF0Taylor

namespace Balaban.LargeField.KF0AllPlus

/-- **Smallness of the weighted norms, uniform in the torus (F.13).**  For `d`, `n ≥ 1` and the
regime constants `g, γ, κ` of the walk expansion, and every `ε > 0` there is `β₁` such that for all
`β ≥ β₁` (cutoff `p = log β`), with `ρ = kf0Rho d g γ κ p β`: `ρ ≤ 1`, `n ρ² ≤ 1/4`, and the three
majorants of the site pieces without source, of the bond pieces and of the source pieces
(`n² (ρ² + β ρ⁴)`, `2 n² β ρ⁴`, `n ρ² + n ρ`) are at most `ε`. -/
theorem kf0_small_uniform {d n : ℕ} {g γ κ ε : ℝ} (hg : 0 < g)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hε : 0 < ε) :
    ∃ β₁ : ℝ, ∀ β ≥ β₁, 0 < β ∧ 0 < Real.log β ∧ kf0Rho d g γ κ (Real.log β) β ≤ 1 ∧
      (n : ℝ) * kf0Rho d g γ κ (Real.log β) β ^ 2 ≤ 1 / 4 ∧
      (n : ℝ) ^ 2 * (kf0Rho d g γ κ (Real.log β) β ^ 2 + β * kf0Rho d g γ κ (Real.log β) β ^ 4) ≤ ε ∧
      2 * (n : ℝ) ^ 2 * (β * kf0Rho d g γ κ (Real.log β) β ^ 4) ≤ ε ∧
      (n : ℝ) * kf0Rho d g γ κ (Real.log β) β ^ 2 + (n : ℝ) * kf0Rho d g γ κ (Real.log β) β ≤ ε := by
  set θ : ℝ := Real.exp (κ * 3 ^ d) with hθ
  set A : ℝ := kf0WalkA d g γ with hA
  have hθpos : 0 < θ := Real.exp_pos _
  have hApos : 0 < A := kf0WalkA_pos (d := d) hg hq
  have hc : 0 < θ * 1 * A := by positivity
  have hρeq : ∀ β : ℝ, kf0Rho d g γ κ (Real.log β) β = rhoBeta θ 1 A 1 β := by
    intro β; unfold kf0Rho rhoBeta; simp only [mul_one, one_mul]; rw [hθ, hA]; ring
  obtain ⟨β₂, hβ₂⟩ := eventually_atTop.1 (((rhoBeta_eventually_small hc one_pos n).and
    (eventually_gt_atTop 1)).and (eventually_gt_atTop 0))
  obtain ⟨β₃, hβ₃⟩ := smallness_eps one_pos 0 ((n : ℝ) ^ 2 * (θ * 1 * A) ^ 2)
    ((n : ℝ) ^ 2 * (θ * 1 * A) ^ 4) hε
  obtain ⟨β₄, hβ₄⟩ := smallness_eps one_pos 0 0 (2 * (n : ℝ) ^ 2 * (θ * 1 * A) ^ 4) hε
  obtain ⟨β₅, hβ₅⟩ := smallness_eps one_pos ((n : ℝ) * (θ * 1 * A))
    ((n : ℝ) * (θ * 1 * A) ^ 2) 0 hε
  refine ⟨max β₂ (max β₃ (max β₄ β₅)), fun β hβ => ?_⟩
  have h2 := hβ₂ β (le_trans (le_max_left _ _) hβ)
  have h3 := hβ₃ β (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hβ)
  have h4 := hβ₄ β (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_right _ _))) hβ)
  have h5 := hβ₅ β (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_right _ _))) hβ)
  obtain ⟨⟨⟨hρ0, hρ1, hρ⟩, hβ1⟩, hβ0⟩ := h2
  have hlog : 0 < Real.log β := Real.log_pos hβ1
  rw [hρeq]
  have hlg : Real.log (β * 1) = Real.log β := by rw [mul_one]
  have hsq : rhoBeta θ 1 A 1 β ^ 2 = (θ * 1 * A) ^ 2 * (Real.log (β * 1) ^ 2 / β) := by
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 < t ∧ β = t ^ 2 :=
      ⟨Real.sqrt β, Real.sqrt_pos.2 hβ0, (Real.sq_sqrt hβ0.le).symm⟩
    simp only [rhoBeta, Real.sqrt_sq ht.le]
    field_simp
  have hlin : rhoBeta θ 1 A 1 β = (θ * 1 * A) * (Real.log (β * 1) / Real.sqrt β) := by
    unfold rhoBeta; ring
  refine ⟨hβ0, hlog, hρ1, hρ, ?_, ?_, ?_⟩
  · have e1 := site_bound_rhoBeta θ 1 A 1 0 β hβ0
    simp only [hlg, zero_mul, zero_add] at e1 h3
    have h3' := (abs_lt.1 h3).2
    nlinarith [h3', e1, sq_nonneg (n : ℝ)]
  · have e1 := bond_bound_rhoBeta θ 1 A 1 β hβ0
    simp only [hlg, zero_mul, zero_add] at e1 h4
    have h4' := (abs_lt.1 h4).2
    rw [e1]
    linarith
  · simp only [hlg, zero_mul, add_zero] at h5
    have h5' := (abs_lt.1 h5).2
    rw [hsq, hlin]
    simp only [hlg]
    linarith

end Balaban.LargeField.KF0AllPlus
