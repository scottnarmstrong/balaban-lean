/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBudget
public import Balaban.LargeField.R.CoeffResponseBudgetCount
public import Balaban.LargeField.R.CoeffResponseReads
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The unprimed read budgets of one conversion step (P7CONV (38))

The block, bond and mass energies of a background `φ` whose reads are bounded pointwise by
`4 ε²` (block, bond) and `12 ε² ℓ⁻²` (mass), on a region with a cube decomposition: each energy is
at most the pointwise bound times the cube budget times the mixed count.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Balaban.SmallField Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **The mass energy from the pointwise bound `|ν| |s|² ≤ B ℓ⁻²`.** -/
theorem Region.massRead_energy_le {X : Region G} (Dc : StepDecomp X) (f : Torus d (N₀ * L ^ K) → ℝ)
    {B κ β : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hf : ∀ x ∈ X.sites, f x ≤ B * ((G.spacing x) ^ 2)⁻¹)
    (hcube : ∀ c, β * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤ κ * Dc.wt c) :
    β * ∑ x ∈ X.sites, f x ≤ B * (κ * Dc.total) := by
  have h1 : ∑ x ∈ X.sites, f x ≤ ∑ x ∈ X.sites, B * ((G.spacing x) ^ 2)⁻¹ :=
    Finset.sum_le_sum hf
  have h2 : β * ∑ x ∈ X.sites, ((G.spacing x) ^ 2)⁻¹ ≤ κ * Dc.total := by
    have := Dc.sum_sites_le (fun x => β * ((G.spacing x) ^ 2)⁻¹) (κ := κ) (fun c => by
      rw [← Finset.mul_sum]; exact hcube c)
    rwa [← Finset.mul_sum] at this
  calc β * ∑ x ∈ X.sites, f x ≤ β * ∑ x ∈ X.sites, B * ((G.spacing x) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 hβ
    _ = B * (β * ∑ x ∈ X.sites, ((G.spacing x) ^ 2)⁻¹) := by rw [← Finset.mul_sum]; ring
    _ ≤ B * (κ * Dc.total) := mul_le_mul_of_nonneg_left h2 hB

/-- The mass read at the background with the spacing: `ν ℓ(x)² ∑ᵢ |s̃(φ⁰)ᵢ − hᵢ|² ≤ 4 ε²`. -/
theorem massRead_spacing_le {a : ℕ → ℝ} {ν ε : ℝ} (H : BgHyp d L K ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOneReal G a ν ε D) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1) :
    ν * G.spacing x ^ 2 * ∑ j, ‖svec G (bgFieldC G a ν (bgC0 d L N) D) x j - D.h x j‖ ^ 2 ≤
      4 * ε ^ 2 := by
  have h := (XiCOneReal.factors H hε hsm hc1 hD).2.2.1 x hx
  rwa [vn_sq] at h

end Balaban.LargeField.ActionConv
