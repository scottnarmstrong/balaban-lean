/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The coefficient read of an action at a fixed field (P7CONV §3.4, (48)–(50))

At one field, mass and datum, the restricted actions at two block coefficients differ only in
the block term, `½ ∑ (a_x - a'_x) r_x · r_x` (the bond and mass terms cancel).  With the
invariant `β̂ (a_i - ak) = β̂_{j+1} a_{j+1} - β̂ ak` of a conversion chain, the difference is
bounded by the two absolute block reads (49).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **Exact coefficient difference of the action** at a fixed field, mass and datum: bond and mass
terms cancel (P7CONV (48)). -/
theorem actionRegionC_coeff_sub (X : Region G) (a a' : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) :
    actionRegionC X a ν Dat φ - actionRegionC X a' ν Dat φ =
      (1 / 2) * ∑ x ∈ X.sites, (levelCoeff G a x - levelCoeff G a' x) *
        ∑ i, (Dat.Ψ x i - blockAvg G φ x i) * (Dat.Ψ x i - blockAvg G φ x i) := by
  unfold actionRegionC Region.blockPair
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- **The coefficient mismatch read**: if `β̂ (a - ak) = β' a₁ - β̂ ak` on every layer, the
difference of the two actions at one field is bounded by
`|β' - β̂| B + β̂ B^{wt}`, with the absolute block reads
`B = ½ ∑ |a₁(x)| |r_x|²`, `B^{wt} = ½ ∑ |a₁(x) - ak(x)| |r_x|²` (P7CONV (49)–(50)). -/
theorem coeff_mismatch_action_le (X : Region G) (a ak a₁ : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) {β β' : ℝ} (hβ : 0 ≤ β)
    (h : ∀ ℓ, β * (a ℓ - ak ℓ) = β' * a₁ ℓ - β * ak ℓ) :
    ‖(β : ℂ) * (actionRegionC X a ν Dat φ - actionRegionC X ak ν Dat φ)‖ ≤
      |β' - β| * ((1 / 2) * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ *
        ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2) +
      β * ((1 / 2) * ∑ x ∈ X.sites, ‖levelCoeff G (a₁ - ak) x‖ *
        ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2) := by
  have hc : ∀ x : Torus d (N₀ * L ^ K), (β : ℂ) * (levelCoeff G a x - levelCoeff G ak x) =
      ((β' - β : ℝ) : ℂ) * levelCoeff G a₁ x + (β : ℂ) * levelCoeff G (a₁ - ak) x := by
    intro x
    unfold levelCoeff
    set D : ℝ := ((L : ℝ) ^ G.layerIndex x) ^ 2
    have e : β * (a (G.layerIndex x) / D - ak (G.layerIndex x) / D) =
        (β' - β) * (a₁ (G.layerIndex x) / D) +
          β * ((a₁ - ak) (G.layerIndex x) / D) := by
      simp only [Pi.sub_apply]
      linear_combination D⁻¹ * h (G.layerIndex x)
    exact_mod_cast e
  set c : Torus d (N₀ * L ^ K) → ℂ := fun x =>
    ((β' - β : ℝ) : ℂ) * levelCoeff G a₁ x + (β : ℂ) * levelCoeff G (a₁ - ak) x with hcdef
  have e : (β : ℂ) * ((1 / 2) * ∑ x ∈ X.sites, (levelCoeff G a x - levelCoeff G ak x) *
        ∑ i, (Dat.Ψ x i - blockAvg G φ x i) * (Dat.Ψ x i - blockAvg G φ x i)) =
      (1 / 2) * ∑ x ∈ X.sites, c x *
        ∑ i, (Dat.Ψ x i - blockAvg G φ x i) * (Dat.Ψ x i - blockAvg G φ x i) := by
    rw [mul_left_comm, Finset.mul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
    rw [← mul_assoc, hcdef]
    simp only []
    rw [← hc x, mul_sub]
  rw [actionRegionC_coeff_sub, e, norm_mul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have hs := weighted_bilinear_self_le X.sites c
    (fun x i => Dat.Ψ x i - blockAvg G φ x i)
  have hcn : ∀ x : Torus d (N₀ * L ^ K), ‖c x‖ ≤
      |β' - β| * ‖levelCoeff G a₁ x‖ + β * ‖levelCoeff G (a₁ - ak) x‖ := fun x => by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
      Real.norm_of_nonneg hβ]
  have hs2 : ∑ x ∈ X.sites, ‖c x‖ * ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 ≤
      |β' - β| * ∑ x ∈ X.sites, ‖levelCoeff G a₁ x‖ * ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 +
      β * ∑ x ∈ X.sites, ‖levelCoeff G (a₁ - ak) x‖ *
        ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have hnn : 0 ≤ ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    have := mul_le_mul_of_nonneg_right (hcn x) hnn
    linarith
  rw [h2]
  nlinarith [hs, hs2]

end Balaban.LargeField.ActionConv
