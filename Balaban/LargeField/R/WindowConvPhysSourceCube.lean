/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseCubeBudget
public import Balaban.LargeField.R.CoeffResponseBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Per-cube budgets of one conversion step (P7CONV (38), (52))

For a layer block `Δ_ℓ(x)`, `ℓ ≤ j + 1`, of a region, the coupling-weighted coefficient, spacing
and mass sums are at most the same sums with `L^{(d-2)(j+1)}`; with the coupling flow they are
multiples of `cs.beta (j + 1)`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.SmallField Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- The weighted coefficient sum over a layer block of layer `ℓ ≤ j + 1`. -/
theorem Region.layerBlock_levelCoeff_le (X : Region G) (hd : 2 ≤ d) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) {j : ℕ} (hl : G.layerIndex x ≤ j + 1) (a : ℕ → ℝ) {β₁ B : ℝ}
    (hβ : 0 ≤ β₁) (hB : β₁ * |a (G.layerIndex x)| ≤ B) :
    β₁ * ∑ y ∈ G.blk (G.layerIndex x) x, ‖levelCoeff G a y‖ ≤
      B * (L : ℝ) ^ ((d - 2) * (j + 1)) := by
  rw [X.layerBlock_sum_levelCoeff hx, pow_layer_mul hd]
  have hP : (L : ℝ) ^ (G.layerIndex x * (d - 2)) ≤ (L : ℝ) ^ ((d - 2) * (j + 1)) := by
    apply pow_L_mono
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hl
  calc β₁ * (|a (G.layerIndex x)| * (L : ℝ) ^ (G.layerIndex x * (d - 2)))
      = (β₁ * |a (G.layerIndex x)|) * (L : ℝ) ^ (G.layerIndex x * (d - 2)) := by ring
    _ ≤ B * (L : ℝ) ^ ((d - 2) * (j + 1)) :=
        mul_le_mul hB hP (by positivity) ((mul_nonneg hβ (abs_nonneg _)).trans hB)

/-- The spacing sum over a layer block of layer `ℓ ≤ j + 1`. -/
theorem Region.layerBlock_spacing_le (X : Region G) (hd : 2 ≤ d) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) {j : ℕ} (hl : G.layerIndex x ≤ j + 1) {β₁ : ℝ} (hβ : 0 ≤ β₁) :
    β₁ * ∑ y ∈ G.blk (G.layerIndex x) x, ((G.spacing y) ^ 2)⁻¹ ≤
      β₁ * (L : ℝ) ^ ((d - 2) * (j + 1)) := by
  rw [X.layerBlock_sum_spacing hx]
  have := pow_layer_mul (L := L) hd (G.layerIndex x) 1
  rw [one_div, one_mul] at this
  rw [this]
  have hP : (L : ℝ) ^ (G.layerIndex x * (d - 2)) ≤ (L : ℝ) ^ ((d - 2) * (j + 1)) := by
    apply pow_L_mono
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hl
  exact mul_le_mul_of_nonneg_left hP hβ

/-- The mass sum over a layer block of layer `ℓ ≤ j + 1`, when the mass satisfies
`|ν| (L^ℓ)² ≤ c`. -/
theorem Region.layerBlock_mass_le (X : Region G) (hd : 2 ≤ d) {x : Torus d (N₀ * L ^ K)}
    (hx : x ∈ X.sites) {j : ℕ} (hl : G.layerIndex x ≤ j + 1) {β₁ ν c : ℝ} (hβ : 0 ≤ β₁)
    (hν : |ν| * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ c) :
    β₁ * ∑ _y ∈ G.blk (G.layerIndex x) x, |ν| ≤ β₁ * c * (L : ℝ) ^ ((d - 2) * (j + 1)) := by
  rw [X.layerBlock_sum_const hx]
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hl ⊢
  have hP : (L : ℝ) ^ (G.layerIndex x * e) ≤ (L : ℝ) ^ (e * (j + 1)) := by
    apply pow_L_mono
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hl
  have e1 : ((L : ℝ) ^ G.layerIndex x) ^ (e + 2) * |ν| =
      (|ν| * ((L : ℝ) ^ G.layerIndex x) ^ 2) * (L : ℝ) ^ (G.layerIndex x * e) := by
    have h2 : (L : ℝ) ^ (G.layerIndex x * (e + 2)) =
        ((L : ℝ) ^ G.layerIndex x) ^ 2 * (L : ℝ) ^ (G.layerIndex x * e) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [← pow_mul, h2]; ring
  rw [e1]
  have h0 : 0 ≤ |ν| * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
  calc β₁ * ((|ν| * ((L : ℝ) ^ G.layerIndex x) ^ 2) * (L : ℝ) ^ (G.layerIndex x * e))
      ≤ β₁ * (c * (L : ℝ) ^ (e * (j + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hν hP (by positivity) (h0.trans hν)) hβ
    _ = β₁ * c * (L : ℝ) ^ (e * (j + 1)) := by ring

/-- The coupling-flow arithmetic: `β g_{n-1} P ≤ e^{2η} (β P g_{j+1})`. -/
theorem flow_pow_le {β η g1 gj P : ℝ} (hβ : 0 < β) (hg1 : g1 ≤ Real.exp η)
    (hgj : Real.exp (-η) ≤ gj) (hP : 0 ≤ P) :
    β * g1 * P ≤ Real.exp (2 * η) * (β * P * gj) := by
  have e2 : Real.exp (2 * η) * Real.exp (-η) = Real.exp η := by
    rw [← Real.exp_add]; ring_nf
  calc β * g1 * P ≤ β * Real.exp η * P := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg1 hβ.le) hP
    _ = Real.exp (2 * η) * (β * P * Real.exp (-η)) := by rw [← e2]; ring
    _ ≤ Real.exp (2 * η) * (β * P * gj) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hgj (by positivity)

/-- **The three cube budgets of a conversion step** on a decomposition into layer blocks of weight
one: with `β₁ = β g₁`, `cb = β L^{(d-2)(j+1)} g_j`, `β g_j a(ℓ) = β g₁ a₁(ℓ)`, `|a(ℓ)| ≤ Ka` and
`|ν₁| (L^ℓ)² ≤ cν²`. -/
theorem cube_budgets (X : Region G) (Dc : StepDecomp X) (hd2 : 2 ≤ d) {j : ℕ}
    (hwt1 : ∀ c, Dc.wt c = 1)
    (hcells : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
      G.layerIndex x ≤ j + 1)
    {a₁ aw : ℕ → ℝ} {β g1 gj η Ka cν ν1 cb : ℝ} (hβ : 0 < β) (hg1 : g1 ≤ Real.exp η)
    (hg1p : 0 < g1) (hgj : Real.exp (-η) ≤ gj) (hgj0 : 0 < gj) (hKa : ∀ ℓ, |aw ℓ| ≤ Ka)
    (hca : ∀ ℓ, β * gj * aw ℓ = β * g1 * a₁ ℓ)
    (hν : ∀ x ∈ X.sites, |ν1| * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ cν ^ 2)
    (hcb : cb = β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj) :
    (∀ c, (β * g1) * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a₁ x‖ ≤ (Ka * cb) * Dc.wt c) ∧
    (∀ c, (β * g1) * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤
      (Real.exp (2 * η) * cb) * Dc.wt c) ∧
    (∀ c, (β * g1) * ∑ _x ∈ (Dc.cube c).sites, |ν1| ≤
      (Real.exp (2 * η) * cν ^ 2) * (cb * Dc.wt c)) := by
  have hβ1 : 0 ≤ β * g1 := (mul_pos hβ hg1p).le
  have hP0 : (0 : ℝ) ≤ (L : ℝ) ^ ((d - 2) * (j + 1)) := by positivity
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨x, hx, hs, hl⟩ := hcells c
    rw [hs, hwt1 c, mul_one]
    have hB : (β * g1) * |a₁ (G.layerIndex x)| ≤ β * gj * Ka := by
      have e := hca (G.layerIndex x)
      have e2 : (β * g1) * |a₁ (G.layerIndex x)| = (β * gj) * |aw (G.layerIndex x)| := by
        rw [← abs_of_pos (mul_pos hβ hg1p), ← abs_mul, ← e, abs_mul, abs_of_pos (mul_pos hβ hgj0)]
      rw [e2]
      exact mul_le_mul_of_nonneg_left (hKa _) (mul_pos hβ hgj0).le
    have h1 := X.layerBlock_levelCoeff_le hd2 hx hl a₁ hβ1 hB
    calc _ ≤ _ := h1
      _ = _ := by rw [hcb]; ring
  · obtain ⟨x, hx, hs, hl⟩ := hcells c
    rw [hs, hwt1 c, mul_one]
    have h1 := X.layerBlock_spacing_le hd2 hx hl hβ1
    have h2 := flow_pow_le hβ hg1 hgj hP0
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := by rw [hcb]
  · obtain ⟨x, hx, hs, hl⟩ := hcells c
    rw [hs, hwt1 c, mul_one]
    have h1 := X.layerBlock_mass_le hd2 hx hl hβ1 (hν x hx)
    have h2 := flow_pow_le hβ hg1 hgj (by positivity : 0 ≤ cν ^ 2 * (L : ℝ) ^ ((d - 2) * (j + 1)))
    calc _ ≤ _ := h1
      _ = β * g1 * (cν ^ 2 * (L : ℝ) ^ ((d - 2) * (j + 1))) := by ring
      _ ≤ _ := h2
      _ = _ := by rw [hcb]; ring

end Balaban.LargeField.ActionConv
