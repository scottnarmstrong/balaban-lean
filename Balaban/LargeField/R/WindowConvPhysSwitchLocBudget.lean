/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysSwitchLocGen
public import Balaban.LargeField.R.CoeffResponseCubeMain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The per-cube budgets of the switch on layer blocks (the real flow)

For a region decomposed into layer blocks of weight one with layers `ℓ ≤ j + 1 ≤ k`, at the
coupling `β̂_k = β g_k` of the scale `k`, with `A = β L^{(d-2)(j+1)} g_{j+1} E²` (`E ≥ ε₀ > 0`):
`β̂_k ∑ |a(x)| ≤ C_b A`, `β̂_k ∑ ℓ(x)⁻² ≤ C_g A`, `β̂_k ∑ |ν_k| ≤ C_m A` on every cell, for
`C_b ≥ e^{2η} K_a / ε₀²`, `C_g ≥ e^{2η} / ε₀²`, `C_m ≥ e^{2η} D_δ / (β ε₀²)` and the regime
`β |ν| L^{k d} ≤ 1`, `ν_k = ν δ_k`, `|δ_k| ≤ D_δ` (`switch_cube_budgets`).  These are the budgets of
`hcoef` (P7 p. 500 (2.11)) read at the coefficients of the switch.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- **The three per-cube budgets of the switch.** -/
theorem switch_cube_budgetsP (X : Region G) (Dc : StepDecomp X) (hd : 2 ≤ d) {j k : ℕ}
    (hjk : j + 1 ≤ k) (hwt1 : ∀ c, Dc.wt c = 1)
    (hcells : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
      G.layerIndex x ≤ j + 1)
    (a : ℕ → ℝ) {β η gk gj Ka ε₀ E ν δk Cb Cg Cm : ℝ} (hβ : 0 < β)
    (hgk : gk ≤ Real.exp η) (hgj : Real.exp (-η) ≤ gj) (hε₀ : 0 < ε₀) (hE : ε₀ ^ 2 ≤ E ^ 2)
    (hKa : ∀ ℓ, |a ℓ| ≤ Ka)
    (hCb : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (hCg : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (hCm0 : 0 ≤ Cm)
    (hCm : β * Real.exp η * (((L : ℝ) ^ (j + 1)) ^ d * (|ν| * |δk|)) ≤
      Cm * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2)) :
    (∀ c, β * gk * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a x‖ ≤
      Cb * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 * Dc.wt c)) ∧
    (∀ c, β * gk * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤
      Cg * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 * Dc.wt c)) ∧
    (∀ c, β * gk * ∑ _x ∈ (Dc.cube c).sites, |ν * δk| ≤
      Cm * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 * Dc.wt c)) := by
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hgj0 : 0 < gj := lt_of_lt_of_le (Real.exp_pos _) hgj
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hA0 : 0 ≤ β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 := by positivity
  have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb
  have hCg0 : 0 ≤ Cg := le_trans (by positivity) hCg
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨x, hx, hs, hl⟩ := hcells c
    rw [hs, X.layerBlock_sum_levelCoeff hx, pow_layer_mul hd, hwt1, mul_one]
    calc β * gk * (|a (G.layerIndex x)| * (L : ℝ) ^ (G.layerIndex x * (d - 2)))
        ≤ (Real.exp (2 * η) * |a (G.layerIndex x)| / ε₀ ^ 2) *
          (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2) :=
          cube_budget_core hβ hgk hgj (abs_nonneg _) hε2 hE hl
      _ ≤ Cb * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hA0
          refine le_trans ?_ hCb
          gcongr
          exact hKa _
  · obtain ⟨x, hx, hs, hl⟩ := hcells c
    have hp := pow_layer_mul (L := L) hd (G.layerIndex x) 1
    rw [one_div] at hp
    rw [hs, X.layerBlock_sum_spacing hx, hp, hwt1, mul_one]
    have := cube_budget_core (L := L) (d := d) hβ hgk hgj (X := 1) (by norm_num) hε2 hE hl
    calc β * gk * (1 * (L : ℝ) ^ (G.layerIndex x * (d - 2)))
        ≤ (Real.exp (2 * η) * 1 / ε₀ ^ 2) * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2) :=
          this
      _ ≤ Cg * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hA0
          rw [mul_one]; exact hCg
  · obtain ⟨x, hx, hs, hl⟩ := hcells c
    rw [hs, X.layerBlock_sum_const hx, hwt1, mul_one, abs_mul]
    set ℓ := G.layerIndex x
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
    have hLk : ((L : ℝ) ^ ℓ) ^ d ≤ ((L : ℝ) ^ (j + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hl) d
    have hgk0 : 0 ≤ gk ∨ gk < 0 := le_or_gt 0 gk
    have hstep : β * gk * (((L : ℝ) ^ ℓ) ^ d * (|ν| * |δk|)) ≤
        β * Real.exp η * (((L : ℝ) ^ (j + 1)) ^ d * (|ν| * |δk|)) := by
      rcases hgk0 with hg | hg
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hgk hβ.le)
          (mul_le_mul_of_nonneg_right hLk (by positivity)) (by positivity) (by positivity)
      · have h1 : β * gk * (((L : ℝ) ^ ℓ) ^ d * (|ν| * |δk|)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hβ.le hg.le)
            (by positivity)
        have h2 : 0 ≤ β * Real.exp η * (((L : ℝ) ^ (j + 1)) ^ d * (|ν| * |δk|)) := by positivity
        linarith
    exact hstep.trans (by simpa using hCm)

/-- **The three per-cube budgets of the switch.** -/
theorem switch_cube_budgets (X : Region G) (Dc : StepDecomp X) (hd : 2 ≤ d) {j k : ℕ}
    (hjk : j + 1 ≤ k) (hwt1 : ∀ c, Dc.wt c = 1)
    (hcells : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
      G.layerIndex x ≤ j + 1)
    (a : ℕ → ℝ) {β η gk gj Ka Dδ ε₀ E ν δk Cb Cg Cm : ℝ} (hβ : 0 < β)
    (hgk : gk ≤ Real.exp η) (hgj : Real.exp (-η) ≤ gj) (hε₀ : 0 < ε₀) (hE : ε₀ ^ 2 ≤ E ^ 2)
    (hKa : ∀ ℓ, |a ℓ| ≤ Ka) (hreg : β * |ν| * (L : ℝ) ^ (k * d) ≤ 1) (hδk : |δk| ≤ Dδ)
    (hCb : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (hCg : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (hCm : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm) :
    (∀ c, β * gk * ∑ x ∈ (Dc.cube c).sites, ‖levelCoeff G a x‖ ≤
      Cb * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 * Dc.wt c)) ∧
    (∀ c, β * gk * ∑ x ∈ (Dc.cube c).sites, ((G.spacing x) ^ 2)⁻¹ ≤
      Cg * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 * Dc.wt c)) ∧
    (∀ c, β * gk * ∑ _x ∈ (Dc.cube c).sites, |ν * δk| ≤
      Cm * (β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 * Dc.wt c)) := by
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hDδ0 : 0 ≤ Dδ := (abs_nonneg _).trans hδk
  have hgj0 : 0 < gj := lt_of_lt_of_le (Real.exp_pos _) hgj
  have hCm0 : 0 ≤ Cm := le_trans (by positivity) hCm
  exact switch_cube_budgetsP X Dc hd hjk hwt1 hcells a hβ hgk hgj hε₀ hE hKa hCb hCg hCm0
    (mass_budget_of_regime hβ hjk hε₀ hE hgj hreg hδk hCm)

end Balaban.LargeField.ActionConv
