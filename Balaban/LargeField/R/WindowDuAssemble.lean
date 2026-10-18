/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuMassTerm
public import Balaban.LargeField.R.WindowConvPhysSwitchLocBudget

/-!
# The mass budget of a piece on the real flow (blocker 4)

`piece_mass_card_le`: `β g_k |ν_k| |X| ≤ C_m A_max |X|_{mix}` for the region `X` of a piece, from the per-cube
budget of the mass term (`switch_cube_budgets`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem piece_mass_card_le (X : Region G) (Dc : StepDecomp X) (hd : 2 ≤ d) {j k : ℕ}
    (hjk : j + 1 ≤ k) (hwt1 : ∀ c, Dc.wt c = 1)
    (hcells : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
      G.layerIndex x ≤ j + 1)
    (a : ℕ → ℝ) {β η gk gj Ka Dδ ε₀ E ν δk Cb Cg Cm Amax : ℝ} (hβ : 0 < β)
    (hgk : gk ≤ Real.exp η) (hgk' : Real.exp (-η) ≤ gk) (hgj : Real.exp (-η) ≤ gj)
    (hε₀ : 0 < ε₀) (hE : ε₀ ^ 2 ≤ E ^ 2)
    (hKa : ∀ ℓ, |a ℓ| ≤ Ka) (hreg : β * |ν| * (L : ℝ) ^ (k * d) ≤ 1) (hδk : |δk| ≤ Dδ)
    (hCb : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (hCg : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (hCm : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
    (hAmax : β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 ≤ Amax) :
    β * gk * |ν * δk| * (X.sites.card : ℝ) ≤ Cm * Amax * Dc.total := by
  have hgk0 : 0 < gk := lt_of_lt_of_le (Real.exp_pos _) hgk'
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hDδ0 : 0 ≤ Dδ := (abs_nonneg _).trans hδk
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hCm0 : 0 ≤ Cm := le_trans (by positivity) hCm
  obtain ⟨-, -, hcm⟩ := switch_cube_budgets X Dc hd hjk hwt1 hcells a hβ hgk hgj hε₀ hE hKa hreg
    hδk hCb hCg hCm
  have hA0 : 0 ≤ β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 := by
    have := lt_of_lt_of_le (Real.exp_pos _) hgj
    positivity
  refine (Dc.card_budget (β := β * gk) (κ := Cm * Amax) (ν * δk) (fun c => ?_))
  refine (hcm c).trans ?_
  rw [hwt1 c, mul_one, mul_one]
  exact mul_le_mul_of_nonneg_left hAmax hCm0

end Balaban.LargeField.ActionConv
