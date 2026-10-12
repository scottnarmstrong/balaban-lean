/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseScale
public import Balaban.Localization.CubeFoldPoisson

/-!
# The pointwise cut estimate at a mixed physical wall: scale arithmetic (VMOD-9 §3, (3.1))

`cut_scale_abs`: the geometric proof of `PointwiseScale.scale_abs` for a layer `j`, a source scale
`j'` and a separation, without the bundled `PtSetting` (and so without the uncut operator).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **VMOD-9 (3.1).** The scale mismatch `bd^{j'}` of the source block is absorbed by the layer
separation. -/
theorem cut_scale_abs {G : GeneratingSet d L N₀ k ϱ} (hd : 0 < d) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) {j j' : ℕ} (hj1 : 1 ≤ j)
    (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x y') :
    ∃ t₂ : ℝ, t ≤ t₂ ∧ ENNReal.ofReal t₂ ≤ G.pathDist x y' ∧
      bd d L ^ j' * Real.exp (-(agmonRate d * t₂)) ≤
        bd d L ^ j * bd d L * Real.exp (-(agmonRate d / 2 * t)) := by
  have hε0 := agmonRate_pos hd
  have hb1 := one_le_bd (d := d) (L := L)
  have hb0 : 0 < bd d L := by linarith
  rcases le_or_gt j' j with h | h
  · refine ⟨t, le_rfl, ht, ?_⟩
    have h1 : bd d L ^ j' ≤ bd d L ^ j := pow_le_pow_right₀ hb1 h
    have h2 : Real.exp (-(agmonRate d * t)) ≤ Real.exp (-(agmonRate d / 2 * t)) := by
      apply Real.exp_le_exp.2
      nlinarith
    calc bd d L ^ j' * Real.exp (-(agmonRate d * t)) ≤ bd d L ^ j *
          Real.exp (-(agmonRate d / 2 * t)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ ≤ _ := by
          rw [mul_assoc, mul_comm (bd d L) _, ← mul_assoc]
          have : 0 ≤ bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) := by positivity
          nlinarith
  · have hsep0 := G.pathDist_separation_le hϱ hj1 hj'k hx (G.mem_layer.1 hy').1
    set s0 : ℝ := (ϱ - 1) * ((j' - j - 1 : ℕ) : ℝ) with hs0
    have hs00 : 0 ≤ s0 := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    refine ⟨max t s0, le_max_left _ _, ?_, ?_⟩
    · rcases le_total t s0 with h' | h'
      · rw [max_eq_right h']; exact hsep0
      · rw [max_eq_left h']; exact ht
    · set m := j' - j with hm
      have hjm : j' = j + m := by omega
      have hexp : Real.exp (-(agmonRate d * max t s0)) ≤
          Real.exp (-(agmonRate d / 2 * t)) * Real.exp (-(agmonRate d / 2 * s0)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : t ≤ max t s0 := le_max_left _ _
        have h2 : s0 ≤ max t s0 := le_max_right _ _
        nlinarith
      have hc : bd d L ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) :=
        (bd_le d).trans hsep
      have habs := pow_mul_exp_le' hb1 hc m
      have e : agmonRate d / 2 * s0 = agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ) := by
        rw [hs0]; ring
      rw [e] at hexp
      calc bd d L ^ j' * Real.exp (-(agmonRate d * max t s0))
          ≤ bd d L ^ (j + m) * (Real.exp (-(agmonRate d / 2 * t)) *
            Real.exp (-(agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
            rw [hjm]; exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) *
            (bd d L ^ m * Real.exp (-(agmonRate d / 2 * (ϱ - 1) * ((m - 1 : ℕ) : ℝ)))) := by
            rw [pow_add]; ring
        _ ≤ bd d L ^ j * Real.exp (-(agmonRate d / 2 * t)) * bd d L :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = _ := by ring

end Balaban.Localization
