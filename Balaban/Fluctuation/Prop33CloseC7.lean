/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionLevelPair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The smallness `c₇ ≤ thm73C3` of Proposition 3.3 is satisfiable (W136b)

`hc7 : c7 d L N BG κ ≤ thm73C3 d L N` is a smallness condition on the constants `(B_G, κ)` of the
decoupled Green family: `c₇ ≤ δ_close / (2 C₃) ≤ δ_*'(B) ≤ τ'(B) / 3 = 1 / (45 A (B + 1)²)`, with
`B = 1 + L b + 4 L b / γ₁`, `b = B_G e^{N₀ κ}`.  So for `B_G ≥ 1` it holds for every large `κ`;
the constants of `interaction_levelPair_witness` can be taken with `κ` as large as desired.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation

section C7

variable {d L N : ℕ} [NeZero L]

theorem thm73C3_pos (hd : 0 < d) : 0 < thm73C3 d L N := by
  have h1 := bgC1_pos' (d := d) (L := L) (N := N) hd
  have h2 := bgK1_pos (d := d) (L := L) (N := N)
  have h3 := smallnessConst_nonneg hd
  have h4 := sandwichConst_nonneg d L N
  have h5 := deltaStar_pos (d := d) (L := L) (N := N) hd
  have h6 := compC4_ge d
  have hC : 0 < compC4 d := by linarith
  have hK : 0 < bgK1 d L N ^ 2 := by positivity
  have hb2 : 0 < bgC2 d L N := by
    unfold bgC2
    exact lt_min h1 (by positivity)
  unfold thm73C3 thm73C2
  exact lt_min (by positivity) (by positivity)

/-- `c₇` is small as soon as `B_G ≥ 1` and `κ` is large. -/
theorem c7_le_of_large (hd : 0 < d) {BG κ T : ℝ} (hBG : 1 ≤ BG) (hT : 0 < T)
    (hκ : 1 / T ≤ κ) : c7 d L N BG κ ≤ T := by
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκ
  have hB0 : 0 ≤ famConst d L BG κ := by
    have := famConst_ge_one (L := L) (by linarith : 0 ≤ BG) κ hd; linarith
  set B := famConst d L BG κ with hBdef
  -- `κ ≤ B`
  have hN0 : (1 : ℝ) ≤ (N0 d L : ℝ) := by
    have : 1 ≤ N0 d L := by
      unfold N0
      have : 0 < (8 * L) ^ d := pow_pos (by have := NeZero.pos L; omega) _
      omega
    exact_mod_cast this
  have hexp : κ ≤ Real.exp ((N0 d L : ℝ) * κ) := by
    have := Real.add_one_le_exp ((N0 d L : ℝ) * κ)
    nlinarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
  have hγ := gamma1_pos hd
  have hκB : κ ≤ B := by
    have hb : κ ≤ BG * Real.exp ((N0 d L : ℝ) * κ) := by nlinarith [Real.exp_pos ((N0 d L : ℝ) * κ)]
    have hb0 : 0 ≤ BG * Real.exp ((N0 d L : ℝ) * κ) := by positivity
    have h3 : 0 ≤ (L : ℝ) * (4 * (BG * Real.exp ((N0 d L : ℝ) * κ)) / gamma1 d) := by positivity
    have h4 : BG * Real.exp ((N0 d L : ℝ) * κ) ≤ (L : ℝ) * (BG * Real.exp ((N0 d L : ℝ) * κ)) := by
      nlinarith
    rw [hBdef]; unfold famConst
    linarith
  -- chain
  have hL53 : 1 ≤ lemma53Const d L := by
    have h1 := cB7_pos d L
    unfold lemma53Const
    exact le_trans (by linarith) (le_max_right _ _)
  have hL53p : 0 < lemma53Const d L := by linarith
  have hc7 : c7 d L N BG κ ≤ deltaClose d L N BG κ / (2 * lemma53Const d L) := by
    unfold c7
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdc : deltaClose d L N BG κ ≤ cTau' d L N B / 3 := by
    unfold deltaClose
    exact (min_le_left _ _).trans (by
      unfold deltaStar'
      exact (min_le_left _ _).trans (min_le_left _ _))
  have hdc0 : 0 ≤ deltaClose d L N BG κ := (deltaClose_pos (d := d) (L := L) (N := N) hd
    (by linarith)).le
  have hA := Balaban.Background.cA_ge d L N
  have hτ : cTau' d L N B / 3 ≤ T := by
    unfold cTau'
    have h1 : 1 / T ≤ B + 1 := by linarith
    have hB1 : (1 : ℝ) ≤ (B + 1) ^ 2 := by nlinarith
    have h2 : 1 / (15 * cA d L N * (B + 1) ^ 2) / 3 ≤ 1 / (B + 1) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ cA d L N - 1) (by linarith : (0:ℝ) ≤ B)]
    refine h2.trans ?_
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hT] at h1
    nlinarith
  calc c7 d L N BG κ ≤ deltaClose d L N BG κ / (2 * lemma53Const d L) := hc7
    _ ≤ deltaClose d L N BG κ := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
    _ ≤ T := hdc.trans hτ

/-- **`hc7` is satisfiable**: for `B_G ≥ 1` and `κ ≥ 1 / thm73C3`,
`c₇ ≤ thm73C3`. -/
theorem c7_le_thm73C3_of_large (hd : 0 < d) {BG κ : ℝ} (hBG : 1 ≤ BG)
    (hκ : 1 / thm73C3 d L N ≤ κ) : c7 d L N BG κ ≤ thm73C3 d L N :=
  c7_le_of_large hd hBG (thm73C3_pos hd) hκ

end C7

end Balaban.Localization
