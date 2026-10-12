/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The decay-rate arithmetic of one step with direct labels

`notes/phase1/TRUE-LOCAL.md` §4, formulas (6)-(8): the positive counterpart of
`stepRates_no_closure_landed` (`StepRates.lean:122`).  The rate fields are the landed ones quoted
in the module doc of `StepRates.lean`:
(i) `κ_dec - 1 ≤ κ_in` (`InteractionHatAssemble.lean:189`), (iii) `StepActivityBound.hκ`
(`StepNonvanishBound.lean:76`), (iv) `thm31b_of_input`'s `hκb` (`Thm31b.lean:304`).

If the expansion terms are labelled by their own domain `Y` (identity labels), the label
conversion is the identity and `κ_H = 2 κ_dec - 1`, instead of the landed
`hatKappaH d L (2 κ_dec - 1) = (2 κ_dec - 1)/hatA d L - c₁`.

* `stepRates_direct_closure`, `stepRates_direct_iff`: abstract arithmetic with `κ_H = 2 κ_dec - 1`;
  the class rate is preserved (`κ_in ≤ κ_out`) iff `4 κ₀ + c + 3/2 ≤ κ_in`.
* `stepRates_direct_witness`: the numerical fields of `stepRates_trace_witness` at `d = L = 3`,
  with `κ_H = 2 κ_dec - 1`, `κ_dec - 1 ≤ κ_in ≤ κ_out`.
* `stepRates_landed_impossible`: the landed conversion admits no such rates.

The physical expansion terms are not yet shown to satisfy the direct-label input (the open
physical locality theorem of `TRUE-LOCAL.md`); this file is unconditional arithmetic.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban

/-- **T1.**  With `κ_H = 2 κ_dec - 1`, the landed fields (i) `κ_dec - 1 ≤ κ_in`, (iii)
`κ' + (3 κ₀ + c + 3/2) ≤ κ_H` and (iv) `κ_out ≤ κ' - κ₀ - 1` give
`κ_out ≤ 2 κ_in - (4 κ₀ + c + 3/2)`. -/
theorem stepRates_direct_bound {κ0 c κin κdec κH κ' κout : ℝ} (hH : κH = 2 * κdec - 1)
    (h1 : κdec - 1 ≤ κin) (h3 : κ' + (3 * κ0 + c + 3 / 2) ≤ κH) (h4 : κout ≤ κ' - κ0 - 1) :
    κout ≤ 2 * κin - (4 * κ0 + c + 3 / 2) := by
  subst hH; linarith

/-- **T1, characterization.**  For `κ_H = 2 κ_dec - 1` the fields (i), (iii), (iv) (with
`κ' ≤ κ_h`) admit `κ_in ≤ κ_out` if and only if `4 κ₀ + c + 3/2 ≤ κ_in`; the largest achievable
`κ_out` is `2 κ_in - (4 κ₀ + c + 3/2)`. -/
theorem stepRates_direct_iff (κ0 c κin : ℝ) :
    (∃ κdec κH κ' κh κout : ℝ, κH = 2 * κdec - 1 ∧ κdec - 1 ≤ κin ∧
      κ' + (3 * κ0 + c + 3 / 2) ≤ κH ∧ κ' ≤ κh ∧ κout ≤ min κh κ' - κ0 - 1 ∧ κin ≤ κout) ↔
      4 * κ0 + c + 3 / 2 ≤ κin := by
  constructor
  · rintro ⟨κdec, κH, κ', κh, κout, hH, h1, h3, hh, h4, h5⟩
    have : min κh κ' = κ' := min_eq_right hh
    rw [this] at h4
    have := stepRates_direct_bound hH h1 h3 h4
    linarith
  · intro h
    refine ⟨κin + 1, 2 * (κin + 1) - 1, 2 * κin - 3 * κ0 - c - 1 / 2,
      2 * κin - 3 * κ0 - c - 1 / 2, 2 * κin - (4 * κ0 + c + 3 / 2), rfl, by linarith,
      by linarith, le_rfl, ?_, by linarith⟩
    rw [min_self]; linarith

/-- **T1, the explicit choice.**  The choices (8) of `TRUE-LOCAL.md` with general `κ₀, c ≥ 0`. -/
theorem stepRates_direct_closure {κ0 c κin κdec κH κ' κout : ℝ} (hκ0 : 0 ≤ κ0) (hc : 0 ≤ c)
    (hdec : 2 * (4 * κ0 + c + 7 / 2) ≤ κdec) (hH : κH = 2 * κdec - 1) (hin : κin = κdec)
    (hk' : κ' = 3 / 2 * κdec + κ0 + 1) (hout : κout = 3 / 2 * κdec) :
    κdec - 1 ≤ κin ∧ κ' + (3 * κ0 + c + 3 / 2) ≤ κH ∧ κout ≤ min κ' κ' - κ0 - 1 ∧
      κ' ≤ κ' ∧ κin ≤ κout := by
  subst hH hin hk' hout
  refine ⟨by linarith, by linarith, ?_, le_rfl, by linarith⟩
  rw [min_self]; linarith

/-- **T2.**  At `d = L = 3`, the numerical fields of `stepRates_trace_witness (m₀)` with direct
labels: `κ_H = 2 κ_dec - 1` replaces `hatKappaH 3 3 (2 κdec - 1) = κH`, the field
`κdec - 1 ≤ κin` replaces `κin < κdec - 1`, and `κin ≤ κout ≤ min κh κ' - κ0 - 1` is added.
Values: `κ₀ = a_Ent + 1`, `κdec = 100 (κ₀ + c₁ + 10)`, `κin = κdec`, `κ_H = κ_G = 2κdec - 1`,
`κ' = κ_h = κ_det = 3/2 κdec + κ₀ + 1`, `κout = 3/2 κdec`. -/
theorem stepRates_direct_witness (m₀ : ℕ) :
    ∃ κ0 Kc κ' κH κG κh κdet κin κdec κout κtr κtr' κAE εH : ℝ,
      aEnt 3 3 + 1 ≤ κ0 ∧ K0 3 3 κ0 + 1 ≤ Kc ∧ 0 < εH ∧ 0 ≤ κ' ∧ κ0 ≤ κ' ∧
      κ' + 3 * κ0 + c1 3 3 + 3 / 2 ≤ κH ∧
      εH ≤ 1 / (8 * Kc ^ 3 * c1 3 3 *
        Real.exp ((κH - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) ∧
      κH ≤ κG ∧ κ0 ≤ κh ∧ κ' ≤ κh ∧ κ' ≤ κdet ∧ κH = 2 * κdec - 1 ∧
      3 * κ0 + 3 ≤ κdec ∧ κdec - 1 ≤ κin ∧ κin ≤ κout ∧ κout ≤ min κh κ' - κ0 - 1 ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κAE ∧
      4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κtr ≤ κAE ∧
      1 ≤ (κAE / 2 - 1) / 2 ∧
      Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κAE / 2 - 1) / 2 ∧
      3 ≤ κtr ∧ 0 ≤ κtr' ∧ aMulti 3 3 + 2 ≤ 2 * κtr - κtr' ∧ 3 * κtr / 2 ≤ κtr' := by
  have hc1 : 1 ≤ c1 3 3 := one_le_c1 3 3
  have hent : 0 ≤ aEnt 3 3 := aEnt_nonneg 3 3
  obtain ⟨κ0, h0⟩ : ∃ x : ℝ, x = aEnt 3 3 + 1 := ⟨_, rfl⟩
  obtain ⟨κdec, hdec⟩ : ∃ x : ℝ, x = 100 * (κ0 + c1 3 3 + 10) := ⟨_, rfl⟩
  obtain ⟨κ', hk'⟩ : ∃ x : ℝ, x = 3 / 2 * κdec + κ0 + 1 := ⟨_, rfl⟩
  obtain ⟨κH, hkH⟩ : ∃ x : ℝ, x = 2 * κdec - 1 := ⟨_, rfl⟩
  obtain ⟨κtr, htr⟩ : ∃ x : ℝ, x = max 3 (2 * aMulti 3 3 + 4) := ⟨_, rfl⟩
  have hκtr3 : 3 ≤ κtr := htr ▸ le_max_left _ _
  have hκtr2 : 2 * aMulti 3 3 + 4 ≤ κtr := htr ▸ le_max_right _ _
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨κAE, hAE⟩ : ∃ x : ℝ, x = 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) *
    (κdec + κtr) + 6 + 4 * |Real.log X| := ⟨_, rfl⟩
  have hκ0pos : 0 ≤ κ0 := by linarith
  have hκdec0 : 0 ≤ κdec := by linarith
  have hκ'0 : 0 < κ' := by linarith
  have hlogX := le_abs_self (Real.log X)
  have habs := abs_nonneg (Real.log X)
  have hcoef : (0 : ℝ) ≤ 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) := by positivity
  have hcd := mul_le_mul_of_nonneg_left (show κdec ≤ κdec + κtr by linarith) hcoef
  have hct := mul_le_mul_of_nonneg_left (show κtr ≤ κdec + κtr by linarith) hcoef
  have hKc : 0 < K0 3 3 κ0 + 1 := by
    have : 0 ≤ K0 3 3 κ0 := by
      unfold K0
      apply div_nonneg (Real.exp_pos _).le
      have : Real.exp (-1) < 1 := by simp
      linarith
    linarith
  have hpos : 0 < 1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
      Real.exp ((κH - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)) := by
    have : 0 < c1 3 3 := by linarith
    positivity
  have hmin : min κ' κ' = κ' := min_self κ'
  exact ⟨κ0, K0 3 3 κ0 + 1, κ', κH, κH, κ', κ', κdec, κdec, 3 / 2 * κdec, κtr, 3 * κtr / 2, κAE,
    1 / (8 * (K0 3 3 κ0 + 1) ^ 3 * c1 3 3 *
      Real.exp ((κH - 2 * κ0) * cG 3 3 + c1 3 3 + κ' * cG 3 3)),
    by linarith, le_rfl, hpos, by linarith, by linarith, by linarith, le_rfl, le_rfl,
    by linarith, le_rfl, le_rfl, hkH, by linarith, by linarith, by linarith,
    by rw [hmin]; linarith, by linarith, by linarith, by linarith,
    by rw [← hX]; linarith, hκtr3, by linarith, by linarith, le_rfl⟩

/-- **T3 (comparison).**  With the landed label conversion `κ_H = hatKappaH d L (2 κdec - 1)`
there are no rates satisfying the landed fields (i), (iii), (iv) with `κin ≤ κout`
(`stepRates_no_closure_landed`); `stepRates_direct_witness` is the direct-label counterpart. -/
theorem stepRates_landed_impossible {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ¬ ∃ κ0 κ' κH κh κin κdec κout : ℝ, aEnt d L + 1 ≤ κ0 ∧ 0 < κin ∧
      hatKappaH d L (2 * κdec - 1) = κH ∧ κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH ∧ κ' ≤ κh ∧
      κdec - 1 ≤ κin ∧ κout ≤ min κh κ' - κ0 - 1 ∧ κin ≤ κout := by
  rintro ⟨κ0, κ', κH, κh, κin, κdec, κout, hκ0, hκin, hH, hκ, hκh, hdec, hout, hle⟩
  have := stepRates_no_closure_landed hd hL hκ0 hκin hdec hκh (hH ▸ hκ) hout
  linarith

end Balaban.Fluctuation
