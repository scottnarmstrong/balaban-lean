/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# The positive-mass term in the removed quotient

The radius is at most one.  This bounds the extra oscillation term of the complete action
without changing the massless boundary estimate.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The additional complete-action oscillation cost with a bounded running mass. -/
theorem removed_mass_arith {N : ℕ} {mass E ρ Kw cF cst card Dd : ℝ}
    (hmass0 : 0 ≤ mass) (hmass : mass ≤ E) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hKw : 0 ≤ Kw) (hcF : 0 ≤ cF) (hcst : 0 ≤ cst)
    (hcard0 : 0 ≤ card) (hcard : card ≤ Dd) :
    mass * ((N : ℝ) / 2 * (4 * (Kw * (cF * ρ)) + (Kw * (cF * ρ)) ^ 2)) *
        (card * cst) ≤
      E * ((N : ℝ) / 2 * (4 * (Kw * cF) + (Kw * cF) ^ 2)) * cst * Dd := by
  have hE : 0 ≤ E := hmass0.trans hmass
  have hDd : 0 ≤ Dd := hcard0.trans hcard
  set B := Kw * (cF * ρ) with hB
  set Bc := Kw * cF with hBc
  have hB0 : 0 ≤ B := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  have hBle : B ≤ Bc := by
    rw [hB, hBc]
    have heq : Kw * (cF * ρ) = (Kw * cF) * ρ := by ring
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hρ1
  have hquad : 4 * B + B ^ 2 ≤ 4 * Bc + Bc ^ 2 := by
    nlinarith [pow_le_pow_left₀ hB0 hBle 2]
  calc mass * ((N : ℝ) / 2 * (4 * B + B ^ 2)) * (card * cst)
      ≤ E * ((N : ℝ) / 2 * (4 * Bc + Bc ^ 2)) * (Dd * cst) := by
          gcongr
    _ = _ := by ring

end Balaban.LargeField
