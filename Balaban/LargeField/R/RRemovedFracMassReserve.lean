/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.LargeField.Regime.A0PrimeReserve
import Mathlib.Tactic.Linarith

/-!
# One reserve payment for the collar and the complete-action mass cost

The strengthened collar threshold spends half of the chosen reserve fraction.  The other
half pays the fixed-window mass oscillation term.  The source still needs to establish these
thresholds for its chosen constants.
-/

@[expose] public section

namespace Balaban.LargeField

/-- The collar count and one fixed-window mass cost fit in the same seed reserve. -/
theorem collar_mass_reserve (d p0 : ℕ) (hp : d < p0) {Rb a A0 lamPrev lam θ Cm Dd : ℝ}
    (hRb : 0 < Rb) (ha : 0 < a) (hA : 0 < A0) (h1 : 1 ≤ lamPrev)
    (hmono : lamPrev ≤ lam) (hθ : θ < 1)
    (hcollar : (2 * a / (1 - θ)) * (4 * Rb + 7) ^ d < A0 ^ 2 * lamPrev ^ 2)
    (hmass : 2 * a * Cm * Dd ≤ (1 - θ) * A0 ^ 2 * lam ^ (2 * p0)) :
    (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d + Cm * Dd <
      (1 - θ) * (A0 ^ 2 * lam ^ (2 * p0) / a) := by
  have hθpos : 0 < 1 - θ := sub_pos.mpr hθ
  have ha' : 0 < 2 * a / (1 - θ) := div_pos (by positivity) hθpos
  have hcollarBound := collar_reserve d p0 hp hRb ha' hA h1 hmono hcollar
  have hidentity : A0 ^ 2 * lam ^ (2 * p0) / (2 * a / (1 - θ)) =
      (1 - θ) / 2 * (A0 ^ 2 * lam ^ (2 * p0) / a) := by
    field_simp
  rw [hidentity] at hcollarBound
  have hmassHalf : Cm * Dd ≤ (1 - θ) / 2 * (A0 ^ 2 * lam ^ (2 * p0) / a) := by
    rw [show (1 - θ) / 2 * (A0 ^ 2 * lam ^ (2 * p0) / a) =
      ((1 - θ) * A0 ^ 2 * lam ^ (2 * p0)) / (2 * a) by field_simp]
    rw [le_div_iff₀ (by positivity : 0 < 2 * a)]
    nlinarith only [hmass]
  nlinarith only [hcollarBound, hmassHalf]

end Balaban.LargeField
