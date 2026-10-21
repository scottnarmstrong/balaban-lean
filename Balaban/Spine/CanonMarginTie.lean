/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Nat

/-!
# The numeric tie of the canonical margin

`CanonMarginTie L m₀`: `18 ≤ (L - 2) L^{m₀}`.  The region `X₁` of an inherited term contains the
`(L-2)`-cell neighbourhood of the polymer (`X1_far`); the margin of the two-torus comparison is the
set of sites within `12 M` of the polymer (`M = L^{k+1+m₁}`) enlarged by `6 M` (`hatRad_add_le_six`), and a cell has
side `L^{m₀} M`.  The tie is a choice of the constants `L`, `m₀` (it holds for `m₀ ≥ 3` and `L ≥ 3`,
`canonMarginTie_of_three_le`, and for `m₀ ≥ 2` and `L ≥ 4`); `m₀` is the cover parameter, free in the statement of the roots.
-/

@[expose] public section

namespace Balaban.Spine

/-- **The tie** `18 ≤ (L - 2) L^{m₀}`. -/
def CanonMarginTie (L m₀ : ℕ) : Prop := 18 ≤ (L - 2) * L ^ m₀

/-- `m₀ ≥ 3` and `L ≥ 3` give the tie: `(L-2) L^{m₀} ≥ L^3 ≥ 27`.  (For `L = 3`, `m₀ = 2` the value is `9`.) -/
theorem canonMarginTie_of_three_le {L m₀ : ℕ} (hL : 3 ≤ L) (hm : 3 ≤ m₀) :
    CanonMarginTie L m₀ := by
  unfold CanonMarginTie
  have h1 : 1 ≤ L - 2 := by omega
  have h2 : 27 ≤ L ^ m₀ := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ L ^ 3 := Nat.pow_le_pow_left hL 3
      _ ≤ L ^ m₀ := Nat.pow_le_pow_right (by omega) hm
  calc 18 ≤ 27 := by norm_num
    _ ≤ L ^ m₀ := h2
    _ = 1 * L ^ m₀ := (one_mul _).symm
    _ ≤ (L - 2) * L ^ m₀ := Nat.mul_le_mul_right _ h1

/-- Non-vacuity (rule 10): the tie holds at the constants `L = 3`, `m₀ = 3`. -/
theorem canonMarginTie_nonempty : CanonMarginTie 3 3 := canonMarginTie_of_three_le le_rfl le_rfl

/-- For `L ≥ 4` and `m₀ ≥ 2` the tie holds (`(L-2) L² ≥ 2 · 16`). -/
theorem canonMarginTie_of_four_le {L m₀ : ℕ} (hL : 4 ≤ L) (hm : 2 ≤ m₀) :
    CanonMarginTie L m₀ := by
  unfold CanonMarginTie
  have h1 : 2 ≤ L - 2 := by omega
  have h2 : 16 ≤ L ^ m₀ := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ L ^ 2 := Nat.pow_le_pow_left hL 2
      _ ≤ L ^ m₀ := Nat.pow_le_pow_right (by omega) hm
  calc 18 ≤ 2 * 16 := by norm_num
    _ ≤ (L - 2) * L ^ m₀ := Nat.mul_le_mul h1 h2

end Balaban.Spine
