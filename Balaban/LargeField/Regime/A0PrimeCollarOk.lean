/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Regime.A0PrimeReserve
public import Balaban.LargeField.Counter.Params

/-!
# The collar reserve under the typing conditions (W874, blocker 2)

The hypothesis `d < p₀` of `collar_reserve` follows from the typing conditions `p₂ ≥ 2d + 3` and
`p₂ < 2 p₀` (`Typing.Ok.p2_ge`, `Typing.Ok.p0_gt`): they give `p₀ ≥ d + 2`.
-/

@[expose] public section

namespace Balaban.LargeField

/-- Under the typing conditions, `d + 2 ≤ p₀`. -/
theorem Typing.Ok.d_add_two_le_p0 {T : Typing} (ok : T.Ok) : T.d + 2 ≤ T.p0 := by
  have h1 := ok.p2_ge
  have h2 := ok.p0_gt
  omega

/-- Under the typing conditions, `d < p₀`. -/
theorem Typing.Ok.d_lt_p0 {T : Typing} (ok : T.Ok) : T.d < T.p0 := by
  have := ok.d_add_two_le_p0
  omega

/-- **The collar reserve for a setting with the typing conditions**: `collar_reserve` at
`d = T.d`, `p₀ = T.p0`, with `d < p₀` taken from `Typing.Ok`. -/
theorem collar_reserve_of_typing {T : Typing} (ok : T.Ok) {Rb a A0 lamPrev lam : ℝ}
    (hRb : 0 < Rb) (ha : 0 < a) (hA : 0 < A0) (h1 : 1 ≤ lamPrev) (hmono : lamPrev ≤ lam)
    (hlam : a * (4 * Rb + 7) ^ T.d < A0 ^ 2 * lamPrev ^ 2) :
    (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ T.d <
      A0 ^ 2 * lam ^ (2 * T.p0) / a :=
  collar_reserve T.d T.p0 ok.d_lt_p0 hRb ha hA h1 hmono hlam

end Balaban.LargeField
