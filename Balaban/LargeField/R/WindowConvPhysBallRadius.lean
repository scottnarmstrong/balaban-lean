/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.Setup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The radius condition of the switch (P7 (2.14))

The ball around the piece region `X_i` on which the local and the window generating sets agree has
radius `2 L^{j} M` (`piece_window_layers_switch`).  The stability of the background asks for the
radius `r ≥ (ϱ_B + 3d) L^{j+1} + 2`.  With `M = c M₁` this is the condition
`2 c M₁ ≥ (ϱ_B + 3d) L + 2` on the constants, for every scale `j`.
-/

@[expose] public section

namespace Balaban.LargeField

variable {S : Setting} [NeZero S.L] {n : ℕ → ℕ} {R : ℕ → ℝ} {M : ℕ}

/-- **The radius condition on the constants**: if `2 c M₁ ≥ (ϱ_B + 3d) L + 2` then the ball radius
`2 L^j M` of the piece is at least `(ϱ_B + 3d) L^{j+1} + 2` at every scale `j`. -/
theorem ball_radius_of_const (g : Geo S n R M) (ϱB : ℝ)
    (hc : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1)) (j : ℕ) :
    (ϱB + 3 * S.d) * (S.L : ℝ) ^ (j + 1) + 2 ≤ 2 * ((S.L : ℝ) ^ j * M) := by
  have hM : (M : ℝ) = (g.c : ℝ) * g.M1 := by exact_mod_cast g.hM
  have hL : (1 : ℝ) ≤ S.L := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  have hp : (1 : ℝ) ≤ (S.L : ℝ) ^ j := one_le_pow₀ hL
  have h0 : (0 : ℝ) ≤ (S.L : ℝ) ^ j := by linarith
  rw [hM, pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hc h0]

end Balaban.LargeField
