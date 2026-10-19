/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuPt
public import Balaban.SmallField.XiProps

/-!
# Why the side conditions of the window conversion are not constant conditions (blocker 4, W1122)

`sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` produces its Theorem 5.2 constants
`Kw δw Ks δs Kw' δm` by `∃`, after the window point, and only then quantifies over the caller's
constants.  Its smallness conditions bound the caller's `ε_i = epsSeq L α α₀ (j_i + 1)` by `δw`,
for instance `bgK1 · (xiC1 · ε_i) ≤ min (δ*) δw`.  No condition on the caller's constants
can discharge them for an unspecified `δw`: the uniform form is false.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.SmallField

/-- The smallness condition `bgK1 · (xiC1 · ε) ≤ min (δ*) δw` of the window conversion holds for no
positive `ε` uniformly in the (existentially produced) constant `δw > 0`. -/
theorem window_smallness_not_uniform (d L N : ℕ) [NeZero L] {ε : ℝ} (hε : 0 < ε) :
    ¬ ∀ δw : ℝ, 0 < δw →
      bgK1 d L N * (xiC1 d * ε) ≤ min (deltaStar d L N) δw := by
  intro h
  have hx : 0 < xiC1 d := by unfold xiC1; positivity
  have hc : 0 < bgK1 d L N * (xiC1 d * ε) := mul_pos (bgK1_pos d L N) (mul_pos hx hε)
  have h1 := h (bgK1 d L N * (xiC1 d * ε) / 2) (by positivity)
  have h2 := h1.trans (min_le_right _ _)
  linarith

end Balaban.LargeField
