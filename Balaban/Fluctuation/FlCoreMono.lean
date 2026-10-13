/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionEngine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `FlCore` is monotone in its two radii

The fields of `FlCore` that mention `eps` carry it on the left with a nonnegative coefficient, and
those that mention `δ₁` carry it on the left of an upper bound.  Hence the core persists when
`eps` and `δ₁` are replaced by smaller positive radii.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps eps' : ℝ} {Kc Cx c₂ BG₂ δ₁ δ₁' : ℝ}

/-- **`FlCore` at smaller radii**: the core persists when the radius `eps` and the radius `δ₁`
are replaced by smaller positive numbers. -/
theorem FlCore.mono (h : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (he0 : 0 < eps') (he : eps' ≤ eps) (hδ0 : 0 < δ₁') (hδ : δ₁' ≤ δ₁) :
    FlCore N Gp Hm a₁ ν c BG κ eps' Kc Cx c₂ BG₂ δ₁' := by
  have hd0 : 0 < d := by have := h.HBp.hd; omega
  have hK4 : 0 < K4 d L N BG κ := K4_pos h.hS.fam.2.1 hd0
  have hX : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  have hXe : xiC1 d * eps' ≤ xiC1 d * eps := mul_le_mul_of_nonneg_left he hX
  have hKe : K4 d L N BG κ * (xiC1 d * eps') ≤ K4 d L N BG κ * (xiC1 d * eps) :=
    mul_le_mul_of_nonneg_left hXe hK4.le
  refine { h with
    eps_pos := he0
    small1 := ?_
    c7le := le_trans hXe h.c7le
    δ₁_pos := hδ0
    δ₁_le := le_trans hδ h.δ₁_le
    B_le := by linarith [h.B_le]
    B_one := by linarith [h.B_one]
    phi_lt := ?_ }
  · have := h.small1
    have h' : (4 * (d : ℝ) + 6) * ((2 * d + 1) * eps') ≤ (4 * d + 6) * ((2 * d + 1) * eps) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left he (by positivity)
    linarith
  · have := h.phi_lt
    have h' : (3 + K4 d L N BG κ) * (xiC1 d * eps') ≤ (3 + K4 d L N BG κ) * (xiC1 d * eps) :=
      mul_le_mul_of_nonneg_left hXe (by linarith)
    linarith

end Balaban.Localization
