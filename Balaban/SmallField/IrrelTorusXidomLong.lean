/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSquare
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The longitudinal estimate for a real-centred complex datum

This is the scalar estimate after splitting the source field into its component along the
real centre and its orthogonal component. It is used with the normalized composed spin.
-/

@[expose] public section

namespace Balaban.SmallField

/-- The longitudinal contraction is quadratic in the complex chart radius. -/
theorem longitudinal_contraction_le
    {ν τ ζ : ℝ} {u v hL hP : ℂ}
    (hζ : 0 ≤ ζ)
    (hLong : ‖hL - ν‖ ≤ 2 * τ ^ 2 * ζ ^ 2)
    (hu : ‖u - 1‖ ≤ 8 * ζ ^ 2)
    (hv : ‖v‖ ≤ 4 * ζ)
    (hbL : ‖hL‖ ≤ 3 * τ ^ 2)
    (hbP : ‖hP‖ ≤ 3 * τ ^ 2 * ζ) :
    ‖u * hL + v * hP - ν‖ ≤ 38 * τ ^ 2 * ζ ^ 2 := by
  have e : u * hL + v * hP - (ν : ℂ) =
      (hL - ν) + (u - 1) * hL + v * hP := by ring
  rw [e]
  have h1 : ‖(u - 1) * hL‖ ≤ 24 * τ ^ 2 * ζ ^ 2 := by
    rw [norm_mul]
    calc
      ‖u - 1‖ * ‖hL‖ ≤ (8 * ζ ^ 2) * (3 * τ ^ 2) :=
        mul_le_mul hu hbL (norm_nonneg _) (by positivity)
      _ = 24 * τ ^ 2 * ζ ^ 2 := by ring
  have h2 : ‖v * hP‖ ≤ 12 * τ ^ 2 * ζ ^ 2 := by
    rw [norm_mul]
    calc
      ‖v‖ * ‖hP‖ ≤ (4 * ζ) * (3 * τ ^ 2 * ζ) :=
        mul_le_mul hv hbP (norm_nonneg _) (by positivity)
      _ = 12 * τ ^ 2 * ζ ^ 2 := by ring
  calc
    ‖(hL - ν) + (u - 1) * hL + v * hP‖
        ≤ ‖hL - ν‖ + ‖(u - 1) * hL‖ + ‖v * hP‖ := by
          nlinarith only [norm_add_le (hL - ν + (u - 1) * hL) (v * hP),
            norm_add_le (hL - ν) ((u - 1) * hL)]
    _ ≤ 2 * τ ^ 2 * ζ ^ 2 + 24 * τ ^ 2 * ζ ^ 2 + 12 * τ ^ 2 * ζ ^ 2 := by
      nlinarith only [hLong, h1, h2]
    _ = 38 * τ ^ 2 * ζ ^ 2 := by ring

end Balaban.SmallField
