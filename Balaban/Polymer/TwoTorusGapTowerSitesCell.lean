/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.BoxTransport
public import Balaban.Frozen.Geometry.IsPolymer

/-!
# Fine sites and coarse cells (blocker 7)

The dictionary between the fine sites of the torus `ℤ/(D K)` and its `K^d` cells of side `D`
(for the tower: `D = aK = cellSide L 1 m₁ (k+1)`, `D K = N₁ L^{m₁} L^{k+1}`; for Root-F: `D = M L^j`,
a block of `IsPolymer`).  The cell of the point `y ∈ ℤ` is `y / D` (floor division); in the quarter
box shrunk by one cell, `4 (|y| + D) < D K`, the cell is in the quarter box `4 |c| < K` of the
coarse torus, and the cell index of the image of `y` in `ℤ/(D K)` is the centred representative of
`y / D`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

section Cell

variable {D K : ℕ}

/-- The cell index of the image of `y ∈ ℤ` in `ℤ/(D K)`, as an integer: `(y / D) mod K`. -/
theorem val_div_cast_int {n : ℕ} (hn : n = D * K) (hD : 0 < D) (hK : 0 < K) (y : ℤ) :
    ((((y : ZMod n).val / D : ℕ) : ℕ) : ℤ) = (y / (D : ℤ)) % (K : ℤ) := by
  subst hn
  have : NeZero (D * K) := ⟨Nat.mul_ne_zero hD.ne' hK.ne'⟩
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have hKz : (0 : ℤ) < K := by exact_mod_cast hK
  rw [Int.natCast_div, ZMod.val_intCast]
  push_cast
  set q := y / (D : ℤ) with hq
  set r := y % (D : ℤ) with hr
  have hy : y = (D : ℤ) * q + r := (Int.mul_ediv_add_emod y D).symm
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hDz.ne'
  have hr1 : r < D := Int.emod_lt_of_pos _ hDz
  set t := q % (K : ℤ) with ht
  set s := q / (K : ℤ) with hs
  have hq' : q = (K : ℤ) * s + t := (Int.mul_ediv_add_emod q K).symm
  have ht0 : 0 ≤ t := Int.emod_nonneg _ hKz.ne'
  have ht1 : t < K := Int.emod_lt_of_pos _ hKz
  have hy2 : y = ((D : ℤ) * K) * s + ((D : ℤ) * t + r) := by
    rw [hy, hq']; ring
  have hlt : (D : ℤ) * t + r < (D : ℤ) * K := by nlinarith
  have hnn : 0 ≤ (D : ℤ) * t + r := by nlinarith
  have hm : y % ((D : ℤ) * K) = (D : ℤ) * t + r := by
    rw [hy2, Int.mul_add_emod_self_left]
    · exact Int.emod_eq_of_lt hnn hlt
  rw [hm]
  have : ((D : ℤ) * t + r) / D = t := by
    rw [Int.mul_add_ediv_left _ _ hDz.ne']
    rw [Int.ediv_eq_zero_of_lt hr0 hr1]; ring
  exact this

/-- The cell index of the image of `y` is the centred representative of the cell `y / D`, if that
is small. -/
theorem cell_valMinAbs {n r : ℕ} (hn : n = D * K) (hD : 0 < D) (hK : 2 * r + 1 < K) {y : ℤ}
    (h : |y / (D : ℤ)| ≤ r) :
    ((((y : ZMod n).val / D : ℕ) : ZMod K)).valMinAbs = y / (D : ℤ) := by
  have hK0 : 0 < K := by omega
  have h1 : ((((y : ZMod n).val / D : ℕ) : ZMod K)) = ((y / (D : ℤ) : ℤ) : ZMod K) := by
    have := val_div_cast_int hn hD hK0 y
    have h2 : ((((y : ZMod n).val / D : ℕ) : ZMod K)) =
        ((((((y : ZMod n).val / D : ℕ) : ℕ) : ℤ)) : ZMod K) :=
      (Int.cast_natCast _).symm
    rw [h2, this, ZMod.intCast_mod]
  rw [h1]
  exact valMinAbs_intCast_of_abs_le hK h

/-- The quarter box shrunk by one cell: the cell of a fine point lies in the quarter box of the
coarse torus. -/
theorem four_abs_ediv_lt (hD : 0 < D) {y : ℤ} (h : 4 * (|y| + D) < (D : ℤ) * K) :
    4 * |y / (D : ℤ)| < K := by
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have h1 := Int.mul_ediv_self_le (x := y) hDz.ne'
  have h2 := Int.lt_mul_ediv_self_add (x := y) hDz
  set c := y / (D : ℤ)
  rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rcases abs_cases c with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
    nlinarith

end Cell

end Balaban.Polymer.TwoTorusStep
