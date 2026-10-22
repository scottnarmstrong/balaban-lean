/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Terms
public import Balaban.Localization.PolymerGeometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The size bound of the cast comparison from the torus size

`hbig_of_size`: the torus-size condition `hbigA` of `hgeom_of_cast` follows from a bound of the form
`2 R + (4 (k+1) + 36) L^{k+1+m₀+m₁} + 8 ≤ size`, for `L ≥ 3` and a cube exponent `s < m₀`
(`s` is the exponent of `ClassHatCond`, `hatScale < m₀`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization

theorem hbig_of_size {L m₀ m₁ s k R size : ℕ} (hL : 3 ≤ L) (hs : s < m₀)
    (hsz : 2 * R + (4 * (k + 1) + 36) * L ^ (k + 1 + m₀ + m₁) + 8 ≤ size) :
    2 * (R + 3 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ k) +
        (5 * L + 1) * (L ^ k * L ^ (m₁ + s)) + 6 * (k + 1) * L ^ ((k + 1) + (m₁ + s)) + 1 +
        (5 * L + 2) * L ^ ((k + 1) + (m₁ + s)) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < size := by
  have hL0 : 0 < L := by omega
  set V := L ^ (k + 1 + m₀ + m₁) with hV
  set P := L ^ ((k + 1) + (m₁ + s)) with hP
  set Q := L ^ k * L ^ (m₁ + s) with hQ
  have hQe : Q = L ^ (k + (m₁ + s)) := by rw [hQ, ← pow_add]
  have hLP : L * P ≤ V := by
    rw [hP, hV, ← pow_succ']; exact Nat.pow_le_pow_right hL0 (by omega)
  have hLLQ : L * (L * Q) ≤ V := by
    rw [hQe, ← pow_succ', ← pow_succ', hV]; exact Nat.pow_le_pow_right hL0 (by omega)
  have hcs : cellSide L m₀ m₁ k = L ^ (k + m₀ + m₁) := rfl
  have hLcs : L * cellSide L m₀ m₁ k = V := by
    rw [hcs, hV, ← pow_succ']; congr 1; omega
  have hLk1 : L ^ (k + 1) ≤ V := by
    rw [hV]; exact Nat.pow_le_pow_right hL0 (by omega)
  -- the pieces
  have h1 : (5 * L + 1) * Q ≤ 2 * V := by
    have hQL : Q ≤ L * Q := Nat.le_mul_of_pos_left Q hL0
    have h3 : 3 * (L * Q) ≤ L * (L * Q) := Nat.mul_le_mul_right _ hL
    nlinarith
  have h2 : 6 * (k + 1) * P ≤ 2 * (k + 1) * V := by
    have h3 : 3 * P ≤ V := by
      have : 3 * P ≤ L * P := Nat.mul_le_mul_right _ hL
      omega
    nlinarith
  have h3 : (5 * L + 2) * P ≤ 7 * V := by
    have : (5 * L + 2) * P ≤ 7 * (L * P) := by nlinarith [Nat.zero_le P]
    omega
  have h4 : 3 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ k) ≤ 4 * V := by
    have hcs3 : 3 * cellSide L m₀ m₁ k ≤ V := by
      have : 3 * cellSide L m₀ m₁ k ≤ L * cellSide L m₀ m₁ k := Nat.mul_le_mul_right _ hL
      omega
    have hh : (2 * (L / 2) + 1) ≤ L + 1 := by omega
    have : (2 * (L / 2) + 1) * cellSide L m₀ m₁ k ≤ (L + 1) * cellSide L m₀ m₁ k :=
      Nat.mul_le_mul_right _ hh
    have e : (L + 1) * cellSide L m₀ m₁ k = L * cellSide L m₀ m₁ k + cellSide L m₀ m₁ k := by ring
    omega
  nlinarith [hsz]

end Balaban.Inhabited
