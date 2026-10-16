module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The collar count against the reserve (route R-YM, leaf `collar_reserve`)

The extended direction tests of the hybrid convention A0' reach the cubes within
`ρ_k = 2 ⌊R_{k-1}⌋ + 3` of a failing cube, with `R_{k-1} = R_b λ_{k-1}²`.  A large-field component
absorbs at most `(2 ρ_k + 1)^d` further cubes.  `collar_reserve` shows that the reserve
`β δ² = A₀² λ_k^{2 p₀} / a` of P5 (1.30)-(1.31) exceeds this count as soon as `p₀ > d` and
`A₀² λ_{k-1}² > a (4 R_b + 7)^d`; thus `p_*(d) = d`.
-/

@[expose] public section

namespace Balaban.LargeField

/-- `(2 ρ + 1)^d < β δ²`, with `ρ = 2 ⌊R_b λ'²⌋ + 3` (`λ' = λ_{k-1} ≤ λ = λ_k`) and
`β δ² = A₀² λ^{2 p₀} / a`, for `p₀ > d` and `a (4 R_b + 7)^d < A₀² λ'²`. -/
theorem collar_reserve (d p0 : ℕ) (hp : d < p0) {Rb a A0 lamPrev lam : ℝ} (hRb : 0 < Rb)
    (ha : 0 < a) (hA : 0 < A0) (h1 : 1 ≤ lamPrev) (hmono : lamPrev ≤ lam)
    (hlam : a * (4 * Rb + 7) ^ d < A0 ^ 2 * lamPrev ^ 2) :
    (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d < A0 ^ 2 * lam ^ (2 * p0) / a := by
  have hl2 : 1 ≤ lamPrev ^ 2 := one_le_pow₀ h1
  have hfl : (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) ≤ Rb * lamPrev ^ 2 :=
    Nat.floor_le (by positivity)
  have hbase : 2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1 ≤ (4 * Rb + 7) * lamPrev ^ 2 := by
    nlinarith
  have hnn : 0 ≤ 2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1 := by positivity
  have h2 : (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d ≤
      (4 * Rb + 7) ^ d * lamPrev ^ (2 * d) := by
    calc _ ≤ ((4 * Rb + 7) * lamPrev ^ 2) ^ d := pow_le_pow_left₀ hnn hbase d
      _ = _ := by rw [mul_pow, ← pow_mul]
  rw [lt_div_iff₀ ha]
  have hpos : 0 < lamPrev ^ (2 * d) := by positivity
  have h3 : (2 * (2 * (⌊Rb * lamPrev ^ 2⌋₊ : ℝ) + 3) + 1) ^ d * a <
      A0 ^ 2 * lamPrev ^ 2 * lamPrev ^ (2 * d) := by
    calc _ ≤ (4 * Rb + 7) ^ d * lamPrev ^ (2 * d) * a := by gcongr
      _ = a * (4 * Rb + 7) ^ d * lamPrev ^ (2 * d) := by ring
      _ < _ := mul_lt_mul_of_pos_right hlam hpos
  have h4 : lamPrev ^ 2 * lamPrev ^ (2 * d) ≤ lam ^ (2 * p0) := by
    calc lamPrev ^ 2 * lamPrev ^ (2 * d) = lamPrev ^ (2 * d + 2) := by ring
      _ ≤ lamPrev ^ (2 * p0) := pow_le_pow_right₀ h1 (by omega)
      _ ≤ lam ^ (2 * p0) := pow_le_pow_left₀ (by linarith) hmono _
  calc _ < A0 ^ 2 * lamPrev ^ 2 * lamPrev ^ (2 * d) := h3
    _ = A0 ^ 2 * (lamPrev ^ 2 * lamPrev ^ (2 * d)) := by ring
    _ ≤ A0 ^ 2 * lam ^ (2 * p0) := by gcongr

end Balaban.LargeField
