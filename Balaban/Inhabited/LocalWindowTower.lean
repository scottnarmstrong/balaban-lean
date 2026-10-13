/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorTyping
public import Balaban.Inhabited.StepTower

/-!
# The tower records force the low-index window

The block-size lower bound `large_block` of a numerical tower, together with the lower bound on
the decoupling rate, gives `L ^ m₁ ≥ 128 d ^ 3`, hence `R₀(d, L) ≤ 5 L L ^ m₁`: the separation
window of the local generating sets is non-empty for every tower.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.LargeField

private theorem pow_ge_cube (d : ℕ) : (d : ℝ) ^ 3 ≤ (24 : ℝ) ^ d / 6 * d := by
  have h1 : d < 2 ^ d := Nat.lt_two_pow_self
  have h2 : d * d ≤ 4 ^ d := by
    calc d * d ≤ 2 ^ d * 2 ^ d := Nat.mul_le_mul h1.le h1.le
      _ = 4 ^ d := by rw [← mul_pow]; norm_num
  have h3 : 6 ≤ 6 ^ d ∨ d = 0 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact Or.inr h
    · exact Or.inl (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 6) h)
  rcases h3 with h3 | h3
  · have h24 : (24 : ℝ) ^ d = 4 ^ d * 6 ^ d := by
      rw [← mul_pow]; norm_num
    have a : ((d * d : ℕ) : ℝ) ≤ ((4 ^ d : ℕ) : ℝ) := by exact_mod_cast h2
    have b : ((6 : ℕ) : ℝ) ≤ ((6 ^ d : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at a b
    have hd : (0 : ℝ) ≤ d := by positivity
    rw [h24]
    have : (d : ℝ) * d * 6 ≤ 4 ^ d * 6 ^ d := by
      apply mul_le_mul a b (by norm_num) (by positivity)
    nlinarith
  · subst h3; simp

/-- **The tower forces the window.**  For every general tower, `R₀(d, L) ≤ 5 L · L ^ m₁`. -/
theorem StepTowerG.bgR0_le_minSep {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) : bgR0 d L ≤ minSep L ((L ^ T.m₁ : ℕ)) := by
  have hd := T.hd
  have hL := T.hL
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hLR : (3 : ℝ) ≤ L := by exact_mod_cast hL
  -- κ ≥ 12 d
  have hpow : (1 : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have hκ : 12 * (d : ℝ) ≤ T.κ := by
    have := T.κ_lower
    have h3 : (3 : ℝ) ≤ T.κdec := by linarith [T.κ0_nonneg, T.κdec_lower]
    have : 4 * (d : ℝ) * 1 * 3 ≤ 4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * T.κdec := by
      gcongr
    linarith
  -- cstarX ≥ 1
  have hc : 1 ≤ cstarX d L := by
    unfold cstarX
    have h1 := commXConst_nonneg d L
    have h2 := Cchi_nonneg d L
    have h5 : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    have : (1 : ℝ) ≤ (commXConst d L + 1) := by linarith
    have : (1 : ℝ) ≤ (Cchi d L + 1) := by linarith
    have : (1 : ℝ) ≤ (commXConst d L + 1) * (Cchi d L + 1) := by nlinarith
    have h72 : (1 : ℝ) ≤ 72 * (3 * 5 ^ d) := by nlinarith
    nlinarith
  have hN0 : 3 * (24 : ℝ) ^ d ≤ (N0 d L : ℝ) := by
    unfold N0
    push_cast
    have : (24 : ℝ) ^ d ≤ (8 * (L : ℝ)) ^ d := by
      gcongr; linarith
    linarith
  have hP : 128 * (d : ℝ) ^ 3 ≤ (L : ℝ) ^ T.m₁ := by
    have hb := T.large_block
    have he : (N0 d L : ℝ) * T.κ ≤ Real.exp (N0 d L * T.κ) := by
      linarith [Real.add_one_le_exp ((N0 d L : ℝ) * T.κ)]
    have hcub := pow_ge_cube d
    have h24 : (0 : ℝ) ≤ (24 : ℝ) ^ d := by positivity
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hk0 : 0 ≤ T.κ := by linarith
    have hstep : 36 * (24 : ℝ) ^ d * d ≤ (N0 d L : ℝ) * T.κ := by
      calc 36 * (24 : ℝ) ^ d * d = (3 * (24 : ℝ) ^ d) * (12 * d) := by ring
        _ ≤ (N0 d L : ℝ) * T.κ := by
          apply mul_le_mul hN0 hκ (by positivity) (by positivity)
    have hexp0 : 0 ≤ Real.exp (N0 d L * T.κ) := (Real.exp_pos _).le
    have : Real.exp (N0 d L * T.κ) ≤ cstarX d L * Real.exp (N0 d L * T.κ) := by
      nlinarith
    nlinarith
  have hLm : (L : ℝ) ^ T.m₁ ≥ 128 * (d : ℝ) ^ 3 := hP
  have hLpos : (0 : ℝ) < L := by linarith
  have hlogL : Real.log L ≤ L := by
    linarith [Real.log_le_sub_one_of_pos hLpos]
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  unfold minSep bgR0
  push_cast
  have hP0 : (d : ℝ) ≤ (L : ℝ) ^ T.m₁ := by
    have : (d : ℝ) ≤ (d : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith [pow_pos (by linarith : (0:ℝ) < d) 3]
  apply max_le
  · have : 4 * (d : ℝ) * L ≤ 5 * L * (L : ℝ) ^ T.m₁ := by nlinarith
    exact this
  · have hr : agmonRate d / 2 / 2 = 1 / (64 * (d : ℝ) ^ 2) := by
      unfold agmonRate poincareConst
      have : min (1 / (d : ℝ)) (1 / 2) = 1 / d := by
        apply min_eq_left
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      rw [this]; field_simp; ring
    rw [hr]
    have hd2 : (0 : ℝ) < d := by linarith
    have : 1 + 2 * (d : ℝ) * Real.log L / (1 / (64 * (d : ℝ) ^ 2)) =
        1 + 128 * (d : ℝ) ^ 3 * Real.log L := by
      field_simp; ring
    rw [this]
    have h1 : 128 * (d : ℝ) ^ 3 * Real.log L ≤ 128 * (d : ℝ) ^ 3 * L :=
      mul_le_mul_of_nonneg_left hlogL (by positivity)
    have h2 : 128 * (d : ℝ) ^ 3 * L ≤ (L : ℝ) ^ T.m₁ * L := by nlinarith
    nlinarith

/-- The fixed `3, 3, 2` tower forces the window as well. -/
theorem StepTower.bgR0_le_minSep {κmin : ℝ} (T : StepTower κmin) :
    bgR0 3 3 ≤ minSep 3 ((3 ^ T.m₁ : ℕ)) :=
  T.toG.bgR0_le_minSep

end Balaban.Inhabited
