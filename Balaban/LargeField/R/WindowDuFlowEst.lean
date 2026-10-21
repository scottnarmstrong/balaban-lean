/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvRatio

/-!
# The coupling-weighted size of the sources along the flow (blocker 4)

For the flow `β_j = β L^{(d-2) j} g_j` with `g_j ≤ e^η` and the sources `ε_j = α₀ T_j L^{-α j}`
(`T_j < 3`), `d - 2 - 2α = 2γ`:

* `beta_epsSq_decay_le`: `β_j ε_j² (L^{-2γ})^j ≤ 9 β e^η α₀²`;
* `beta_epsSq_le_pow`: `β_j ε_j² ≤ 9 β e^η α₀² (L^{2γ})^J` for `j ≤ J`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.SmallField Balaban.LargeField.ActionConv

/-- **`β_j ε_j² (L^{-2γ})^j ≤ 9 β e^η α₀²`.** -/
theorem beta_epsSq_decay_le (L d : ℕ) [NeZero L] (hd : 2 ≤ d) {β η α α₀ γ b g : ℝ} {j : ℕ}
    (hβ : 0 ≤ β) (hα₀ : 0 ≤ α₀) (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (hb : b = β * (L : ℝ) ^ ((d - 2) * j) * g) (hg0 : 0 ≤ g) (hg : g ≤ Real.exp η) :
    b * epsSeq L α α₀ j ^ 2 * ((L : ℝ) ^ (-(2 * γ))) ^ j ≤ 9 * β * Real.exp η * α₀ ^ 2 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hq0 : 0 ≤ ((L : ℝ) ^ (-α)) ^ j := pow_nonneg (Real.rpow_nonneg hLpos.le _) _
  have hr0 : 0 ≤ ((L : ℝ) ^ (-(2 * γ))) ^ j := pow_nonneg (Real.rpow_nonneg hLpos.le _) _
  have hT3 := epsTail_lt_three j
  have hε0 : 0 ≤ epsSeq L α α₀ j := by
    unfold epsSeq
    have := epsTail_pos j
    positivity
  have hε : epsSeq L α α₀ j ≤ 3 * α₀ * ((L : ℝ) ^ (-α)) ^ j := by
    unfold epsSeq
    have h1 : α₀ * epsTail j ≤ α₀ * 3 := mul_le_mul_of_nonneg_left hT3.le hα₀
    calc α₀ * epsTail j * ((L : ℝ) ^ (-α)) ^ j ≤ α₀ * 3 * ((L : ℝ) ^ (-α)) ^ j :=
          mul_le_mul_of_nonneg_right h1 hq0
      _ = 3 * α₀ * ((L : ℝ) ^ (-α)) ^ j := by ring
  have hε2 : epsSeq L α α₀ j ^ 2 ≤ (3 * α₀ * ((L : ℝ) ^ (-α)) ^ j) ^ 2 :=
    pow_le_pow_left₀ hε0 hε 2
  have key : (L : ℝ) ^ ((d - 2) * j) * (((L : ℝ) ^ (-α)) ^ j) ^ 2 *
      ((L : ℝ) ^ (-(2 * γ))) ^ j = 1 := by
    have e1 : (L : ℝ) ^ ((d - 2) * j) = (L : ℝ) ^ ((((d - 2) * j : ℕ) : ℝ)) :=
      (Real.rpow_natCast _ _).symm
    have e2 : (((L : ℝ) ^ (-α)) ^ j) ^ 2 = (L : ℝ) ^ (-α * ((j * 2 : ℕ) : ℝ)) := by
      rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    have e3 : ((L : ℝ) ^ (-(2 * γ))) ^ j = (L : ℝ) ^ (-(2 * γ) * (j : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    rw [e1, e2, e3, ← Real.rpow_add hLpos, ← Real.rpow_add hLpos]
    have hc : (((d - 2) * j : ℕ) : ℝ) = ((d : ℝ) - 2) * j := by
      push_cast [Nat.cast_sub hd]; ring
    have : (((d - 2) * j : ℕ) : ℝ) + -α * ((j * 2 : ℕ) : ℝ) + -(2 * γ) * (j : ℝ) = 0 := by
      rw [hc]; push_cast; nlinarith
    rw [this, Real.rpow_zero]
  have hLk : 0 ≤ (L : ℝ) ^ ((d - 2) * j) := by positivity
  have hb' : b ≤ β * (L : ℝ) ^ ((d - 2) * j) * Real.exp η := by
    rw [hb]; exact mul_le_mul_of_nonneg_left hg (by positivity)
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  calc b * epsSeq L α α₀ j ^ 2 * ((L : ℝ) ^ (-(2 * γ))) ^ j
      ≤ (β * (L : ℝ) ^ ((d - 2) * j) * Real.exp η) * (3 * α₀ * ((L : ℝ) ^ (-α)) ^ j) ^ 2 *
          ((L : ℝ) ^ (-(2 * γ))) ^ j := by
        gcongr
    _ = 9 * β * Real.exp η * α₀ ^ 2 *
          ((L : ℝ) ^ ((d - 2) * j) * (((L : ℝ) ^ (-α)) ^ j) ^ 2 * ((L : ℝ) ^ (-(2 * γ))) ^ j) := by
        ring
    _ = 9 * β * Real.exp η * α₀ ^ 2 := by rw [key, mul_one]

/-- **`β_j ε_j² ≤ 9 β e^η α₀² (L^{2γ})^J` for `j ≤ J`.** -/
theorem beta_epsSq_le_pow (L d : ℕ) [NeZero L] (hd : 2 ≤ d) {β η α α₀ γ b g : ℝ} {j J : ℕ}
    (hβ : 0 ≤ β) (hα₀ : 0 ≤ α₀) (hγ : 0 ≤ γ) (hγα : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (hb : b = β * (L : ℝ) ^ ((d - 2) * j) * g) (hg0 : 0 ≤ g) (hg : g ≤ Real.exp η) (hjJ : j ≤ J) :
    b * epsSeq L α α₀ j ^ 2 ≤ 9 * β * Real.exp η * α₀ ^ 2 * ((L : ℝ) ^ (2 * γ)) ^ J := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have h := beta_epsSq_decay_le L d hd (η := η) (j := j) hβ hα₀ hγα hb hg0 hg
  have hs1 : (1 : ℝ) ≤ (L : ℝ) ^ (2 * γ) := Real.one_le_rpow hL1 (by positivity)
  have hrs : ((L : ℝ) ^ (-(2 * γ))) ^ j * ((L : ℝ) ^ (2 * γ)) ^ j = 1 := by
    rw [← mul_pow, ← Real.rpow_add hLpos]
    simp
  have hA0 : 0 ≤ 9 * β * Real.exp η * α₀ ^ 2 := by positivity
  have hb0 : 0 ≤ b * epsSeq L α α₀ j ^ 2 := by
    rw [hb]; positivity
  calc b * epsSeq L α α₀ j ^ 2
      = b * epsSeq L α α₀ j ^ 2 * (((L : ℝ) ^ (-(2 * γ))) ^ j * ((L : ℝ) ^ (2 * γ)) ^ j) := by
        rw [hrs, mul_one]
    _ = (b * epsSeq L α α₀ j ^ 2 * ((L : ℝ) ^ (-(2 * γ))) ^ j) * ((L : ℝ) ^ (2 * γ)) ^ j := by ring
    _ ≤ (9 * β * Real.exp η * α₀ ^ 2) * ((L : ℝ) ^ (2 * γ)) ^ j :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ ≤ (9 * β * Real.exp η * α₀ ^ 2) * ((L : ℝ) ^ (2 * γ)) ^ J := by
        gcongr

end Balaban.LargeField
