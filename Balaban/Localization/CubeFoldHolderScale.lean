/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseHolderMain

/-!
# The scale split of the mixed-wall Hölder estimate (VMOD-10 §2)

`cut_holder_scale_cases`, `cut_holder_scale`: outside the short regime `j ≥ 2`, `ρ ≥ 8`, `r ≤ ρ/4`
(`ρ = c₀ L^{j-1}/d`), `ℓ ≤ (8dL/c₀) ℓ^θ r^{1-θ}` (VMOD-10 (2.2)), with an abstract radius constant `c₀`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale

variable {d L : ℕ} [NeZero L]

/-- **The case split of VMOD-10 §2** at an abstract radius constant `c₀ > 0`: outside the short
regime `j ≥ 2`, `ρ ≥ 8`, `r ≤ ρ/4` (`ρ = c₀ L^{j-1}/d`), `L^j ≤ 8dL/c₀` or `L^j ≤ (8dL/c₀) r`. -/
theorem cut_holder_scale_cases {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1) {j : ℕ} (hj : 1 ≤ j) {r : ℝ}
    (hnot : ¬ (2 ≤ j ∧ 8 ≤ c0 * (L : ℝ) ^ (j - 1) / d ∧ r ≤ (c0 * (L : ℝ) ^ (j - 1) / d) / 4))
    (hd : 1 ≤ d) :
    (L : ℝ) ^ j ≤ 8 * d * L / c0 ∨ (L : ℝ) ^ j ≤ 8 * d * L / c0 * r := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  have hpow : (L : ℝ) ^ j = L * (L : ℝ) ^ (j - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hK : (L : ℝ) ≤ 8 * d * L / c0 := by
    rw [le_div_iff₀ hc0]; nlinarith [mul_pos hd0 hL0]
  by_cases hj2 : 2 ≤ j
  · by_cases h8 : 8 ≤ c0 * (L : ℝ) ^ (j - 1) / d
    · right
      have hr : (c0 * (L : ℝ) ^ (j - 1) / d) / 4 < r := by
        by_contra hcon
        exact hnot ⟨hj2, h8, not_lt.1 hcon⟩
      have hρ0 : 0 < c0 * (L : ℝ) ^ (j - 1) / d := by positivity
      have e : (L : ℝ) ^ (j - 1) = d * ((c0 * (L : ℝ) ^ (j - 1) / d)) / c0 := by
        field_simp
      rw [hpow, e]
      have hr' : (c0 * (L : ℝ) ^ (j - 1) / d) < 4 * r := by linarith
      rw [show (L : ℝ) * (d * (c0 * (L : ℝ) ^ (j - 1) / d) / c0) =
          d * L / c0 * (c0 * (L : ℝ) ^ (j - 1) / d) by field_simp]
      have hq : 0 < (d : ℝ) * L / c0 := by positivity
      have : 8 * (d : ℝ) * L / c0 * r = d * L / c0 * (8 * r) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hq.le
    · left
      push Not at h8
      have e : (L : ℝ) ^ (j - 1) < 8 * d / c0 := by
        rw [div_lt_iff₀ hd0] at h8
        rw [lt_div_iff₀ hc0]; linarith
      rw [hpow]
      calc (L : ℝ) * (L : ℝ) ^ (j - 1) ≤ L * (8 * d / c0) :=
            mul_le_mul_of_nonneg_left e.le hL0.le
        _ = _ := by ring
  · left
    have : j = 1 := by omega
    subst this
    simp only [pow_one]
    exact hK

/-- **VMOD-10 (2.2).** Outside the short regime, `ℓ ≤ (8dL/c₀) ℓ^θ r^{1-θ}`. -/
theorem cut_holder_scale {c0 : ℝ} (hc0 : 0 < c0) (hc04 : c0 ≤ 1 / 4) {j : ℕ} (hj : 1 ≤ j) {r : ℝ}
    (hr : 1 ≤ r)
    (hnot : ¬ (2 ≤ j ∧ 8 ≤ c0 * (L : ℝ) ^ (j - 1) / d ∧ r ≤ (c0 * (L : ℝ) ^ (j - 1) / d) / 4))
    (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (L : ℝ) ^ j ≤ 8 * d * L / c0 * (((L : ℝ) ^ j) ^ θ * r ^ (1 - θ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hℓ1 : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ hL1
  have hK1 : (1 : ℝ) ≤ 8 * d * L / c0 := by
    rw [le_div_iff₀ hc0]; nlinarith [mul_pos (lt_of_lt_of_le one_pos hd1) (lt_of_lt_of_le one_pos hL1)]
  exact le_const_rpow_mul hℓ1 hr hK1 hθ0 hθ1 (cut_holder_scale_cases hc0 (hc04.trans (by norm_num)) hj hnot hd)

end Balaban.Localization
