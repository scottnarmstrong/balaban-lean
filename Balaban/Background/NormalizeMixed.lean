/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Mixed second differences of the normalization (four-point version of `normalize_bounds`)

For four vectors `v₀₀, v₁₀, v₀₁, v₁₁` near a unit reference vector, the mixed second difference
`F(v₁₁) - F(v₁₀) - F(v₀₁) + F(v₀₀)` of `F = normalize` is bounded by the first differences `T₁`
(from `v₀₀`) and the mixed second difference `T₂` of the `v`'s:
`‖Δ F‖ ≤ 22 T₂ + 650 T₁²` (`normalize_mixed`).  As in `normalize_bounds`, the proof is by exact
algebraic identities for `s = √(v ⬝ v)` and `s⁻¹`, without derivatives.
-/

@[expose] public section

namespace Balaban.Background

open Matrix

section Scalar

/-- The mixed second difference of `s⁻¹` in terms of that of `s`. -/
theorem inv_mixed_le {s00 s10 s01 s11 : ℂ} {Z t : ℝ} (h00 : 19 / 20 ≤ s00.re)
    (h10 : 19 / 20 ≤ s10.re) (h01 : 19 / 20 ≤ s01.re) (h11 : 19 / 20 ≤ s11.re)
    (hZ : ‖s11 - s10 - s01 + s00‖ ≤ Z) (t10 : ‖s10 - s00‖ ≤ t) (t01 : ‖s01 - s00‖ ≤ t)
    (t11 : ‖s11 - s00‖ ≤ t) :
    ‖s11⁻¹ - s10⁻¹ - s01⁻¹ + s00⁻¹‖ ≤ 2 * Z + 6 * t ^ 2 := by
  have n00 := norm_ge_of_re h00
  have n10 := norm_ge_of_re h10
  have n01 := norm_ge_of_re h01
  have n11 := norm_ge_of_re h11
  have e00 : s00 ≠ 0 := by intro h; rw [h] at n00; simp at n00; linarith
  have e10 : s10 ≠ 0 := by intro h; rw [h] at n10; simp at n10; linarith
  have e01 : s01 ≠ 0 := by intro h; rw [h] at n01; simp at n01; linarith
  have e11 : s11 ≠ 0 := by intro h; rw [h] at n11; simp at n11; linarith
  have hid : s11⁻¹ - s10⁻¹ - s01⁻¹ + s00⁻¹ = -(s11 - s10 - s01 + s00) / s00 ^ 2 +
      ((s11 - s00) ^ 2 / (s00 ^ 2 * s11) - (s10 - s00) ^ 2 / (s00 ^ 2 * s10) -
        (s01 - s00) ^ 2 / (s00 ^ 2 * s01)) := by
    field_simp; ring
  rw [hid]
  have b0 : ‖-(s11 - s10 - s01 + s00) / s00 ^ 2‖ ≤ 2 * Z := by
    rw [norm_div, norm_neg, norm_pow, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ≤ ‖s00‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg (s11 - s10 - s01 + s00)]
  have bq : ∀ s : ℂ, 19 / 20 ≤ ‖s‖ → ‖s - s00‖ ≤ t →
      ‖(s - s00) ^ 2 / (s00 ^ 2 * s)‖ ≤ 2 * t ^ 2 := by
    intro s hs ht
    rw [norm_div, norm_pow, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) / 2 ≤ ‖s00‖ ^ 2 * ‖s‖ := by
      nlinarith [mul_nonneg (norm_nonneg s00) (norm_nonneg s)]
    have h2 : ‖s - s00‖ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith [sq_nonneg ‖s - s00‖, sq_nonneg t]
  have b11 := bq s11 n11 t11
  have b10 := bq s10 n10 t10
  have b01 := bq s01 n01 t01
  calc _ ≤ ‖-(s11 - s10 - s01 + s00) / s00 ^ 2‖ +
        ‖(s11 - s00) ^ 2 / (s00 ^ 2 * s11) - (s10 - s00) ^ 2 / (s00 ^ 2 * s10) -
          (s01 - s00) ^ 2 / (s00 ^ 2 * s01)‖ := norm_add_le _ _
    _ ≤ _ := by
      have c1 := norm_sub_le ((s11 - s00) ^ 2 / (s00 ^ 2 * s11) -
        (s10 - s00) ^ 2 / (s00 ^ 2 * s10)) ((s01 - s00) ^ 2 / (s00 ^ 2 * s01))
      have c2 := norm_sub_le ((s11 - s00) ^ 2 / (s00 ^ 2 * s11))
        ((s10 - s00) ^ 2 / (s00 ^ 2 * s10))
      linarith

/-- The mixed second difference of a square root in terms of that of the radicand. -/
theorem sqrt_mixed_le {s00 s10 s01 s11 : ℂ} {Z t : ℝ} (h00 : 19 / 20 ≤ s00.re)
    (hZ : ‖s11 ^ 2 - s10 ^ 2 - s01 ^ 2 + s00 ^ 2‖ ≤ Z) (t10 : ‖s10 - s00‖ ≤ t)
    (t01 : ‖s01 - s00‖ ≤ t) (t11 : ‖s11 - s00‖ ≤ t) :
    ‖s11 - s10 - s01 + s00‖ ≤ Z + 3 * t ^ 2 := by
  have hid : 2 * s00 * (s11 - s10 - s01 + s00) =
      (s11 ^ 2 - s10 ^ 2 - s01 ^ 2 + s00 ^ 2) -
        ((s11 - s00) ^ 2 - (s10 - s00) ^ 2 - (s01 - s00) ^ 2) := by ring
  have hn : 1 ≤ ‖2 * s00‖ := by
    have := norm_ge_of_re h00
    rw [norm_mul]; simp; linarith
  have hq : ∀ s : ℂ, ‖s - s00‖ ≤ t → ‖(s - s00) ^ 2‖ ≤ t ^ 2 := by
    intro s hs
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs 2
  have q11 := hq s11 t11
  have q10 := hq s10 t10
  have q01 := hq s01 t01
  have : ‖2 * s00‖ * ‖s11 - s10 - s01 + s00‖ ≤ Z + 3 * t ^ 2 := by
    rw [← norm_mul, hid]
    have c1 := norm_sub_le (s11 ^ 2 - s10 ^ 2 - s01 ^ 2 + s00 ^ 2)
      ((s11 - s00) ^ 2 - (s10 - s00) ^ 2 - (s01 - s00) ^ 2)
    have c2 := norm_sub_le ((s11 - s00) ^ 2 - (s10 - s00) ^ 2) ((s01 - s00) ^ 2)
    have c3 := norm_sub_le ((s11 - s00) ^ 2) ((s10 - s00) ^ 2)
    linarith
  nlinarith [norm_nonneg (s11 - s10 - s01 + s00)]

end Scalar

section Vector

variable {N : ℕ}

/-- The mixed second difference of the squared norm. -/
theorem dot_mixed_le {v00 v10 v01 v11 : Fin N → ℂ} {a T1 T2 : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1 / 100)
    (nv0 : cNorm v00 ≤ 2 + a) (hT1 : 0 ≤ T1) (hT2' : 0 ≤ T2) (hT10 : cNorm (v10 - v00) ≤ T1)
    (hT01 : cNorm (v01 - v00) ≤ T1) (hT11 : cNorm (v11 - v00) ≤ T1)
    (hT2 : cNorm (v11 - v10 - v01 + v00) ≤ T2) :
    ‖v11 ⬝ᵥ v11 - v10 ⬝ᵥ v10 - v01 ⬝ᵥ v01 + v00 ⬝ᵥ v00‖ ≤ 5 * T2 + 3 * T1 ^ 2 := by
  have hid : v11 ⬝ᵥ v11 - v10 ⬝ᵥ v10 - v01 ⬝ᵥ v01 + v00 ⬝ᵥ v00 =
      2 * (v00 ⬝ᵥ (v11 - v10 - v01 + v00)) + (v11 - v00) ⬝ᵥ (v11 - v00) -
        (v10 - v00) ⬝ᵥ (v10 - v00) - (v01 - v00) ⬝ᵥ (v01 - v00) := by
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hid]
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  have c1 : ‖2 * (v00 ⬝ᵥ (v11 - v10 - v01 + v00))‖ ≤ 2 * ((2 + a) * T2) := by
    rw [norm_mul, n2]
    exact mul_le_mul_of_nonneg_left ((cNorm_dot_le _ _).trans
      (mul_le_mul nv0 hT2 (cNorm_nonneg _) (by positivity))) (by norm_num)
  have q : ∀ w : Fin N → ℂ, cNorm w ≤ T1 → ‖w ⬝ᵥ w‖ ≤ T1 ^ 2 := fun w hw =>
    (cNorm_dot_le _ _).trans (by
      have := mul_le_mul hw hw (cNorm_nonneg _) hT1; linarith [sq T1])
  have q1 := q _ hT11
  have q2 := q _ hT10
  have q3 := q _ hT01
  have d1 := norm_sub_le (2 * (v00 ⬝ᵥ (v11 - v10 - v01 + v00)) +
    (v11 - v00) ⬝ᵥ (v11 - v00) - (v10 - v00) ⬝ᵥ (v10 - v00)) ((v01 - v00) ⬝ᵥ (v01 - v00))
  have d2 := norm_sub_le (2 * (v00 ⬝ᵥ (v11 - v10 - v01 + v00)) +
    (v11 - v00) ⬝ᵥ (v11 - v00)) ((v10 - v00) ⬝ᵥ (v10 - v00))
  have d3 := norm_add_le (2 * (v00 ⬝ᵥ (v11 - v10 - v01 + v00)))
    ((v11 - v00) ⬝ᵥ (v11 - v00))
  have t6 : (2 + a) * T2 ≤ 2.01 * T2 := by nlinarith
  linarith

/-- The Leibniz expansion of `r v` and its bound. -/
theorem leibniz_mixed_le {r00 r10 r01 r11 : ℂ} {v00 v10 v01 v11 : Fin N → ℂ}
    {a T1 T2 R P : ℝ} (u0 : ‖r00‖ ≤ 20 / 19) (nv0 : cNorm v00 ≤ 2 + a)
    (hT10 : cNorm (v10 - v00) ≤ T1)
    (hT01 : cNorm (v01 - v00) ≤ T1) (hT11 : cNorm (v11 - v00) ≤ T1)
    (hT2 : cNorm (v11 - v10 - v01 + v00) ≤ T2) (hR : ‖r11 - r10 - r01 + r00‖ ≤ R)
    (hP10 : ‖r10 - r00‖ ≤ P) (hP01 : ‖r01 - r00‖ ≤ P) (hP11 : ‖r11 - r00‖ ≤ P) :
    cNorm (r11 • v11 - r10 • v10 - r01 • v01 + r00 • v00) ≤
      20 / 19 * T2 + R * (2 + a) + 3 * (P * T1) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hR
  have hP0 : 0 ≤ P := le_trans (norm_nonneg _) hP10
  have e : r11 • v11 - r10 • v10 - r01 • v01 + r00 • v00 =
      r00 • (v11 - v10 - v01 + v00) + (r11 - r10 - r01 + r00) • v00 +
        (r11 - r00) • (v11 - v00) - (r10 - r00) • (v10 - v00) - (r01 - r00) • (v01 - v00) := by
    funext i; simp [Pi.sub_apply, Pi.smul_apply, Pi.add_apply]; ring
  rw [e]
  have f1 : cNorm (r00 • (v11 - v10 - v01 + v00)) ≤ 20 / 19 * T2 := by
    rw [cNorm_smul]; exact mul_le_mul u0 hT2 (cNorm_nonneg _) (by norm_num)
  have f2 : cNorm ((r11 - r10 - r01 + r00) • v00) ≤ R * (2 + a) := by
    rw [cNorm_smul]; exact mul_le_mul hR nv0 (cNorm_nonneg _) hR0
  have f3 : cNorm ((r11 - r00) • (v11 - v00)) ≤ P * T1 := by
    rw [cNorm_smul]; exact mul_le_mul hP11 hT11 (cNorm_nonneg _) hP0
  have f4 : cNorm ((r10 - r00) • (v10 - v00)) ≤ P * T1 := by
    rw [cNorm_smul]; exact mul_le_mul hP10 hT10 (cNorm_nonneg _) hP0
  have f5 : cNorm ((r01 - r00) • (v01 - v00)) ≤ P * T1 := by
    rw [cNorm_smul]; exact mul_le_mul hP01 hT01 (cNorm_nonneg _) hP0
  have g1 := cNorm_sub_le (r00 • (v11 - v10 - v01 + v00) + (r11 - r10 - r01 + r00) • v00 +
    (r11 - r00) • (v11 - v00) - (r10 - r00) • (v10 - v00)) ((r01 - r00) • (v01 - v00))
  have g2 := cNorm_sub_le (r00 • (v11 - v10 - v01 + v00) + (r11 - r10 - r01 + r00) • v00 +
    (r11 - r00) • (v11 - v00)) ((r10 - r00) • (v10 - v00))
  have g3 := cNorm_add_le (r00 • (v11 - v10 - v01 + v00) + (r11 - r10 - r01 + r00) • v00)
    ((r11 - r00) • (v11 - v00))
  have g4 := cNorm_add_le (r00 • (v11 - v10 - v01 + v00)) ((r11 - r10 - r01 + r00) • v00)
  linarith

/-- **Four-point version of `normalize_bounds`.**  Four vectors within `a ≤ 1/100` of a unit
reference vector, with first differences from `v₀₀` at most `T₁` and mixed second difference at
most `T₂`: the mixed second difference of `normalize` is at most `22 T₂ + 650 T₁²`. -/
theorem normalize_mixed {ref v00 v10 v01 v11 : Fin N → ℂ} {a T1 T2 : ℝ}
    (href : ref ⬝ᵥ ref = 1) (hrefn : cNorm ref ≤ 2) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 100)
    (h00 : cNorm (v00 - ref) ≤ a) (h10 : cNorm (v10 - ref) ≤ a) (h01 : cNorm (v01 - ref) ≤ a)
    (h11 : cNorm (v11 - ref) ≤ a) (hT10 : cNorm (v10 - v00) ≤ T1)
    (hT01 : cNorm (v01 - v00) ≤ T1) (hT11 : cNorm (v11 - v00) ≤ T1)
    (hT2 : cNorm (v11 - v10 - v01 + v00) ≤ T2) :
    cNorm (normalize v11 - normalize v10 - normalize v01 + normalize v00) ≤
      22 * T2 + 650 * T1 ^ 2 := by
  have hT1 : 0 ≤ T1 := le_trans (cNorm_nonneg _) hT10
  have hT2' : 0 ≤ T2 := le_trans (cNorm_nonneg _) hT2
  obtain ⟨nv0, -, -, s0r⟩ := sqrt_facts href hrefn ha0 ha h00
  obtain ⟨nv1, -, -, s1r⟩ := sqrt_facts href hrefn ha0 ha h10
  obtain ⟨nv2, -, -, s2r⟩ := sqrt_facts href hrefn ha0 ha h01
  obtain ⟨nv3, -, -, s3r⟩ := sqrt_facts href hrefn ha0 ha h11
  have e00 := sqrtDot_sq v00
  have e10 := sqrtDot_sq v10
  have e01 := sqrtDot_sq v01
  have e11 := sqrtDot_sq v11
  have zdiff : ∀ v : Fin N → ℂ, cNorm v ≤ 2 + a → cNorm (v - v00) ≤ T1 →
      ‖v ⬝ᵥ v - v00 ⬝ᵥ v00‖ ≤ 5 * T1 := by
    intro v hv hT
    rw [← dot_sub_add]
    refine (cNorm_dot_le _ _).trans ?_
    have : cNorm (v + v00) ≤ 4 + 2 * a := by
      have := cNorm_add_le v v00; linarith
    calc cNorm (v - v00) * cNorm (v + v00) ≤ T1 * (4 + 2 * a) :=
          mul_le_mul hT this (cNorm_nonneg _) hT1
      _ ≤ 5 * T1 := by nlinarith
  have t10 : ‖sqrtDot v10 - sqrtDot v00‖ ≤ 5 * T1 :=
    (sqrt_sub_le s0r s1r e00 e10).trans (zdiff v10 nv1 hT10)
  have t01 : ‖sqrtDot v01 - sqrtDot v00‖ ≤ 5 * T1 :=
    (sqrt_sub_le s0r s2r e00 e01).trans (zdiff v01 nv2 hT01)
  have t11 : ‖sqrtDot v11 - sqrtDot v00‖ ≤ 5 * T1 :=
    (sqrt_sub_le s0r s3r e00 e11).trans (zdiff v11 nv3 hT11)
  have hΔz : ‖sqrtDot v11 ^ 2 - sqrtDot v10 ^ 2 - sqrtDot v01 ^ 2 + sqrtDot v00 ^ 2‖ ≤
      5 * T2 + 3 * T1 ^ 2 := by
    rw [e00, e10, e01, e11]
    exact dot_mixed_le ha0 ha nv0 hT1 hT2' hT10 hT01 hT11 hT2
  have hΔs := sqrt_mixed_le s0r hΔz t10 t01 t11
  have hΔr := inv_mixed_le s0r s1r s2r s3r hΔs t10 t01 t11
  have hunit : ‖(sqrtDot v00)⁻¹‖ ≤ 20 / 19 := by
    have := norm_ge_of_re s0r
    rw [norm_inv]; rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hρ : ∀ sj : ℂ, 19 / 20 ≤ sj.re → ‖sj - sqrtDot v00‖ ≤ 5 * T1 →
      ‖sj⁻¹ - (sqrtDot v00)⁻¹‖ ≤ 10 * T1 := by
    intro sj hj hs
    have := inv_sub_le s0r hj
    linarith
  have key := leibniz_mixed_le (r00 := (sqrtDot v00)⁻¹) (r10 := (sqrtDot v10)⁻¹)
    (r01 := (sqrtDot v01)⁻¹) (r11 := (sqrtDot v11)⁻¹) hunit nv0 hT10 hT01 hT11 hT2
    (R := 2 * (5 * T2 + 3 * T1 ^ 2 + 3 * (5 * T1) ^ 2) + 6 * (5 * T1) ^ 2)
    (P := 10 * T1) (by
      refine hΔr.trans ?_
      nlinarith)
    (hρ _ s1r t10) (hρ _ s2r t01) (hρ _ s3r t11)
  have e : normalize v11 - normalize v10 - normalize v01 + normalize v00 =
      (sqrtDot v11)⁻¹ • v11 - (sqrtDot v10)⁻¹ • v10 - (sqrtDot v01)⁻¹ • v01 +
        (sqrtDot v00)⁻¹ • v00 := rfl
  rw [e]
  have hb : (2 * (5 * T2 + 3 * T1 ^ 2 + 3 * (5 * T1) ^ 2) + 6 * (5 * T1) ^ 2) * (2 + a) ≤
      (10 * T2 + 306 * T1 ^ 2) * 2.01 := by
    have : (2 * (5 * T2 + 3 * T1 ^ 2 + 3 * (5 * T1) ^ 2) + 6 * (5 * T1) ^ 2) =
        10 * T2 + 306 * T1 ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (10 * T2 + 306 * T1 ^ 2) * 2.01 = 20.1 * T2 + 615.06 * T1 ^ 2 := by ring
  rw [h2] at hb
  nlinarith [sq_nonneg T1]

end Vector

end Balaban.Background
