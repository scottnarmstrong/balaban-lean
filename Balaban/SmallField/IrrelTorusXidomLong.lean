/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomSquare
public import Balaban.SmallField.RenormAnisoCtx
public import Balaban.SmallField.PsiGeomTube
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

open Balaban.Background Balaban.Multiscale

/-- Normalizing a complex spin changes its real longitudinal coefficient only quadratically
in the transverse displacement. -/
theorem normalized_longitudinal_le
    {q w z : ℂ} {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hsq : w ^ 2 = q ^ 2 + z ^ 2)
    (hw : 3 / 4 ≤ ‖w‖) (hwq : 3 / 2 ≤ ‖w + q‖)
    (hz : ‖z‖ ≤ 2 * ζ) :
    ‖q / w - 1‖ ≤ 8 * ζ ^ 2 ∧ ‖z / w‖ ≤ 4 * ζ := by
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
    linarith
  have hwq0 : w + q ≠ 0 := by
    intro h
    simp [h] at hwq
    linarith
  have he : q / w - 1 = -(z ^ 2) / (w * (w + q)) := by
    field_simp [hw0, hwq0]
    linear_combination -hsq
  have hzn : ‖z‖ ^ 2 ≤ 4 * ζ ^ 2 := by
    nlinarith only [hz, hζ, norm_nonneg z, sq_nonneg (‖z‖ - 2 * ζ)]
  have hden : 9 / 8 ≤ ‖w‖ * ‖w + q‖ := by
    nlinarith only [hw, hwq, norm_nonneg w, norm_nonneg (w + q),
      mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hwq)]
  constructor
  · rw [he, norm_div, norm_neg, norm_pow, norm_mul]
    have hden0 : 0 < ‖w‖ * ‖w + q‖ := by linarith
    apply (div_le_iff₀ hden0).2
    calc
      ‖z‖ ^ 2 ≤ 4 * ζ ^ 2 := hzn
      _ ≤ (8 * ζ ^ 2) * (‖w‖ * ‖w + q‖) := by
        nlinarith only [hden, sq_nonneg ζ, mul_nonneg (sq_nonneg ζ) (sub_nonneg.mpr hden)]
  · rw [norm_div]
    have hwpos : 0 < ‖w‖ := by linarith
    apply (div_le_iff₀ hwpos).2
    nlinarith only [hz, hw, hζ, mul_nonneg hζ (sub_nonneg.mpr hw)]

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

/-- The longitudinal invariant of a source tube datum has the required quadratic size.
The weaker complex spin size from scaled composition is absorbed by doubling the tube radius. -/
theorem vInv_bound_of_source_tube {d N : ℕ}
    {p h : Fin N → ℝ} {z h' : Fin N → ℂ}
    {ν τ ζ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν ≤ τ ^ 2) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hp : |∑ i, p i ^ 2 - 1| < τ ^ 2 * ζ)
    (hh1 : ν * |1 - (∑ i, p i * h i) / rn p| < τ ^ 2 * ζ ^ 2)
    (hh2 : ν * |∑ i, h i ^ 2 - 1| < τ ^ 2 * ζ ^ 2)
    (hz : vn z < ζ + τ * ζ)
    (hsq : ‖∑ i, ((p i : ℂ) + z i) * ((p i : ℂ) + z i) -
      ∑ i, (p i : ℂ) * (p i : ℂ)‖ < τ ^ 2 * ζ)
    (hh' : ν * vn h' < τ ^ 2 * ζ)
    (hph' : ν * ‖∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ < τ ^ 2 * ζ ^ 2) :
    ‖vInv (fun _ : Site d => fun i => (p i : ℂ) + z i)
      ((ν : ℂ) • fun i => (h i : ℂ) + h' i) - ν‖ ≤
      98 * τ ^ 2 * ζ ^ 2 := by
  have hζ2 : 0 < 2 * ζ := by positivity
  have hζ200 : 2 * ζ ≤ 1 / 100 := by linarith
  have hp2 : |∑ i, p i ^ 2 - 1| < τ ^ 2 * (2 * ζ) := by
    nlinarith [sq_nonneg τ]
  have hh12 : ν * |1 - (∑ i, p i * h i) / rn p| < τ ^ 2 * (2 * ζ) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg ζ, mul_nonneg (sq_nonneg τ) (sq_nonneg ζ)]
  have hh22 : ν * |∑ i, h i ^ 2 - 1| < τ ^ 2 * (2 * ζ) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg ζ, mul_nonneg (sq_nonneg τ) (sq_nonneg ζ)]
  have hz2 : vn z < 2 * ζ + τ ^ 2 * (2 * ζ) := by
    nlinarith [sq_nonneg τ]
  have hsq2 : ‖∑ i, ((p i : ℂ) + z i) * ((p i : ℂ) + z i) -
      ∑ i, (p i : ℂ) * (p i : ℂ)‖ < τ ^ 2 * (2 * ζ) := by
    nlinarith [sq_nonneg τ]
  have hh'2 : ν * vn h' < τ ^ 2 * (2 * ζ) := by
    nlinarith [sq_nonneg τ]
  have hph'2 : ν * ‖∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ <
      τ ^ 2 * (2 * ζ) ^ 2 := by
    nlinarith [sq_nonneg τ, sq_nonneg ζ, mul_nonneg (sq_nonneg τ) (sq_nonneg ζ)]
  have hv := lemma33_tube hν hτ hτ1 hντ hζ2 hζ200 hp2 hh12 hh22 hz2 hsq2 hh'2 hph'2
  have he : vInv (fun _ : Site d => fun i => (p i : ℂ) + z i)
      ((ν : ℂ) • fun i => (h i : ℂ) + h' i) =
      (ν : ℂ) * tubeV p z h h' := by
    unfold vInv uInv sqrtC tubeV tubeU uExt dot dotc
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm _ (ν : ℂ)]
    rw [← Finset.mul_sum]
    ring
  rw [he]
  have he2 : (ν : ℂ) * tubeV p z h h' - ν = (ν : ℂ) * (tubeV p z h h' - 1) := by ring
  rw [he2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]
  have hV := hv.2.1
  have hV' : ν * ‖tubeV p z h h' - 1‖ <
      ν * (1 / 2 * (7 * τ) ^ 2 * (2 * ζ) ^ 2 / ν) :=
    mul_lt_mul_of_pos_left hV hν
  have hν0 : ν ≠ 0 := hν.ne'
  calc
    ν * ‖tubeV p z h h' - 1‖
        ≤ ν * (1 / 2 * (7 * τ) ^ 2 * (2 * ζ) ^ 2 / ν) := hV'.le
    _ = 98 * τ ^ 2 * ζ ^ 2 := by field_simp [hν0]; ring

end Balaban.SmallField
