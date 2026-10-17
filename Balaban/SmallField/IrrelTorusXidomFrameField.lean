/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomRealFrame
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The field coordinate in a real-centre frame
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

/-- The source chart bounds control all rotated field coordinates, with quadratic control
on the longitudinal coordinate. -/
theorem realFrame_field_coords {N : ℕ} {i₀ : Fin N}
    {p h : Fin N → ℝ} {z h' : Fin N → ℂ} {ν τ ζ : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hζ : 0 < ζ) (hντ : ν ≤ τ ^ 2)
    (hp : |∑ i, p i ^ 2 - 1| < τ ^ 2 * ζ)
    (hz : vn z < ζ + τ * ζ)
    (hbclose : ‖((ν : ℂ) • fun i => (h i : ℂ) + h' i) -
      ((ν : ℂ) • fun i => (p i : ℂ) + z i)‖ ≤ 10 * τ ^ 2 * ζ)
    (hr : ν * |1 - (∑ i, p i * h i) / rn p| < τ ^ 2 * ζ ^ 2)
    (hc : ν * ‖∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ < τ ^ 2 * ζ ^ 2)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.transpose * Q = 1)
    (hQp : Q.mulVec p = rn p • (Pi.single i₀ 1 : Fin N → ℝ))
    (hQe : Q.transpose.mulVec (Pi.single i₀ 1 : Fin N → ℝ) =
      fun i => p i / rn p) :
    (∀ i, ‖((cmat Q).mulVec (((ν : ℂ) • fun l => (h l : ℂ) + h' l))) i -
      (ν : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ 13 * N * τ ^ 2 * ζ) ∧
    ‖((cmat Q).mulVec (((ν : ℂ) • fun l => (h l : ℂ) + h' l))) i₀ - ν‖ <
      2 * τ ^ 2 * ζ ^ 2 := by
  let v : Fin N → ℂ := fun i => (p i : ℂ) + z i
  let b : Fin N → ℂ := (ν : ℂ) • fun i => (h i : ℂ) + h' i
  let e : Fin N → ℂ := Pi.single i₀ 1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hν0 : 0 ≤ ν := hν.le
  have hτ2 : τ ^ 2 ≤ 1 := by nlinarith [sq_nonneg τ]
  have hν1 : ν ≤ 1 := hντ.trans hτ2
  have hv : ‖(cmat Q).mulVec v - e‖ ≤ τ ^ 2 * ζ + 2 * N * ζ := by
    apply (pi_norm_le_iff_of_nonneg ?_).2
    · intro i
      simpa only [Pi.sub_apply] using
        realFrame_source_center_close hτ1 hζ hp hz hQ hQp i
    · positivity
  have hbQ : ‖(cmat Q).mulVec b - (ν : ℂ) • e‖ ≤ 13 * N * τ ^ 2 * ζ := by
    have he : (cmat Q).mulVec b - (ν : ℂ) • e =
        (cmat Q).mulVec (b - (ν : ℂ) • v) +
          (ν : ℂ) • ((cmat Q).mulVec v - e) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
      abel_nf
    rw [he]
    have h1 : ‖(cmat Q).mulVec (b - (ν : ℂ) • v)‖ ≤
        10 * N * τ ^ 2 * ζ := by
      calc
        _ ≤ N * ‖b - (ν : ℂ) • v‖ := realOrth_mulVec_norm_le hQ _
        _ ≤ N * (10 * τ ^ 2 * ζ) :=
          mul_le_mul_of_nonneg_left hbclose (Nat.cast_nonneg N)
        _ = 10 * N * τ ^ 2 * ζ := by ring
    have h2 : ‖(ν : ℂ) • ((cmat Q).mulVec v - e)‖ ≤
        3 * N * τ ^ 2 * ζ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]
      calc
        _ ≤ ν * (τ ^ 2 * ζ + 2 * N * ζ) :=
          mul_le_mul_of_nonneg_left hv hν0
        _ ≤ 3 * N * τ ^ 2 * ζ := by
          have hpart1 : ν * (τ ^ 2 * ζ) ≤ N * τ ^ 2 * ζ := by
            convert mul_le_mul_of_nonneg_right (hν1.trans hN)
              (by positivity : 0 ≤ τ ^ 2 * ζ) using 1; ring
          have hpart2 : ν * (2 * N * ζ) ≤ τ ^ 2 * (2 * N * ζ) :=
            mul_le_mul_of_nonneg_right hντ (by positivity)
          nlinarith [hpart1, hpart2]
    calc
      _ ≤ ‖(cmat Q).mulVec (b - (ν : ℂ) • v)‖ +
          ‖(ν : ℂ) • ((cmat Q).mulVec v - e)‖ := norm_add_le _ _
      _ ≤ 13 * N * τ ^ 2 * ζ := by nlinarith [h1, h2]
  constructor
  · intro i
    have hi := norm_le_pi_norm ((cmat Q).mulVec b - (ν : ℂ) • e) i
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hi.trans hbQ
  · exact realFrame_source_longitudinal hν hQe hr hc

end Balaban.SmallField
