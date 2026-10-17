/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomLocal
public import Balaban.Symmetry.Rotation
import Balaban.SmallField.XiUnitWitness
import Mathlib.Tactic.Linarith

/-!
# Coordinate control for a real orthogonal frame
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Matrix Finset

/-- Every entry of a real orthogonal matrix has absolute value at most one. -/
theorem realOrth_entry_abs_le_one {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.transpose * Q = 1) (i k : Fin N) : |Q i k| ≤ 1 := by
  have hcol : ∑ l : Fin N, (Q l k) ^ 2 = 1 := by
    have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M k k) hQ
    simpa [Matrix.mul_apply, dotProduct, sq] using hh
  have hle : (Q i k) ^ 2 ≤ ∑ l : Fin N, (Q l k) ^ 2 := by
    exact Finset.single_le_sum (fun l _ => sq_nonneg (Q l k)) (Finset.mem_univ i)
  rw [hcol] at hle
  nlinarith [abs_nonneg (Q i k), sq_abs (Q i k)]

/-- A nonzero real centre admits an orthogonal frame that carries its normalized vector to
the reference coordinate, with a uniform entry bound. -/
theorem exists_real_center_frame {N : ℕ} {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁)
    (p : Fin N → ℝ) (hp : 0 < rn p) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ,
      Q.transpose * Q = 1 ∧
      Q.mulVec p = rn p • (Pi.single i₀ 1 : Fin N → ℝ) ∧
      Q.mulVec (fun i => p i / rn p) = Pi.single i₀ 1 ∧
      ∀ i k, |Q i k| ≤ 1 := by
  have hp0 : p ≠ 0 := by
    intro he
    subst p
    simp [rn] at hp
  obtain ⟨Q, hQ, hQp, -⟩ := Balaban.Symmetry.exists_rotation hne p p hp0
  have heq : Real.sqrt (p ⬝ᵥ p) = rn p := by
    simp [rn, dotProduct, sq]
  rw [heq] at hQp
  refine ⟨Q, hQ, hQp, ?_, realOrth_entry_abs_le_one hQ⟩
  have hnorm : (fun i => p i / rn p) = (rn p)⁻¹ • p := by
    funext i
    simp [smul_eq_mul, inv_mul_eq_div]
  rw [hnorm, Matrix.mulVec_smul, hQp, smul_smul]
  simp [hp.ne']

/-- Real orthogonal rotations have a simple coordinate-maximum bound after complexification. -/
theorem realOrth_mulVec_norm_le {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℝ}
    (hQ : Q.transpose * Q = 1) (w : Fin N → ℂ) :
    ‖(cmat Q).mulVec w‖ ≤ N * ‖w‖ := by
  have hbd : ∀ i k, ‖cmat Q i k‖ ≤ 1 := by
    intro i k
    simpa [cmat] using realOrth_entry_abs_le_one hQ i k
  simpa only [mul_one] using norm_mulVec_le (by norm_num : (0 : ℝ) ≤ 1) hbd w

/-- In the real-centre frame the complex source spin is close to the reference coordinate. -/
theorem realFrame_source_center_close {N : ℕ} {i₀ : Fin N}
    {p : Fin N → ℝ} {z : Fin N → ℂ} {τ ζ : ℝ}
    (hτ1 : τ ≤ 1) (hζ : 0 < ζ)
    (hp : |∑ i, p i ^ 2 - 1| < τ ^ 2 * ζ)
    (hz : vn z < ζ + τ * ζ)
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Q.transpose * Q = 1)
    (hQp : Q.mulVec p = rn p • (Pi.single i₀ 1 : Fin N → ℝ)) :
    ∀ i, ‖(cmat Q).mulVec (fun l => (p l : ℂ) + z l) i -
      (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ τ ^ 2 * ζ + 2 * N * ζ := by
  have hzpi : ‖z‖ ≤ vn z :=
    (pi_norm_le_iff_of_nonneg (vn_nonneg z)).2 fun i => norm_le_vn z i
  have hzQ : ‖(cmat Q).mulVec z‖ ≤ 2 * N * ζ := by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc
      _ ≤ N * ‖z‖ := realOrth_mulVec_norm_le hQ z
      _ ≤ N * vn z := mul_le_mul_of_nonneg_left hzpi hN
      _ ≤ 2 * N * ζ := by
        have hζ2 : vn z ≤ 2 * ζ := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hτ1) hζ.le]
        nlinarith [mul_nonneg hN (sub_nonneg.mpr hζ2)]
  have hpclose : |rn p - 1| ≤ τ ^ 2 * ζ := by
    exact (abs_rn_sub_one_le p).trans hp.le
  have hQpc : (cmat Q).mulVec (fun l => (p l : ℂ)) =
      (rn p : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) := by
    funext i
    rw [← cmat_mulVec Q p i, hQp]
    by_cases hi : i = i₀ <;> simp [Pi.smul_apply, smul_eq_mul, hi]
  intro i
  have he : (cmat Q).mulVec (fun l => (p l : ℂ) + z l) =
      (rn p : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) + (cmat Q).mulVec z := by
    rw [← hQpc, ← Matrix.mulVec_add]
    rfl
  rw [he]
  have hpi : ‖((cmat Q).mulVec z) i‖ ≤ ‖(cmat Q).mulVec z‖ := norm_le_pi_norm _ i
  have hrad : ‖(rn p : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i -
      (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ |rn p - 1| := by
    by_cases hi : i = i₀
    · subst i
      simpa only [Pi.single_eq_same, mul_one] using show
        ‖(rn p : ℂ) - 1‖ ≤ |rn p - 1| by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    · simp [Pi.single_eq_of_ne hi]
  have htri : ‖((rn p : ℂ) • (Pi.single i₀ 1 : Fin N → ℂ) +
      (cmat Q).mulVec z) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      ‖(rn p : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i -
        (Pi.single i₀ 1 : Fin N → ℂ) i‖ + ‖((cmat Q).mulVec z) i‖ := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    convert norm_add_le ((rn p : ℂ) * (Pi.single i₀ 1 : Fin N → ℂ) i -
      (Pi.single i₀ 1 : Fin N → ℂ) i) (((cmat Q).mulVec z) i) using 1; abel_nf
  exact htri.trans (by linarith)

/-- The reference row of an orthogonal real-centre frame is the normalized centre. -/
theorem realOrth_transpose_frame {N : ℕ} {i₀ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} {p : Fin N → ℝ}
    (hQ : Q.transpose * Q = 1)
    (hQnorm : Q.mulVec (fun i => p i / rn p) = (Pi.single i₀ 1 : Fin N → ℝ)) :
    Q.transpose.mulVec (Pi.single i₀ 1 : Fin N → ℝ) = fun i => p i / rn p := by
  rw [← hQnorm, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

/-- The longitudinal coordinate of the rotated field inherits the quadratic source bounds. -/
theorem realFrame_source_longitudinal {N : ℕ} {i₀ : Fin N}
    {Q : Matrix (Fin N) (Fin N) ℝ} {p h : Fin N → ℝ} {h' : Fin N → ℂ}
    {ν τ ζ : ℝ} (hν : 0 < ν)
    (hQe : Q.transpose.mulVec (Pi.single i₀ 1 : Fin N → ℝ) =
      fun i => p i / rn p)
    (hr : ν * |1 - (∑ i, p i * h i) / rn p| < τ ^ 2 * ζ ^ 2)
    (hc : ν * ‖∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ < τ ^ 2 * ζ ^ 2) :
    ‖((cmat Q).mulVec (((ν : ℂ) • fun i => (h i : ℂ) + h' i))) i₀ - ν‖ <
      2 * τ ^ 2 * ζ ^ 2 := by
  have hrow (i : Fin N) : Q i₀ i = p i / rn p := by
    have hh := congrFun hQe i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hh
  have he : ((cmat Q).mulVec (((ν : ℂ) • fun i => (h i : ℂ) + h' i))) i₀ - ν =
      (ν : ℂ) * (((∑ i, p i * h i) / rn p : ℝ) - 1) +
        (ν : ℂ) * ∑ i, ((p i / rn p : ℝ) : ℂ) * h' i := by
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, cmat,
      Matrix.map_apply, hrow]
    push_cast
    have hsplit : (∑ i, (p i : ℂ) / (rn p : ℂ) *
        ((ν : ℂ) * ((h i : ℂ) + h' i))) =
        ∑ i, ((ν : ℂ) * ((p i : ℂ) / (rn p : ℂ) * (h i : ℂ)) +
          (ν : ℂ) * ((p i : ℂ) / (rn p : ℂ) * h' i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsplit]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hd : (∑ i, (p i : ℂ) / (rn p : ℂ) * (h i : ℂ)) =
        (∑ i, (p i : ℂ) * (h i : ℂ)) / (rn p : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hd]
    ring
  rw [he]
  have hr' : ν * |(∑ i, p i * h i) / rn p - 1| < τ ^ 2 * ζ ^ 2 := by
    rwa [abs_sub_comm] at hr
  have h1 : ‖(ν : ℂ) * (((∑ i, p i * h i) / rn p : ℝ) - 1)‖ <
      τ ^ 2 * ζ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hr'
  have h2 : ‖(ν : ℂ) * ∑ i, ((p i / rn p : ℝ) : ℂ) * h' i‖ <
      τ ^ 2 * ζ ^ 2 := by
    rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]
  exact (norm_add_le _ _).trans_lt (by linarith)

end Balaban.SmallField
