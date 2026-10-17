/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.Green.KF0WalkTorus

/-!
# Positive finite-range atoms of the bare massive covariance

The exact even/odd walk pairing from `KF0B.md`, Round 3, equations (B.22)–(B.23).
For `A = kf0Adj d m`, `a = 2d + ν`, the atom at index `n` is
`a⁻²ⁿ⁻² Aⁿ (a I + A) Aⁿ`. Its entries vanish beyond graph distance `2n+1`,
its quadratic form is nonnegative, and its sum is `(-Δ+ν)⁻¹`.
These facts do not assert finite-range dependence of nonlinear spin observables.
-/

@[expose] public section


open scoped Classical
open Finset Matrix

namespace Balaban.Green

theorem kf0CovAtom_form_nonneg {d m : ℕ} [NeZero m] {ν : ℝ} (hν : 0 < ν)
    (n : ℕ) (u : Torus d m → ℝ) :
    0 ≤ u ⬝ᵥ
      (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) *ᵥ u := by
  let A := kf0Adj d m
  let a : ℝ := 2 * d + ν
  let v := A ^ n *ᵥ u
  have hv : 0 ≤ v ⬝ᵥ ((a • (1 : Matrix (Torus d m) (Torus d m) ℝ)) + A) *ᵥ v := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hA := kf0Adj_form_ge (d := d) (m := m) v
    have hsq := dot_self_nonneg' v
    dsimp [a, A] at *
    nlinarith
  have he : u ⬝ᵥ (A ^ n * (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) *
      A ^ n) *ᵥ u = v ⬝ᵥ (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) *ᵥ v := by
    simp only [← Matrix.mulVec_mulVec]
    change u ⬝ᵥ A ^ n *ᵥ ((a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) *ᵥ v) = _
    exact dot_mulVec_symm _ (kf0Adj_pow_transpose n) u _
  change 0 ≤ u ⬝ᵥ ((a ^ (2 * n + 2))⁻¹ •
    (A ^ n * (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) * A ^ n)) *ᵥ u
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, he]
  exact mul_nonneg (by positivity) hv

theorem kf0CovAtom_posSemidef {d m : ℕ} [NeZero m] {ν : ℝ} (hν : 0 < ν)
    (n : ℕ) :
    (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))).PosSemidef := by
  let A := kf0Adj d m
  let a : ℝ := 2 * d + ν
  have hsym : ((a ^ (2 * n + 2))⁻¹ •
      (A ^ n * (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) * A ^ n))ᵀ =
      (a ^ (2 * n + 2))⁻¹ •
      (A ^ n * (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) * A ^ n) := by
    rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      kf0Adj_pow_transpose, kf0Adj_transpose]
    simp only [A, Matrix.mul_assoc]
  have hherm : (((a ^ (2 * n + 2))⁻¹ •
      (A ^ n * (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) * A ^ n))).IsHermitian := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hsym
  change ((a ^ (2 * n + 2))⁻¹ •
    (A ^ n * (a • (1 : Matrix (Torus d m) (Torus d m) ℝ) + A) * A ^ n)).PosSemidef
  exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun u => by
    simpa only [star_trivial] using kf0CovAtom_form_nonneg hν n u)

theorem kf0CovAtom_expand {d m : ℕ} [NeZero m] (ν : ℝ) (n : ℕ) :
    (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) =
      (((2 * d + ν) ^ (2 * n + 2))⁻¹ * (2 * d + ν)) •
        (kf0Adj d m ^ (2 * n)) +
      ((2 * d + ν) ^ (2 * n + 2))⁻¹ • (kf0Adj d m ^ (2 * n + 1)) := by
  let A := kf0Adj d m
  let a : ℝ := 2 * d + ν
  change (a ^ (2 * n + 2))⁻¹ • (A ^ n * (a • 1 + A) * A ^ n) =
    ((a ^ (2 * n + 2))⁻¹ * a) • A ^ (2 * n) +
      (a ^ (2 * n + 2))⁻¹ • A ^ (2 * n + 1)
  have hmatrix : A ^ n * (a • 1 + A) * A ^ n =
      a • A ^ (2 * n) + A ^ (2 * n + 1) := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one]
    rw [show 2 * n = n + n by omega, pow_add]
    rw [show n + n + 1 = n + 1 + n by omega, pow_add, pow_succ]
  rw [hmatrix, smul_add, smul_smul]

theorem kf0CovAtom_entry_nonneg {d m : ℕ} [NeZero m] {ν : ℝ}
    (hν : 0 < ν) (n : ℕ) (x y : Torus d m) :
    0 ≤ ((((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) x y) := by
  rw [kf0CovAtom_expand]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have ha : 0 < 2 * (d : ℝ) + ν := by positivity
  exact add_nonneg
    (mul_nonneg (by positivity) (kf0Adj_pow_nonneg (2 * n) x y))
    (mul_nonneg (by positivity) (kf0Adj_pow_nonneg (2 * n + 1) x y))

/-- Exact uniform row mass of one covariance atom. Together with entrywise positivity,
this is its `ℓ¹` row norm and gives geometric summability since `2d/(2d+ν)<1`. -/
theorem kf0CovAtom_rowSum {d m : ℕ} [NeZero m] (ν : ℝ)
    (n : ℕ) (x : Torus d m) :
    ∑ y : Torus d m,
      (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) x y =
      (((2 * d + ν) ^ (2 * n + 2))⁻¹ * (2 * d + ν)) * (2 * d : ℝ) ^ (2 * n) +
        ((2 * d + ν) ^ (2 * n + 2))⁻¹ * (2 * d : ℝ) ^ (2 * n + 1) := by
  simp_rw [kf0CovAtom_expand, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    kf0Adj_pow_rowSum, kf0Adj_pow_rowSum]

theorem kf0CovAtom_range {d m : ℕ} [NeZero m] (ν : ℝ)
    (n : ℕ) (x y : Torus d m)
    (hfar : (2 * n + 1 : ℝ) < torusDist d m x y) :
    (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) x y = 0 := by
  have h0 : (kf0Adj d m ^ (2 * n)) x y = 0 := by
    by_contra hne
    have hdist := kf0Adj_pow_dist hne
    push_cast at hdist
    linarith
  have h1 : (kf0Adj d m ^ (2 * n + 1)) x y = 0 := by
    by_contra hne
    have hfar' : ((2 * n + 1 : ℕ) : ℝ) < torusDist d m x y := by
      convert hfar using 1; push_cast; ring
    exact (not_lt_of_ge (kf0Adj_pow_dist hne)) hfar'
  rw [kf0CovAtom_expand]
  simp [h0, h1]

theorem kf0CovAtom_hasSum {d m : ℕ} [NeZero m] {ν : ℝ} (hν : 0 < ν)
    (x y : Torus d m) :
    HasSum (fun n : ℕ =>
      (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) x y)
      ((latticeLaplacian d m ν)⁻¹ x y) := by
  let a : ℝ := 2 * d + ν
  let f : ℕ → ℝ := fun k => (a ^ (k + 1))⁻¹ * (kf0Adj d m ^ k) x y
  have hf : HasSum f ((latticeLaplacian d m ν)⁻¹ x y) := by
    simpa only [f, a, add_zero, zero_smul, add_zero] using
      kf0_neumann_hasSum (d := d) (m := m) hν (t := 0) le_rfl x y
  have he : HasSum (fun n => f (2 * n)) (∑' n, f (2 * n)) := by
    have hi : Function.Injective (fun n : ℕ => 2 * n) := by
      intro n n' h
      dsimp at h
      omega
    exact (hf.summable.comp_injective hi).hasSum
  have ho : HasSum (fun n => f (2 * n + 1)) (∑' n, f (2 * n + 1)) := by
    have hi : Function.Injective (fun n : ℕ => 2 * n + 1) := by
      intro n n' h
      dsimp at h
      omega
    exact (hf.summable.comp_injective hi).hasSum
  have hp := he.add ho
  have heq : (∑' n, f (2 * n)) + (∑' n, f (2 * n + 1)) =
      (latticeLaplacian d m ν)⁻¹ x y :=
    (HasSum.even_add_odd he ho).unique hf
  rw [heq] at hp
  convert hp using 1
  funext n
  rw [kf0CovAtom_expand]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  change (a ^ (2 * n + 2))⁻¹ * a * (kf0Adj d m ^ (2 * n)) x y +
      (a ^ (2 * n + 2))⁻¹ * (kf0Adj d m ^ (2 * n + 1)) x y =
      f (2 * n) + f (2 * n + 1)
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hc : (a ^ (2 * n + 2))⁻¹ * a = (a ^ (2 * n + 1))⁻¹ := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, pow_succ]
    field_simp
  simp only [f, hc]

/-- A single finite-range covariance atom has exactly the same entry on two tori
when its underlying walks cannot wind and the centered displacements agree.
This is coefficient agreement, not agreement of an integrated nonlinear activity. -/
theorem kf0CovAtom_torus_eq {d m m' : ℕ} [NeZero m] [NeZero m']
    (ν : ℝ) (n : ℕ) (hm : 2 * (2 * n + 1) < m)
    (hm' : 2 * (2 * n + 1) < m')
    {x y : Torus d m} {x' y' : Torus d m'}
    (hdisp : torusDisp x y = torusDisp x' y') :
    (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) x y =
      (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m' ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m') (Torus d m') ℝ) + kf0Adj d m') *
          (kf0Adj d m' ^ n))) x' y' := by
  rw [kf0CovAtom_expand, kf0CovAtom_expand]
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [kf0Adj_pow_torus_eq (n := 2 * n) (by omega) (by omega) hdisp]
  rw [kf0Adj_pow_torus_eq (n := 2 * n + 1) hm hm' hdisp]

end Balaban.Green
