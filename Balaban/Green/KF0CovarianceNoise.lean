/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.Green.KF0CovarianceAtoms
import Balaban.Localization.CubeRegimes

/-!
# Local Gram factorization of the bare covariance atoms

Round 3, equation (B.24) of `KF0B.md`: the atom `Γₙ` is the covariance of
independent site noises of variance `ν` and oriented-edge noises of variance one,
transported by `a⁻ⁿ⁻¹ Aⁿ`. The matrix identities here establish the exact finite
covariance factorization. They do not construct the full countable Gaussian product
or localize the nonlinear hard-spin density.
-/

@[expose] public section

open scoped Classical
open Finset Matrix

namespace Balaban.Green

/-- Each torus shift is an orthogonal permutation of lattice sites. -/
theorem kf0Shift_mul_transpose {d m : ℕ} [NeZero m] (μ : Fin d) :
    (shiftMatrix (ℓ := m) μ) * (shiftMatrix (ℓ := m) μ)ᵀ =
      (1 : Matrix (Torus d m) (Torus d m) ℝ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.transpose_apply, shiftMatrix, Matrix.one_apply]
  by_cases h : x = y
  · subst y
    simp
  · simp [h, eq_comm]

/-- The positive local-noise covariance `ν I + ∑(I+Sμ)(I+Sμ)ᵀ` is `a I + A`.
The shift terms count oriented edges with the same multiplicities as `kf0Adj`. -/
theorem kf0Adj_noise_factor {d m : ℕ} [NeZero m] (ν : ℝ) :
    (2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m =
      ν • (1 : Matrix (Torus d m) (Torus d m) ℝ) +
        ∑ μ : Fin d, ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ) *
          ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)ᵀ := by
  have hμ (μ : Fin d) :
      ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ) *
        ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)ᵀ =
      (2 : ℝ) • (1 : Matrix (Torus d m) (Torus d m) ℝ) +
        (shiftMatrix μ + (shiftMatrix μ)ᵀ) := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      kf0Shift_mul_transpose]
    simp only [Matrix.one_mul, two_smul]
    abel
  simp_rw [hμ]
  rw [Finset.sum_add_distrib]
  have hs : (∑ _μ : Fin d, (2 : ℝ) •
      (1 : Matrix (Torus d m) (Torus d m) ℝ)) =
      (2 * d : ℝ) • (1 : Matrix (Torus d m) (Torus d m) ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    ring
  rw [hs, add_smul]
  unfold kf0Adj
  abel

/-- Every covariance atom is a sum of finite-range Gram matrices for independent
site and oriented-edge noises. This is the covariance identity behind (B.24). -/
theorem kf0CovAtom_noise_covariance {d m : ℕ} [NeZero m] (ν : ℝ) (n : ℕ) :
    (((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        ((kf0Adj d m ^ n) *
          ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ) + kf0Adj d m) *
          (kf0Adj d m ^ n))) =
      ((2 * d + ν) ^ (2 * n + 2))⁻¹ •
        (ν • ((kf0Adj d m ^ n) * (kf0Adj d m ^ n)ᵀ) +
          ∑ μ : Fin d,
            ((kf0Adj d m ^ n) *
              ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)) *
            (((kf0Adj d m ^ n) *
              ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)))ᵀ) := by
  have hgram (μ : Fin d) :
      (kf0Adj d m ^ n) *
        (((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ) *
          ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)ᵀ) *
          (kf0Adj d m ^ n) =
      ((kf0Adj d m ^ n) *
        ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)) *
        (((kf0Adj d m ^ n) *
          ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)))ᵀ := by
    rw [Matrix.transpose_mul, kf0Adj_pow_transpose]
    simp only [Matrix.mul_assoc]
  rw [kf0Adj_noise_factor]
  congr 1
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  simp only [kf0Adj_pow_transpose]
  congr 1
  apply Finset.sum_congr rfl
  intro μ _
  exact hgram μ

/-- An oriented-edge noise at `y` reaches `x` through `n` adjacency steps exactly when
one of the two edge endpoints has an `n`-step walk to `x`. -/
theorem kf0Adj_pow_shift_apply {d m : ℕ} [NeZero m]
    (n : ℕ) (μ : Fin d) (x y : Torus d m) :
    (((kf0Adj d m ^ n) * shiftMatrix μ) :
      Matrix (Torus d m) (Torus d m) ℝ) x y =
      (kf0Adj d m ^ n) x (y - Pi.single μ 1) := by
  rw [Matrix.mul_apply]
  have he (z : Torus d m) : y = z + Pi.single μ 1 ↔ z = y - Pi.single μ 1 := by
    constructor
    · intro h; rw [h]; abel
    · intro h; rw [h]; abel
  simp [shiftMatrix, he, mul_ite]

/-- The local edge loading is the sum of the two endpoint walk coefficients. -/
theorem kf0Adj_pow_noise_edge_apply {d m : ℕ} [NeZero m]
    (n : ℕ) (μ : Fin d) (x y : Torus d m) :
    (((kf0Adj d m ^ n) *
      ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)) :
        Matrix (Torus d m) (Torus d m) ℝ) x y =
      (kf0Adj d m ^ n) x y + (kf0Adj d m ^ n) x (y - Pi.single μ 1) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, kf0Adj_pow_shift_apply]

/-- The edge noise at `y` can influence `x` only within `n + 1` unit steps. -/
theorem kf0Adj_pow_noise_edge_range {d m : ℕ} [NeZero m]
    (n : ℕ) (μ : Fin d) (x y : Torus d m)
    (hfar : (n + 1 : ℝ) < torusDist d m x y) :
    (((kf0Adj d m ^ n) *
      ((1 : Matrix (Torus d m) (Torus d m) ℝ) + shiftMatrix μ)) :
        Matrix (Torus d m) (Torus d m) ℝ) x y = 0 := by
  rw [kf0Adj_pow_noise_edge_apply]
  have h0 : (kf0Adj d m ^ n) x y = 0 := by
    by_contra hne
    have hd := kf0Adj_pow_dist hne
    linarith
  have hstep : torusDist d m (y - Pi.single μ 1) y ≤ 1 := by
    have h := Balaban.Reflection.torusDist_sub_single_le y y μ
    simpa [show torusDist d m y y = 0 from
      dist_self (show L1Torus d m from y)] using h
  have h1 : (kf0Adj d m ^ n) x (y - Pi.single μ 1) = 0 := by
    by_contra hne
    have hd := kf0Adj_pow_dist hne
    have htri : torusDist d m x y ≤
        torusDist d m x (y - Pi.single μ 1) +
          torusDist d m (y - Pi.single μ 1) y :=
      dist_triangle (show L1Torus d m from x) (y - Pi.single μ 1) y
    linarith
  simp [h0, h1]

end Balaban.Green
