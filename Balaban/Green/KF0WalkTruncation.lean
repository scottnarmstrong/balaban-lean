/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0WalkSeries
public import Balaban.Green.KF0Reference
public import Balaban.Localization.DecoupledCovPrincipal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# `KF0WalkTruncation`: the walk series of `K^{-1/2}` and its truncations (Lemma H.1)

This is the reference covariance on the **full torus** `Λ = (ℤ/m)^d`; the conditional problem with
holes, the expansion and Root-F are not treated here.

With `A = kf0Adj d m` and the weights `w_n = walkWeight d ν n` of `KF0WalkSeries`:

* `kf0C = ∑_n w_n A^n` (entrywise) is entrywise non-negative, symmetric, has row sums `ν^{-1/2}`,
  satisfies `kf0C * kf0C = (-Δ+ν)⁻¹`, and its complexification is the landed
  `sqrtMat (kf0Op d m ν)` (`kf0C_map_eq_sqrtMat`);
* `kf0CR R = ∑_{n ≤ R} w_n A^n` has range `≤ R`, is dominated by `kf0C`, its increments have row
  sums `w_R (2d)^R ≤ ν^{-1/2} q^R`, `q = 2d/(2d+ν)`, and it satisfies the two-sided form bound
  `(1-q)(2d+ν)^{-1/2} |u|² ≤ ⟨u, C_R u⟩ ≤ ν^{-1/2} |u|²` (Lemma H.1, `kf0_lemmaH1`).
-/

@[expose] public section

namespace Balaban.Green

open Matrix MeasureTheory Set Filter Topology

variable {d m : ℕ} [NeZero m]

/-- The series `C = ∑_n w_n A^n`, entrywise. -/
noncomputable def kf0C (d m : ℕ) [NeZero m] (ν : ℝ) : Matrix (Torus d m) (Torus d m) ℝ :=
  fun x y => ∑' n : ℕ, walkWeight d ν n * (kf0Adj d m ^ n) x y

/-- The walk truncation `C_R = ∑_{n ≤ R} w_n A^n`. -/
noncomputable def kf0CR (d m : ℕ) [NeZero m] (ν : ℝ) (R : ℕ) :
    Matrix (Torus d m) (Torus d m) ℝ :=
  ∑ n ∈ Finset.range (R + 1), walkWeight d ν n • kf0Adj d m ^ n

theorem kf0CR_apply (ν : ℝ) (R : ℕ) (x y : Torus d m) :
    kf0CR d m ν R x y = ∑ n ∈ Finset.range (R + 1), walkWeight d ν n * (kf0Adj d m ^ n) x y := by
  simp [kf0CR, Matrix.sum_apply, Matrix.smul_apply]

/-! ### T3: the series -/

theorem kf0C_hasSum {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    HasSum (fun n : ℕ => walkWeight d ν n * (kf0Adj d m ^ n) x y) (kf0C d m ν x y) := by
  have h := hasSum_coeff_walkWeight (d := d) hν (fun n => (kf0Adj d m ^ n) x y)
    (fun n => kf0Adj_pow_nonneg n x y) (fun n => kf0Adj_pow_le n x y)
  have hs : Summable (fun n : ℕ => walkWeight d ν n * (kf0Adj d m ^ n) x y) :=
    h.summable.congr (fun n => mul_comm _ _)
  exact hs.hasSum

theorem kf0C_nonneg {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) : 0 ≤ kf0C d m ν x y :=
  (kf0C_hasSum hν x y).nonneg fun n =>
    mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n x y)

theorem kf0C_symm (ν : ℝ) (x y : Torus d m) : kf0C d m ν x y = kf0C d m ν y x := by
  unfold kf0C
  exact tsum_congr fun n => by rw [kf0Adj_pow_symm]

/-- Row sums: `∑_y C(x,y) = ν^{-1/2}`. -/
theorem kf0C_rowSum {ν : ℝ} (hν : 0 < ν) (x : Torus d m) :
    ∑ y, kf0C d m ν x y = (Real.sqrt ν)⁻¹ := by
  have h1 := hasSum_sum (s := (Finset.univ : Finset (Torus d m)))
    (fun y _ => kf0C_hasSum hν x y)
  have h2 : (fun n : ℕ => ∑ y, walkWeight d ν n * (kf0Adj d m ^ n) x y) =
      fun n : ℕ => (2 * d : ℝ) ^ n * walkWeight d ν n := by
    ext n
    rw [← Finset.mul_sum, kf0Adj_pow_rowSum]; ring
  rw [h2] at h1
  exact h1.unique (hasSum_walkWeight_row hν)

theorem kf0C_eq_integral {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    kf0C d m ν x y = (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      (latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ))⁻¹ x y := by
  have h := hasSum_coeff_walkWeight (d := d) hν (fun n => (kf0Adj d m ^ n) x y)
    (fun n => kf0Adj_pow_nonneg n x y) (fun n => kf0Adj_pow_le n x y)
  have h' : HasSum (fun n : ℕ => walkWeight d ν n * (kf0Adj d m ^ n) x y)
      ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
        t ^ (-(1 / 2 : ℝ)) * ∑' n, (kf0Adj d m ^ n) x y * ((2 * d + ν + t) ^ (n + 1))⁻¹) := by
    simpa only [mul_comm] using h
  rw [(kf0C_hasSum hν x y).unique h']
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  congr 1
  rw [← (kf0_neumann_hasSum hν ht0 x y).tsum_eq]
  exact tsum_congr fun n => mul_comm _ _

/-! #### Identification with the landed `sqrtMat` -/

private instance : Nonempty (L1Torus d m) := ⟨(0 : Torus d m)⟩

/-- `-Δ + ν`, typed over the `ℓ¹` torus (as `kf0Op`). -/
abbrev KL1 (d m : ℕ) [NeZero m] (ν : ℝ) : Matrix (L1Torus d m) (L1Torus d m) ℝ :=
  latticeLaplacian d m ν

theorem kf0_map_resolvent_add {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ) (t : ℝ) :
    (t : ℂ) • (1 : Matrix ι ι ℂ) + K.map (algebraMap ℝ ℂ) =
      (K + t • (1 : Matrix ι ι ℝ)).map (algebraMap ℝ ℂ) := by
  ext i j
  by_cases h : i = j <;> simp [h, add_comm]

theorem kf0_map_inv_real {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (hM : IsUnit M) :
    (M.map (algebraMap ℝ ℂ))⁻¹ = (M⁻¹).map (algebraMap ℝ ℂ) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hM)]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem kf0_map_sq_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (C Ki : Matrix ι ι ℝ) (S : Matrix ι ι ℂ)
    (hS : C.map (algebraMap ℝ ℂ) = S) (h : S * S = Ki.map (algebraMap ℝ ℂ)) : C * C = Ki := by
  rw [← hS, ← Matrix.map_mul] at h
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem kf0Op_resolvent_inv {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    ((t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν)⁻¹ =
      (((KL1 d m ν) +
        t • (1 : Matrix (L1Torus d m) (L1Torus d m) ℝ))⁻¹).map (algebraMap ℝ ℂ) := by
  have e : (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν =
      ((KL1 d m ν) +
        t • (1 : Matrix (L1Torus d m) (L1Torus d m) ℝ)).map (algebraMap ℝ ℂ) :=
    kf0_map_resolvent_add (ι := L1Torus d m) (latticeLaplacian d m ν) t
  rw [e]
  exact kf0_map_inv_real (ι := L1Torus d m) _ (kf0_isUnit_resolvent (d := d) (m := m) hν ht)

theorem kf0_resOK_of_pos {ν : ℝ} (hν : 0 < ν) : Localization.ResOK (kf0Op d m ν) := by
  intro t ht
  have e : (t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν =
      ((KL1 d m ν) +
        t • (1 : Matrix (L1Torus d m) (L1Torus d m) ℝ)).map (algebraMap ℝ ℂ) :=
    kf0_map_resolvent_add (ι := L1Torus d m) (latticeLaplacian d m ν) t
  rw [e]
  exact (kf0_isUnit_resolvent (d := d) (m := m) hν ht).map (algebraMap ℝ ℂ).mapMatrix

/-- The series `kf0C` is the landed principal inverse square root `sqrtMat (kf0Op)`. -/
theorem kf0C_map_eq_sqrtMat {ν : ℝ} (hν : 0 < ν) :
    (kf0C d m ν).map (algebraMap ℝ ℂ) = Localization.sqrtMat (kf0Op d m ν) := by
  refine Matrix.ext fun (x y : L1Torus d m) => ?_
  have hint : ∀ t ∈ Ioi (0 : ℝ),
      (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • ((t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) +
        kf0Op d m ν)⁻¹) x y =
      ((t ^ (-(1 / 2 : ℝ)) * (latticeLaplacian d m ν +
        t • (1 : Matrix (Torus d m) (Torus d m) ℝ))⁻¹ x y : ℝ) : ℂ) := by
    intro t ht
    rw [kf0Op_resolvent_inv hν (le_of_lt ht)]
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    rfl
  show ((kf0C d m ν x y : ℝ) : ℂ) = ((1 / Real.pi : ℝ) : ℂ) *
    ∫ t in Ioi (0 : ℝ), (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      ((t : ℂ) • (1 : Matrix (L1Torus d m) (L1Torus d m) ℂ) + kf0Op d m ν)⁻¹) x y
  rw [setIntegral_congr_fun measurableSet_Ioi hint, integral_complex_ofReal,
    kf0C_eq_integral hν x y]
  push_cast
  rfl

theorem kf0C_mul_self {ν : ℝ} (hν : 0 < ν) :
    kf0C d m ν * kf0C d m ν = (latticeLaplacian d m ν)⁻¹ := by
  have h := Localization.sqrtMat_mul_self (kf0_resOK_of_pos (d := d) (m := m) hν)
  have hK : (kf0Op d m ν)⁻¹ = ((latticeLaplacian d m ν)⁻¹).map (algebraMap ℝ ℂ) :=
    kf0_map_inv_real (ι := L1Torus d m) (latticeLaplacian d m ν) (by
      have h0 := kf0_isUnit_resolvent (d := d) (m := m) hν (le_refl (0 : ℝ))
      rw [zero_smul, add_zero] at h0
      exact h0)
  exact kf0_map_sq_eq (ι := L1Torus d m) (kf0C d m ν) _ _ (kf0C_map_eq_sqrtMat hν) (hK ▸ h)

/-! ### T4: truncations -/

theorem kf0CR_nonneg {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x y : Torus d m) : 0 ≤ kf0CR d m ν R x y := by
  rw [kf0CR_apply]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n x y)

theorem kf0CR_le_kf0C {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x y : Torus d m) :
    kf0CR d m ν R x y ≤ kf0C d m ν x y := by
  rw [kf0CR_apply]
  exact (kf0C_hasSum hν x y).summable.sum_le_tsum _ fun n _ =>
    mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n x y)

theorem kf0CR_symm (ν : ℝ) (R : ℕ) (x y : Torus d m) : kf0CR d m ν R x y = kf0CR d m ν R y x := by
  rw [kf0CR_apply, kf0CR_apply]
  exact Finset.sum_congr rfl fun n _ => by rw [kf0Adj_pow_symm]

theorem kf0CR_zero {ν : ℝ} : kf0CR d m ν 0 = walkWeight d ν 0 • (1 : Matrix (Torus d m) (Torus d m) ℝ) := by
  simp [kf0CR]

theorem kf0Adj_ne_zero_dist {x y : Torus d m} (h : kf0Adj d m x y ≠ 0) : torusDist d m x y ≤ 1 := by
  by_cases hxy : x = y
  · subst hxy
    have : torusDist d m x x = 0 := dist_self (show L1Torus d m from x)
    linarith
  · apply torusDist_le_one_of_ne_zero (ν := 0)
    intro hK; apply h
    have e := congrFun (congrFun (kf0Adj_eq (d := d) (m := m) 0) x) y
    simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hxy, hK] using e

/-- A walk of length `n` joins points at `ℓ¹` distance `≤ n`. -/
theorem kf0Adj_pow_dist {n : ℕ} {x y : Torus d m} (h : (kf0Adj d m ^ n) x y ≠ 0) :
    torusDist d m x y ≤ n := by
  induction n generalizing y with
  | zero =>
    have hxy : x = y := by
      by_contra hne
      exact h (by simp [hne])
    subst hxy
    have : torusDist d m x x = 0 := dist_self (show L1Torus d m from x)
    simp [this]
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih (left_ne_zero_of_mul hz)
    have h2 := kf0Adj_ne_zero_dist (right_ne_zero_of_mul hz)
    have h3 : torusDist d m x y ≤ torusDist d m x z + torusDist d m z y :=
      dist_triangle (show L1Torus d m from x) (show L1Torus d m from z) (show L1Torus d m from y)
    push_cast
    linarith

/-- Range: `C_R(x,y) = 0` when the `ℓ¹` torus distance exceeds `R`. -/
theorem kf0CR_eq_zero_of_lt {ν : ℝ} {R : ℕ} {x y : Torus d m} (h : (R : ℝ) < torusDist d m x y) :
    kf0CR d m ν R x y = 0 := by
  rw [kf0CR_apply]
  refine Finset.sum_eq_zero fun n hn => ?_
  have hnR : (n : ℝ) ≤ R := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  have : (kf0Adj d m ^ n) x y = 0 := by
    by_contra hne
    have := kf0Adj_pow_dist hne
    linarith
  rw [this, mul_zero]

/-- The `n`-th term has row sum `w_n (2d)^n ≤ ν^{-1/2} q^n`, `q = 2d/(2d+ν)`. -/
theorem walkWeight_mul_le {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    walkWeight d ν n * (2 * d : ℝ) ^ n ≤ (Real.sqrt ν)⁻¹ * (2 * d / (2 * d + ν)) ^ n := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  have hsq : (Real.sqrt (2 * d + ν))⁻¹ ≤ (Real.sqrt ν)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hν) (Real.sqrt_le_sqrt (by linarith))
  calc walkWeight d ν n * (2 * d : ℝ) ^ n
      ≤ (((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹) * (2 * d : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (walkWeight_le hν n) (by positivity)
    _ = (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ n := by
        rw [div_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hsq (by positivity)

/-- Row tail of one step: `∑_y (C_{R+1} - C_R)(x,y) = w_{R+1} (2d)^{R+1} ≤ ν^{-1/2} q^{R+1}`. -/
theorem kf0CR_rowTail {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x : Torus d m) :
    ∑ y, (kf0CR d m ν (R + 1) - kf0CR d m ν R) x y =
      walkWeight d ν (R + 1) * (2 * d : ℝ) ^ (R + 1) ∧
    walkWeight d ν (R + 1) * (2 * d : ℝ) ^ (R + 1) ≤
      (Real.sqrt ν)⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) := by
  refine ⟨?_, walkWeight_mul_le hν _⟩
  have : ∀ y, (kf0CR d m ν (R + 1) - kf0CR d m ν R) x y =
      walkWeight d ν (R + 1) * (kf0Adj d m ^ (R + 1)) x y := by
    intro y
    simp only [Matrix.sub_apply, kf0CR_apply]
    rw [Finset.sum_range_succ _ (R + 1)]
    ring
  simp_rw [this]
  rw [← Finset.mul_sum, kf0Adj_pow_rowSum]

/-- Monotonicity in the mass: the constants for `ν_* ≤ ν`. -/
theorem walkWeight_mul_le_gap {ν g : ℝ} (hg : 0 < g) (hgν : g ≤ ν) (n : ℕ) :
    walkWeight d ν n * (2 * d : ℝ) ^ n ≤ (Real.sqrt g)⁻¹ * (2 * d / (2 * d + g)) ^ n := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hν : 0 < ν := lt_of_lt_of_le hg hgν
  refine (walkWeight_mul_le hν n).trans (mul_le_mul ?_ ?_ (by positivity) (by positivity))
  · exact inv_anti₀ (Real.sqrt_pos.2 hg) (Real.sqrt_le_sqrt hgν)
  · exact pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)) n

/-! #### Row sums and the upper form bound -/

theorem kf0CR_rowSum_le {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x : Torus d m) :
    ∑ y, kf0CR d m ν R x y ≤ (Real.sqrt ν)⁻¹ := by
  rw [← kf0C_rowSum hν x]
  exact Finset.sum_le_sum fun y _ => kf0CR_le_kf0C hν R x y

/-- Schur bound for a symmetric matrix with non-negative entries and row sums `≤ ρ`. -/
theorem form_abs_le {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (h0 : ∀ i j, 0 ≤ M i j)
    (hs : ∀ i j, M i j = M j i) {ρ : ℝ} (hρ : ∀ i, ∑ j, M i j ≤ ρ) (u : ι → ℝ) :
    |u ⬝ᵥ M *ᵥ u| ≤ ρ * ∑ i, u i ^ 2 := by
  have e : u ⬝ᵥ M *ᵥ u = ∑ i, ∑ j, M i j * (u i * u j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  have h1 : ∑ i, ∑ j, M i j * u i ^ 2 = ∑ i, u i ^ 2 * ∑ j, M i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ i, ∑ j, M i j * u j ^ 2 = ∑ j, u j ^ 2 * ∑ i, M j i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [hs i j]; ring
  have h3 : ∑ i, u i ^ 2 * ∑ j, M i j ≤ ρ * ∑ i, u i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (hρ i) (sq_nonneg (u i)); linarith
  calc |∑ i, ∑ j, M i j * (u i * u j)|
      ≤ ∑ i, ∑ j, M i j * ((u i ^ 2 + u j ^ 2) / 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
        rw [abs_mul, abs_of_nonneg (h0 i j)]
        refine mul_le_mul_of_nonneg_left ?_ (h0 i j)
        cases abs_cases (u i * u j) <;> nlinarith [sq_nonneg (u i - u j), sq_nonneg (u i + u j)]
    _ = (∑ i, ∑ j, M i j * u i ^ 2 + ∑ i, ∑ j, M i j * u j ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ρ * ∑ i, u i ^ 2 := by rw [h1, h2]; linarith

theorem kf0CR_form_le {ν : ℝ} (hν : 0 < ν) (R : ℕ) (u : Torus d m → ℝ) :
    u ⬝ᵥ kf0CR d m ν R *ᵥ u ≤ (Real.sqrt ν)⁻¹ * ∑ i, u i ^ 2 :=
  (le_abs_self _).trans (form_abs_le _ (kf0CR_nonneg hν R) (kf0CR_symm ν R)
    (kf0CR_rowSum_le hν R) u)

/-! #### Tails (f) -/

theorem tail_bound (e : ℕ → ℝ) {s K q : ℝ} (he : HasSum e s) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h0 : ∀ n, 0 ≤ e n) (hK : ∀ n, e n ≤ K * q ^ n) (R : ℕ) :
    0 ≤ s - ∑ n ∈ Finset.range (R + 1), e n ∧
      s - ∑ n ∈ Finset.range (R + 1), e n ≤ K * q ^ (R + 1) / (1 - q) := by
  have hs := he.summable
  have h := hs.sum_add_tsum_nat_add (R + 1)
  rw [he.tsum_eq] at h
  have htail : s - ∑ n ∈ Finset.range (R + 1), e n = ∑' n, e (n + (R + 1)) := by linarith
  rw [htail]
  have hK0 : 0 ≤ K := by
    have := hK 0; have := h0 0; simp at *; linarith
  refine ⟨tsum_nonneg fun n => h0 _, ?_⟩
  have hg : Summable (fun n : ℕ => K * q ^ (n + (R + 1))) := by
    have := (summable_geometric_of_lt_one hq0 hq1).mul_left (K * q ^ (R + 1))
    refine this.congr (fun n => ?_)
    ring
  calc ∑' n, e (n + (R + 1)) ≤ ∑' n : ℕ, K * q ^ (n + (R + 1)) :=
        (hs.comp_injective (add_left_injective (R + 1))).tsum_le_tsum (fun n => hK _) hg
    _ = K * q ^ (R + 1) / (1 - q) := by
        have : ∀ n : ℕ, K * q ^ (n + (R + 1)) = (K * q ^ (R + 1)) * q ^ n := fun n => by ring
        simp_rw [this]
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
        field_simp

/-- Entrywise tail: `0 ≤ C - C_R ≤ (2d+ν)^{-1/2} q^{R+1}/(1-q)`. -/
theorem kf0C_sub_kf0CR {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x y : Torus d m) :
    0 ≤ kf0C d m ν x y - kf0CR d m ν R x y ∧
      kf0C d m ν x y - kf0CR d m ν R x y ≤
        (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  rw [kf0CR_apply]
  refine tail_bound _ (kf0C_hasSum hν x y) (by positivity)
    (by rw [div_lt_one ha]; linarith)
    (fun n => mul_nonneg (walkWeight_pos hν n).le (kf0Adj_pow_nonneg n x y))
    (fun n => ?_) R
  calc walkWeight d ν n * (kf0Adj d m ^ n) x y ≤ walkWeight d ν n * (2 * d : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left (kf0Adj_pow_le n x y) (walkWeight_pos hν n).le
    _ ≤ (((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹) * (2 * d : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (walkWeight_le hν n) (by positivity)
    _ = _ := by rw [div_pow]; field_simp

/-- Row-sum tail: `∑_y (C - C_R)(x,y) ≤ (2d+ν)^{-1/2} q^{R+1}/(1-q)`. -/
theorem kf0C_sub_kf0CR_rowSum {ν : ℝ} (hν : 0 < ν) (R : ℕ) (x : Torus d m) :
    0 ≤ ∑ y, (kf0C d m ν x y - kf0CR d m ν R x y) ∧
      ∑ y, (kf0C d m ν x y - kf0CR d m ν R x y) ≤
        (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
          (1 - 2 * d / (2 * d + ν)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  have e : ∑ y, (kf0C d m ν x y - kf0CR d m ν R x y) =
      (Real.sqrt ν)⁻¹ - ∑ n ∈ Finset.range (R + 1), (2 * d : ℝ) ^ n * walkWeight d ν n := by
    rw [Finset.sum_sub_distrib, kf0C_rowSum hν]
    congr 1
    simp_rw [kf0CR_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.mul_sum, kf0Adj_pow_rowSum]; ring
  rw [e]
  refine tail_bound _ (hasSum_walkWeight_row hν) (by positivity)
    (by rw [div_lt_one ha]; linarith)
    (fun n => mul_nonneg (by positivity) (walkWeight_pos hν n).le) (fun n => ?_) R
  calc (2 * d : ℝ) ^ n * walkWeight d ν n
      ≤ (2 * d : ℝ) ^ n * (((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹) :=
        mul_le_mul_of_nonneg_left (walkWeight_le hν n) (by positivity)
    _ = _ := by rw [div_pow]; field_simp

theorem kf0CR_tendsto {ν : ℝ} (hν : 0 < ν) (x y : Torus d m) :
    Tendsto (fun R : ℕ => kf0CR d m ν R x y) atTop (𝓝 (kf0C d m ν x y)) := by
  have h := (kf0C_hasSum hν x y).tendsto_sum_nat
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def, kf0CR_apply] using h2

/-! ### (e) The lower form bound -/

theorem dot_mulVec_symm {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (hB : Bᵀ = B)
    (u w : ι → ℝ) : u ⬝ᵥ B *ᵥ w = (B *ᵥ u) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec]
  have : u ᵥ* B = B *ᵥ u := by
    conv_lhs => rw [← hB]
    exact Matrix.vecMul_transpose B u
  rw [this]

theorem sum_sq_eq_dot {ι : Type*} [Fintype ι] (v : ι → ℝ) : ∑ i, v i ^ 2 = v ⬝ᵥ v := by
  simp [dotProduct, sq]

theorem dot_self_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [← sum_sq_eq_dot]; exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The symmetric form of the adjacency matrix is `≥ -2d |v|²`. -/
theorem kf0Adj_form_ge (v : Torus d m → ℝ) : -(2 * d : ℝ) * (v ⬝ᵥ v) ≤ v ⬝ᵥ kf0Adj d m *ᵥ v := by
  have h := form_abs_le (kf0Adj d m) kf0Adj_nonneg kf0Adj_symm (ρ := 2 * d)
    (fun i => (kf0Adj_rowSum i).le) v
  rw [sum_sq_eq_dot] at h
  have := neg_abs_le (v ⬝ᵥ kf0Adj d m *ᵥ v)
  nlinarith

theorem kf0_partial_form_lower {b : ℝ} (hb : 2 * (d : ℝ) < b) (u : Torus d m → ℝ) (R : ℕ) :
    (1 - 2 * d / b) * (u ⬝ᵥ u) ≤
      ∑ n ∈ Finset.range (R + 1), (b ^ n)⁻¹ * (u ⬝ᵥ kf0Adj d m ^ n *ᵥ u) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb0 : 0 < b := by linarith
  have hr0 : 0 ≤ 2 * (d : ℝ) / b := by positivity
  have hr : 0 ≤ 1 - 2 * (d : ℝ) / b := by rw [sub_nonneg, div_le_one hb0]; linarith
  set A := kf0Adj d m with hA
  have hQe : ∀ k : ℕ, u ⬝ᵥ A ^ (2 * k) *ᵥ u = (A ^ k *ᵥ u) ⬝ᵥ (A ^ k *ᵥ u) := by
    intro k
    rw [two_mul, pow_add, ← Matrix.mulVec_mulVec]
    exact dot_mulVec_symm _ (kf0Adj_pow_transpose k) _ _
  have hQo : ∀ k : ℕ, u ⬝ᵥ A ^ (2 * k + 1) *ᵥ u = (A ^ k *ᵥ u) ⬝ᵥ (A *ᵥ (A ^ k *ᵥ u)) := by
    intro k
    have : A ^ (2 * k + 1) = A ^ k * (A * A ^ k) := by
      rw [two_mul, ← pow_succ', ← pow_add, ← add_assoc]
    rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact dot_mulVec_symm _ (kf0Adj_pow_transpose k) _ _
  let f : ℕ → ℝ := fun n => (b ^ n)⁻¹ * (u ⬝ᵥ A ^ n *ᵥ u)
  have hpair : ∀ k : ℕ, (b ^ (2 * k))⁻¹ * ((1 - 2 * d / b) * ((A ^ k *ᵥ u) ⬝ᵥ (A ^ k *ᵥ u))) ≤
      f (2 * k) + f (2 * k + 1) := by
    intro k
    set v := A ^ k *ᵥ u with hv
    have h1 := kf0Adj_form_ge (d := d) (m := m) v
    have e : (b ^ (2 * k + 1))⁻¹ = (b ^ (2 * k))⁻¹ * b⁻¹ := by rw [pow_succ, mul_inv]
    simp only [f, hQe, hQo, e]
    rw [← sub_nonneg]
    have : (b ^ (2 * k))⁻¹ * b⁻¹ * (v ⬝ᵥ A *ᵥ v) + (b ^ (2 * k))⁻¹ * (v ⬝ᵥ v) -
        (b ^ (2 * k))⁻¹ * ((1 - 2 * d / b) * (v ⬝ᵥ v)) =
        (b ^ (2 * k))⁻¹ * (b⁻¹ * ((v ⬝ᵥ A *ᵥ v) + 2 * d * (v ⬝ᵥ v))) := by
      field_simp; ring
    have h2 : 0 ≤ (v ⬝ᵥ A *ᵥ v) + 2 * d * (v ⬝ᵥ v) := by linarith
    have h3 : 0 ≤ (b ^ (2 * k))⁻¹ * (b⁻¹ * ((v ⬝ᵥ A *ᵥ v) + 2 * d * (v ⬝ᵥ v))) := by positivity
    linarith
  have hpair0 : ∀ k : ℕ, 0 ≤ f (2 * k) + f (2 * k + 1) := fun k =>
    le_trans (by have := dot_self_nonneg' (A ^ k *ᵥ u); positivity) (hpair k)
  have hS2 : ∀ R : ℕ, ∑ n ∈ Finset.range (R + 2 + 1), f n =
      ∑ n ∈ Finset.range (R + 1), f n + (f (R + 1) + f (R + 2)) := by
    intro R
    rw [Finset.sum_range_succ, Finset.sum_range_succ]; ring
  have hodd : ∀ k : ℕ, (1 - 2 * d / b) * (u ⬝ᵥ u) ≤ ∑ n ∈ Finset.range (2 * k + 1 + 1), f n := by
    intro k
    induction k with
    | zero =>
      have := hpair 0
      simp only [mul_zero, pow_zero, inv_one, one_mul, one_mulVec] at this
      simpa [Finset.sum_range_succ] using this
    | succ k ih =>
      have e1 : 2 * (k + 1) + 1 + 1 = (2 * k + 1) + 2 + 1 := by ring
      rw [e1, hS2]
      have := hpair0 (k + 1)
      have e2 : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [e2] at this
      have e3 : 2 * k + 2 + 1 = 2 * k + 1 + 2 := by ring
      rw [e3] at this
      have e4 : 2 * k + 1 + 1 = 2 * k + 2 := by ring
      rw [e4] at this
      linarith
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' R
  · rcases k with _ | k
    · simp only [mul_zero, zero_add, Finset.sum_range_one, pow_zero, inv_one, one_mul,
        one_mulVec]
      have := dot_self_nonneg' u
      nlinarith
    · have e : 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 := by ring
      rw [e, Finset.sum_range_succ]
      have h1 := hodd k
      have h2 : 0 ≤ f (2 * k + 1 + 1) := by
        have : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
        simp only [f]
        rw [this, hQe]
        have := dot_self_nonneg' (A ^ (k + 1) *ᵥ u)
        positivity
      linarith
  · exact hodd k

theorem kf0CR_form_eq (ν : ℝ) (R : ℕ) (u : Torus d m → ℝ) :
    u ⬝ᵥ kf0CR d m ν R *ᵥ u =
      ∑ n ∈ Finset.range (R + 1), walkWeight d ν n * (u ⬝ᵥ kf0Adj d m ^ n *ᵥ u) := by
  simp [kf0CR, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul]

/-- **Lower form bound** (Lemma H.1): `⟨u, C_R u⟩ ≥ (1-q)(2d+ν)^{-1/2} |u|²`, `q = 2d/(2d+ν)`. -/
theorem kf0CR_form_ge {ν : ℝ} (hν : 0 < ν) (R : ℕ) (u : Torus d m → ℝ) :
    (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ * (u ⬝ᵥ u) ≤
      u ⬝ᵥ kf0CR d m ν R *ᵥ u := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  have hpi := Real.pi_pos
  set Q : ℕ → ℝ := fun n => u ⬝ᵥ kf0Adj d m ^ n *ᵥ u with hQ
  rw [kf0CR_form_eq]
  have hw : ∀ n, walkWeight d ν n * (u ⬝ᵥ kf0Adj d m ^ n *ᵥ u) = (1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
      t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹ * Q n := by
    intro n
    rw [integral_mul_const]; unfold walkWeight; ring
  simp_rw [hw]
  have hint : ∀ n ∈ Finset.range (R + 1), IntegrableOn
      (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹ * Q n) (Ioi 0) :=
    fun n _ => (integrableOn_walk ha n).mul_const (Q n)
  rw [← Finset.mul_sum, ← integral_finsetSum _ hint]
  set c : ℝ := (1 - 2 * d / (2 * d + ν)) * (u ⬝ᵥ u) with hc
  have hmono : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * (2 * d + ν + t)⁻¹ * c ≤
      ∫ t in Ioi (0 : ℝ), ∑ n ∈ Finset.range (R + 1),
        t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹ * Q n := by
    refine setIntegral_mono_on ((Localization.integrableOn_rpow_inv_add ha).mul_const c)
      (integrable_finsetSum _ hint) measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0 _
    set b : ℝ := 2 * d + ν + t with hb
    have hbpos : 2 * (d : ℝ) < b := by rw [hb]; linarith
    have hb0 : 0 < b := by linarith
    have hS := kf0_partial_form_lower (d := d) (m := m) hbpos u R
    have hq : 2 * (d : ℝ) / b ≤ 2 * d / (2 * d + ν) :=
      div_le_div_of_nonneg_left (by positivity) ha (by rw [hb]; linarith)
    have hu := dot_self_nonneg' u
    have hS' : c ≤ ∑ n ∈ Finset.range (R + 1), (b ^ n)⁻¹ * Q n := by
      refine le_trans ?_ hS
      rw [hc]
      exact mul_le_mul_of_nonneg_right (by linarith) hu
    have e : ∑ n ∈ Finset.range (R + 1), t ^ (-(1 / 2 : ℝ)) * ((b) ^ (n + 1))⁻¹ * Q n =
        t ^ (-(1 / 2 : ℝ)) * b⁻¹ * ∑ n ∈ Finset.range (R + 1), (b ^ n)⁻¹ * Q n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [pow_succ, mul_inv]; ring
    rw [e]
    have : 0 ≤ t ^ (-(1 / 2 : ℝ)) * b⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left hS' this
  rw [integral_mul_const, Localization.integral_rpow_inv_add ha] at hmono
  have : (1 / Real.pi) * (Real.pi / Real.sqrt (2 * d + ν) * c) =
      (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + ν))⁻¹ * (u ⬝ᵥ u) := by
    rw [hc]; field_simp
  rw [← this]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-! ### Lemma H.1 -/

/-- **Lemma H.1** for `ν ∈ (ν_*, 1]`, `ν_* = 7/(8L²)`, with
`a_L = ν_*^{-1/2}`, `q_L = 2d/(2d+ν_*)`, `c_L = (1-q_L)/√(2d+1)`. -/
theorem kf0_lemmaH1 {L : ℕ} (hL : 0 < L) {ν : ℝ} (hmass : kf0Gap L < ν) (hν1 : ν ≤ 1) (R : ℕ) :
    (∀ x y : Torus d m, 0 ≤ kf0CR d m ν R x y ∧ kf0CR d m ν R x y ≤ kf0C d m ν x y) ∧
    (∀ x y : Torus d m, (R : ℝ) < torusDist d m x y → kf0CR d m ν R x y = 0) ∧
    (∀ x : Torus d m, ∑ y, (kf0CR d m ν (R + 1) - kf0CR d m ν R) x y ≤
      (Real.sqrt (kf0Gap L))⁻¹ * (2 * d / (2 * d + kf0Gap L)) ^ (R + 1)) ∧
    (∀ u : Torus d m → ℝ,
      (1 - 2 * d / (2 * d + kf0Gap L)) * (Real.sqrt (2 * d + 1))⁻¹ * (u ⬝ᵥ u) ≤
        u ⬝ᵥ kf0CR d m ν R *ᵥ u ∧
      u ⬝ᵥ kf0CR d m ν R *ᵥ u ≤ (Real.sqrt (kf0Gap L))⁻¹ * (u ⬝ᵥ u)) := by
  have hg := kf0Gap_pos hL
  have hν : 0 < ν := lt_trans hg hmass
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨fun x y => ⟨kf0CR_nonneg hν R x y, kf0CR_le_kf0C hν R x y⟩,
    fun x y h => kf0CR_eq_zero_of_lt h, fun x => ?_, fun u => ⟨?_, ?_⟩⟩
  · rw [(kf0CR_rowTail hν R x).1]
    exact walkWeight_mul_le_gap hg hmass.le _
  · refine le_trans ?_ (kf0CR_form_ge hν R u)
    have hq : 2 * (d : ℝ) / (2 * d + ν) ≤ 2 * d / (2 * d + kf0Gap L) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hq0 : 2 * (d : ℝ) / (2 * d + kf0Gap L) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have hs : (Real.sqrt (2 * d + 1))⁻¹ ≤ (Real.sqrt (2 * d + ν))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt (by linarith))
    have hu := dot_self_nonneg' u
    have h1 : 0 ≤ 1 - 2 * (d : ℝ) / (2 * d + kf0Gap L) := by linarith
    have h2 : 1 - 2 * (d : ℝ) / (2 * d + kf0Gap L) ≤ 1 - 2 * d / (2 * d + ν) := by linarith
    calc (1 - 2 * (d : ℝ) / (2 * d + kf0Gap L)) * (Real.sqrt (2 * d + 1))⁻¹ * (u ⬝ᵥ u)
        ≤ (1 - 2 * d / (2 * d + ν)) * (Real.sqrt (2 * d + 1))⁻¹ * (u ⬝ᵥ u) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2
            (inv_nonneg.2 (Real.sqrt_nonneg _))) hu
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs
            (by linarith)) hu
  · refine (kf0CR_form_le hν R u).trans ?_
    rw [sum_sq_eq_dot]
    exact mul_le_mul_of_nonneg_right
      (inv_anti₀ (Real.sqrt_pos.2 hg) (Real.sqrt_le_sqrt hmass.le)) (dot_self_nonneg' u)

/-! ### T6: a non-vacuity instance, `d = m = 3`, `ν = 1/8` -/

theorem kf0_instance_d3m3 :
    (∀ x : Torus 3 3, ∑ y, kf0C 3 3 (1 / 8) x y = Real.sqrt 8) ∧
    kf0CR 3 3 (1 / 8) 0 = (Real.sqrt (49 / 8))⁻¹ • (1 : Matrix (Torus 3 3) (Torus 3 3) ℝ) ∧
    (2 * ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) + 1 / 8) = 48 / 49) := by
  refine ⟨fun x => ?_, ?_, by norm_num⟩
  · rw [kf0C_rowSum (by norm_num), ← Real.sqrt_inv]
    norm_num
  · rw [kf0CR_zero, walkWeight_zero (by norm_num)]
    norm_num

end Balaban.Green
