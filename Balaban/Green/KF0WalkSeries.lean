/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Lattice.Laplacian
public import Balaban.Localization.DecoupledIntegral
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# `KF0WalkSeries`: the walk series of the reference covariance (Lemma H.1, first part)

Reference covariance on the **full torus** `Λ = (ℤ/m)^d` only: the conditional problem with holes,
the expansion and Root-F are not treated here.

Write `K = -Δ + ν = (2d + ν)·1 - A`, where `A = kf0Adj d m` is the adjacency matrix of the torus
(`(2d)` neighbours counted with multiplicity, as in `latticeLaplacian`).  Then

* (T1) for `t ≥ 0`, `(K + t)⁻¹ = ∑_n (2d+ν+t)^{-(n+1)} A^n` entrywise (Neumann series);
* (T2) the weights `w_n = π⁻¹ ∫₀^∞ t^{-1/2} (2d+ν+t)^{-(n+1)} dt` are positive,
  `w_n ≤ (2d+ν)^{-n} (2d+ν)^{-1/2}`, and `∑_n w_n (2d)^n = ν^{-1/2}`; more generally for
  coefficients `0 ≤ c_n ≤ (2d)^n` one may sum under the Stieltjes integral.

The series for `C = K^{-1/2}`, the truncations and Lemma H.1 are in
`Balaban.Green.KF0WalkTruncation`.
-/

@[expose] public section

namespace Balaban.Green

open Matrix MeasureTheory Set

variable {d m : ℕ} [NeZero m]

/-- The adjacency matrix of the torus: `∑_μ (S_μ + S_μᵀ)` (each site has `2d` neighbours, counted
with multiplicity). -/
noncomputable def kf0Adj (d m : ℕ) [NeZero m] : Matrix (Torus d m) (Torus d m) ℝ :=
  ∑ μ : Fin d, (shiftMatrix μ + (shiftMatrix μ)ᵀ)

/-- `A = (2d + ν) - (-Δ + ν)`, for every `ν`. -/
theorem kf0Adj_eq (ν : ℝ) :
    kf0Adj d m = ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ)) -
      latticeLaplacian d m ν := by
  unfold kf0Adj latticeLaplacian
  abel

theorem kf0Adj_apply (x y : Torus d m) :
    kf0Adj d m x y = ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then 1 else 0)) := by
  simp [kf0Adj, Matrix.sum_apply, shiftMatrix]

theorem kf0Adj_nonneg (x y : Torus d m) : 0 ≤ kf0Adj d m x y := by
  rw [kf0Adj_apply]
  exact Finset.sum_nonneg fun μ _ => add_nonneg (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num)

theorem kf0Adj_transpose : (kf0Adj d m)ᵀ = kf0Adj d m := by
  unfold kf0Adj
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl fun μ _ => by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem kf0Adj_symm (x y : Torus d m) : kf0Adj d m x y = kf0Adj d m y x := by
  have := congrFun (congrFun (kf0Adj_transpose (d := d) (m := m)) x) y
  simpa using this.symm

/-- Row sums of `A` are `2d`. -/
theorem kf0Adj_rowSum (x : Torus d m) : ∑ y, kf0Adj d m x y = 2 * d := by
  simp_rw [kf0Adj_apply]
  rw [Finset.sum_comm]
  have h1 : ∀ μ : Fin d, ∑ y : Torus d m, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then 1 else 0)) = 2 := by
    intro μ
    rw [Finset.sum_add_distrib]
    have e2 : ∀ y : Torus d m, (x = y + Pi.single μ 1) ↔ (y = x - Pi.single μ 1) := fun y => by
      rw [eq_sub_iff_add_eq, eq_comm]
    simp only [e2, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    norm_num
  rw [Finset.sum_congr rfl fun μ _ => h1 μ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem kf0Adj_pow_nonneg (n : ℕ) (x y : Torus d m) : 0 ≤ (kf0Adj d m ^ n) x y := by
  induction n generalizing x y with
  | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (kf0Adj_nonneg z y)

theorem kf0Adj_pow_rowSum (n : ℕ) (x : Torus d m) :
    ∑ y, (kf0Adj d m ^ n) x y = (2 * d : ℝ) ^ n := by
  induction n generalizing x with
  | zero => simp [Matrix.one_apply]
  | succ n ih =>
    simp_rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, kf0Adj_rowSum, ← Finset.sum_mul, ih]

theorem kf0Adj_pow_le (n : ℕ) (x y : Torus d m) : (kf0Adj d m ^ n) x y ≤ (2 * d : ℝ) ^ n := by
  rw [← kf0Adj_pow_rowSum n x]
  exact Finset.single_le_sum (f := fun y => (kf0Adj d m ^ n) x y)
    (fun z _ => kf0Adj_pow_nonneg n x z) (Finset.mem_univ y)

theorem kf0Adj_pow_transpose (n : ℕ) : ((kf0Adj d m) ^ n)ᵀ = kf0Adj d m ^ n := by
  rw [Matrix.transpose_pow, kf0Adj_transpose]

theorem kf0Adj_pow_symm (n : ℕ) (x y : Torus d m) :
    (kf0Adj d m ^ n) x y = (kf0Adj d m ^ n) y x := by
  have := congrFun (congrFun (kf0Adj_pow_transpose (d := d) (m := m) n) x) y
  simpa using this.symm

/-! ### T1: the Neumann series -/

/-- Neumann series for the resolvent, entrywise. -/
theorem kf0_neumann_hasSum {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (x y : Torus d m) :
    HasSum (fun n : ℕ => ((2 * d + ν + t) ^ (n + 1))⁻¹ * (kf0Adj d m ^ n) x y)
      ((latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ))⁻¹ x y) := by
  set b : ℝ := 2 * d + ν + t with hb
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hbpos : 0 < b := by rw [hb]; linarith
  have hr : 2 * (d : ℝ) / b < 1 := by rw [div_lt_one hbpos, hb]; linarith
  set A := kf0Adj d m with hA
  let c : ℕ → ℝ := fun n => ((b ^ (n + 1))⁻¹)
  have hc0 : ∀ n, 0 ≤ c n := fun n => by positivity
  have hcb : ∀ n, b * c (n + 1) = c n := fun n => by
    simp only [c, pow_succ]; field_simp
  have hsum : ∀ x y : Torus d m, Summable (fun n : ℕ => c n * (A ^ n) x y) := by
    intro x y
    have hg : Summable (fun n : ℕ => b⁻¹ * (2 * (d : ℝ) / b) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) hr).mul_left _
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (kf0Adj_pow_nonneg n x y))
      (fun n => ?_) hg
    have h1 := kf0Adj_pow_le (d := d) (m := m) n x y
    calc c n * (A ^ n) x y ≤ c n * (2 * d) ^ n := mul_le_mul_of_nonneg_left h1 (hc0 n)
      _ = b⁻¹ * (2 * (d : ℝ) / b) ^ n := by
        simp only [c, pow_succ, div_pow]; field_simp
  set S : Matrix (Torus d m) (Torus d m) ℝ := fun x y => ∑' n, c n * (A ^ n) x y with hS
  have hSx : ∀ x y, HasSum (fun n : ℕ => c n * (A ^ n) x y) (S x y) := fun x y =>
    (hsum x y).hasSum
  have hmain : (b • (1 : Matrix (Torus d m) (Torus d m) ℝ) - A) * S = 1 := by
    ext x y
    rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply,
      Matrix.mul_apply, smul_eq_mul]
    -- Σ_z A x z S z y
    have h2 : HasSum (fun n : ℕ => c n * (A ^ (n + 1)) x y) (∑ z, A x z * S z y) := by
      have := hasSum_sum (s := Finset.univ) (fun z _ => (hSx z y).mul_left (A x z))
      convert this using 1
      ext n
      rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    have h1 : HasSum (fun n : ℕ => b * (c n * (A ^ n) x y)) (b * S x y) := (hSx x y).mul_left b
    rw [← hasSum_nat_add_iff' 1] at h1
    have h3 : (fun n : ℕ => b * (c (n + 1) * (A ^ (n + 1)) x y)) =
        fun n : ℕ => c n * (A ^ (n + 1)) x y := by
      ext n; rw [← hcb n]; ring
    simp only [h3] at h1
    have := h1.unique h2
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, c] at this
    have hb0 : b * (b ^ (0 + 1))⁻¹ = 1 := by simp; field_simp
    have e : b * ((b ^ (0 + 1))⁻¹ * (1 : Matrix (Torus d m) (Torus d m) ℝ) x y) =
        (1 : Matrix (Torus d m) (Torus d m) ℝ) x y := by rw [← mul_assoc, hb0, one_mul]
    linear_combination this + e
  have hK : latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ) =
      b • (1 : Matrix (Torus d m) (Torus d m) ℝ) - A := by
    have e := kf0Adj_eq (d := d) (m := m) ν
    rw [← hA] at e
    have eK : latticeLaplacian d m ν = ((2 * d + ν) • (1 : Matrix (Torus d m) (Torus d m) ℝ)) - A := by
      rw [e]; abel
    rw [eK, hb]
    simp only [add_smul]
    abel
  rw [hK]
  have hinv : (b • (1 : Matrix (Torus d m) (Torus d m) ℝ) - A)⁻¹ = S :=
    Matrix.inv_eq_right_inv hmain
  rw [hinv]
  exact hSx x y

/-- The resolvent `K + t` is invertible for `ν > 0`, `t ≥ 0`, with the Neumann series as inverse. -/
theorem kf0_isUnit_resolvent {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    IsUnit (latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ)) := by
  have e : latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ) =
      latticeLaplacian d m (ν + t) := by
    unfold latticeLaplacian
    simp only [add_smul]
    abel
  have hpd : (latticeLaplacian d m ν + t • (1 : Matrix (Torus d m) (Torus d m) ℝ)).PosDef := by
    rw [e]; exact latticeLaplacian_posDef (by linarith)
  exact (Matrix.isUnit_iff_isUnit_det _).2 hpd.det_pos.ne'.isUnit

/-! ### T2: the weights -/

/-- The walk weights `w_n = π⁻¹ ∫₀^∞ t^{-1/2} (2d+ν+t)^{-(n+1)} dt`. -/
noncomputable def walkWeight (d : ℕ) (ν : ℝ) (n : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹

theorem inv_pow_succ_le {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (n : ℕ) :
    ((a + t) ^ (n + 1))⁻¹ ≤ (a ^ n)⁻¹ * (a + t)⁻¹ := by
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le (by linarith) n) (by positivity)

theorem integrableOn_walk {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ((a + t) ^ (n + 1))⁻¹) (Ioi 0) := by
  refine Integrable.mono'
    ((Localization.integrableOn_rpow_inv_add ha).const_mul ((a ^ n)⁻¹)) ?_ ?_
  · exact ((measurable_id.pow_const _).mul
      (((measurable_const.add measurable_id).pow_const _).inv)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ (-(1 / 2 : ℝ)) * ((a + t) ^ (n + 1))⁻¹
        ≤ t ^ (-(1 / 2 : ℝ)) * ((a ^ n)⁻¹ * (a + t)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_pow_succ_le ha ht0 n) h0
      _ = _ := by ring

theorem walkWeight_pos {ν : ℝ} (hν : 0 < ν) (n : ℕ) : 0 < walkWeight d ν n := by
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  unfold walkWeight
  refine mul_pos (by positivity) ?_
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have : 0 < ((2 * d + ν + t) ^ (n + 1))⁻¹ := by positivity
    positivity
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_walk ha n)]
  have hsub : Ioi (0 : ℝ) ⊆ Function.support
      (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹) ∩ Ioi 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    refine ⟨?_, ht⟩
    have : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    have : 0 < ((2 * d + ν + t) ^ (n + 1))⁻¹ := by positivity
    exact (mul_pos ‹0 < t ^ (-(1 / 2 : ℝ))› this).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  simp

theorem walkWeight_le {ν : ℝ} (hν : 0 < ν) (n : ℕ) :
    walkWeight d ν n ≤ ((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹ := by
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  unfold walkWeight
  have hle : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹ ≤
      ∫ t in Ioi (0 : ℝ), (((2 * d + ν) ^ n)⁻¹ * (t ^ (-(1 / 2 : ℝ)) * (2 * d + ν + t)⁻¹)) := by
    refine setIntegral_mono_on (integrableOn_walk ha n)
      ((Localization.integrableOn_rpow_inv_add ha).const_mul _) measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0 _
    calc t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹
        ≤ t ^ (-(1 / 2 : ℝ)) * (((2 * d + ν) ^ n)⁻¹ * (2 * d + ν + t)⁻¹) :=
          mul_le_mul_of_nonneg_left (inv_pow_succ_le ha ht0 n) h0
      _ = _ := by ring
  rw [integral_const_mul, Localization.integral_rpow_inv_add ha] at hle
  have hpi := Real.pi_pos
  calc (1 / Real.pi) * _ ≤ (1 / Real.pi) * (((2 * d + ν) ^ n)⁻¹ * (Real.pi / Real.sqrt (2 * d + ν))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp

theorem walkWeight_zero {ν : ℝ} (hν : 0 < ν) :
    walkWeight d ν 0 = (Real.sqrt (2 * d + ν))⁻¹ := by
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  unfold walkWeight
  simp only [zero_add, pow_one]
  rw [Localization.integral_rpow_inv_add ha]
  have hpi := Real.pi_pos
  field_simp

/-- `∫₀^∞ t^{-1/2} (a+t)^{-(n+1)} dt = π w_n`. -/
theorem integral_walk_eq {ν : ℝ} (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) * ((2 * d + ν + t) ^ (n + 1))⁻¹ =
      Real.pi * walkWeight d ν n := by
  unfold walkWeight
  have hpi := Real.pi_pos
  field_simp

/-- Summation under the Stieltjes integral: for `0 ≤ c_n ≤ (2d)^n`,
`∑ c_n w_n = π⁻¹ ∫₀^∞ t^{-1/2} ∑ c_n (2d+ν+t)^{-(n+1)} dt`. -/
theorem hasSum_coeff_walkWeight {ν : ℝ} (hν : 0 < ν) (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n)
    (hc : ∀ n, c n ≤ (2 * d : ℝ) ^ n) :
    HasSum (fun n => c n * walkWeight d ν n)
      ((1 / Real.pi) * ∫ t in Ioi (0 : ℝ),
        t ^ (-(1 / 2 : ℝ)) * ∑' n, c n * ((2 * d + ν + t) ^ (n + 1))⁻¹) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (0 : ℝ) < 2 * d + ν := by positivity
  have hpi := Real.pi_pos
  let F : ℕ → ℝ → ℝ := fun n t => t ^ (-(1 / 2 : ℝ)) * (c n * ((2 * d + ν + t) ^ (n + 1))⁻¹)
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := fun n =>
    IntegrableOn.congr_fun ((integrableOn_walk ha n).const_mul (c n))
      (fun t _ => by simp only [F]; ring) measurableSet_Ioi
  have hFnorm : ∀ n, ∫ t, ‖F n t‖ ∂(volume.restrict (Ioi (0 : ℝ))) =
      c n * (Real.pi * walkWeight d ν n) := by
    intro n
    rw [← integral_walk_eq, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    have h0 : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht0 _
    simp only [F]
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hc0 n; positivity)]
    ring
  have hq : 2 * (d : ℝ) / (2 * d + ν) < 1 := by rw [div_lt_one ha]; linarith
  have hsum : Summable (fun n => ∫ t, ‖F n t‖ ∂(volume.restrict (Ioi (0 : ℝ)))) := by
    simp_rw [hFnorm]
    have hg : Summable (fun n : ℕ => Real.pi * (Real.sqrt (2 * d + ν))⁻¹ *
        (2 * (d : ℝ) / (2 * d + ν)) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) hq).mul_left _
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n)
      (mul_nonneg hpi.le (walkWeight_pos hν n).le)) (fun n => ?_) hg
    calc c n * (Real.pi * walkWeight d ν n)
        ≤ (2 * d : ℝ) ^ n * (Real.pi * (((2 * d + ν) ^ n)⁻¹ * (Real.sqrt (2 * d + ν))⁻¹)) :=
          mul_le_mul (hc n) (mul_le_mul_of_nonneg_left (walkWeight_le hν n) hpi.le)
            (mul_nonneg hpi.le (walkWeight_pos hν n).le) (by positivity)
      _ = _ := by rw [div_pow]; field_simp
  have h := (hasSum_integral_of_summable_integral_norm hFint hsum).mul_left (1 / Real.pi)
  have e1 : (fun n => (1 / Real.pi) * ∫ t, F n t ∂(volume.restrict (Ioi (0 : ℝ)))) =
      fun n => c n * walkWeight d ν n := by
    ext n
    have : ∫ t, F n t ∂(volume.restrict (Ioi (0 : ℝ))) =
        c n * (Real.pi * walkWeight d ν n) := by
      rw [← integral_walk_eq, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [F]; ring
    rw [this]; field_simp
  rw [e1] at h
  have e2 : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      ∑' n, c n * ((2 * d + ν + t) ^ (n + 1))⁻¹ =
      ∫ t, ∑' n, F n t ∂(volume.restrict (Ioi (0 : ℝ))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun t => by
      simp only [F]; rw [tsum_mul_left])
  rw [e2]; exact h

theorem hasSum_geom_walk {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n : ℕ => (2 * d : ℝ) ^ n * ((2 * d + ν + t) ^ (n + 1))⁻¹) ((ν + t)⁻¹) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : (0 : ℝ) < 2 * d + ν + t := by positivity
  have hr : 2 * (d : ℝ) / (2 * d + ν + t) < 1 := by rw [div_lt_one hb]; linarith
  have := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((2 * d + ν + t)⁻¹)
  convert this using 1
  · ext n; rw [div_pow, pow_succ]; field_simp
  · have : (1 - 2 * (d : ℝ) / (2 * d + ν + t)) = (ν + t) / (2 * d + ν + t) := by
      field_simp; ring
    rw [this]; field_simp

/-- The row-sum identity: `∑_n w_n (2d)^n = ν^{-1/2}`. -/
theorem hasSum_walkWeight_row {ν : ℝ} (hν : 0 < ν) :
    HasSum (fun n : ℕ => (2 * d : ℝ) ^ n * walkWeight d ν n) ((Real.sqrt ν)⁻¹) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := hasSum_coeff_walkWeight (d := d) hν (fun n => (2 * d : ℝ) ^ n)
    (fun n => by positivity) (fun n => le_rfl)
  convert h using 1
  have hpi := Real.pi_pos
  have : ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2 : ℝ)) *
      ∑' n : ℕ, (2 * d : ℝ) ^ n * ((2 * d + ν + t) ^ (n + 1))⁻¹ = Real.pi / Real.sqrt ν := by
    rw [← Localization.integral_rpow_inv_add hν]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [(hasSum_geom_walk hν ht0).tsum_eq]
  rw [this]; field_simp

end Balaban.Green
