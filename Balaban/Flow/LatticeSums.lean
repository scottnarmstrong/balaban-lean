/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.MatrixInfty
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The lattice sums `c₁(v)`, `c₂(v)` and the factor `τ` of the renormalization system

Balaban, *A low temperature expansion for classical `N`-vector models. II*, CMP 182 (1996), (5.13)
(p. 711): the second derivatives at `p = 0` of the Fourier symbols of the unit-lattice operators
`Q(-Δ+v)^{-1}Q*`, `Q(-Δ+v)^{-2}Q*` involve, in the direction `p = t e₁`, the one-component sums

`c_i(v) = ∑_{l ≠ 0} 1/(2 L^{2m}(1 − cos L^{-m} l)) · 1/[2 L^{2m}(1 − cos L^{-m} l) + v]^i`,

`l = 2π n`, `n ∈ ℤ`, `|n| ≤ (L^m − 1)/2`, and the factor `1 − L^{-2m}` that is `τ` of (5.21)
(`SMALLFIELD.md` §3.3; `Flow.matrixInfty`).  With `M = L^m`:

* `latticeSymbol M n = 2 M² (1 − cos (2π n/M))`, the eigenvalue of `-Δ` on the circle of `M` points;
* `latticeSum M v i`: the sum `c_i(v)` over `n ≠ 0`, `2|n| < M`;
* `latticeTau M = 1 − M^{-2}`.

P4 states `0 < c_i(v) < 1/20` and `0 < c₁(v) − v c₂(v) < c₁(v)`; these are proved here
(`latticeSum_pos`, `latticeSum_lt`, `latticeSum_diff`), and with them the parameter range
`InftyRange` of Lemma 3.1 (`inftyRange_latticeSums`).
-/

@[expose] public section

namespace Balaban.Flow

open Finset

/-- The symbol `2 M² (1 − cos (2π n/M))` of the lattice Laplacian on the circle of `M` points. -/
noncomputable def latticeSymbol (M : ℕ) (n : ℤ) : ℝ :=
  2 * (M : ℝ) ^ 2 * (1 - Real.cos (2 * Real.pi * n / M))

/-- The momenta `n ≠ 0`, `2|n| < M` of the circle of `M` points (P4 (5.13)). -/
def latticeIdx (M : ℕ) : Finset ℤ :=
  (Finset.Icc (-(M : ℤ)) M).filter fun n => n ≠ 0 ∧ 2 * |n| < M

/-- **The lattice sums `c_i(v)` of P4 (5.13)**: `∑_{n ≠ 0} 1/(x_n (x_n + v)^i)` with
`x_n = 2 M² (1 − cos (2π n/M))`, `M = L^m`. -/
noncomputable def latticeSum (M : ℕ) (v : ℝ) (i : ℕ) : ℝ :=
  ∑ n ∈ latticeIdx M, 1 / (latticeSymbol M n * (latticeSymbol M n + v) ^ i)

/-- **The factor `τ = 1 − L^{-2m}`** of (5.13), (5.21), `M = L^m`. -/
noncomputable def latticeTau (M : ℕ) : ℝ := 1 - ((M : ℝ) ^ 2)⁻¹

theorem latticeSymbol_ge {M : ℕ} (hM : 0 < M) {n : ℤ} (hn : 2 * |n| < M) :
    16 * (n : ℝ) ^ 2 ≤ latticeSymbol M n := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : 1 - Real.cos (2 * Real.pi * n / M) = 2 * Real.sin (Real.pi * n / M) ^ 2 := by
    have : 2 * Real.pi * n / M = 2 * (Real.pi * n / M) := by ring
    rw [this, Real.cos_two_mul, Real.cos_sq']; ring
  unfold latticeSymbol
  rw [hc]
  have hab : |(n : ℝ)| < M / 2 := by
    have : (2 : ℝ) * |(n : ℝ)| < M := by exact_mod_cast hn
    linarith
  set y : ℝ := Real.pi * |(n : ℝ)| / M with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ Real.pi / 2 := by
    rw [hy, div_le_div_iff₀ hM' (by norm_num)]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin hy0 hy1
  have hsn : Real.sin (Real.pi * n / M) ^ 2 = Real.sin y ^ 2 := by
    rcases abs_cases (n : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [hy, h1]
    · rw [hy, h1, show Real.pi * -(n : ℝ) / M = -(Real.pi * n / M) by ring, Real.sin_neg, neg_sq]
  rw [hsn]
  have h2 : 2 / Real.pi * y = 2 * |(n : ℝ)| / M := by
    rw [hy]; field_simp
  rw [h2] at hs
  have hs0 : 0 ≤ 2 * |(n : ℝ)| / M := by positivity
  have : (2 * |(n : ℝ)| / M) ^ 2 ≤ Real.sin y ^ 2 := pow_le_pow_left₀ hs0 hs 2
  calc 16 * (n : ℝ) ^ 2 = 4 * (M : ℝ) ^ 2 * (2 * |(n : ℝ)| / M) ^ 2 := by
        rw [div_pow, mul_pow, sq_abs]; field_simp; ring
    _ ≤ 4 * (M : ℝ) ^ 2 * Real.sin y ^ 2 := by gcongr
    _ = 2 * (M : ℝ) ^ 2 * (2 * Real.sin y ^ 2) := by ring

theorem latticeIdx_ne {M : ℕ} {n : ℤ} (hn : n ∈ latticeIdx M) : n ≠ 0 ∧ 2 * |n| < M := by
  simp only [latticeIdx, Finset.mem_filter] at hn
  exact hn.2

/-- The sum of `1/n²` over the momenta is at most `4`. -/
theorem sum_inv_sq_latticeIdx (M : ℕ) : ∑ n ∈ latticeIdx M, 1 / ((n : ℝ) ^ 2) ≤ 4 := by
  classical
  set A : Finset ℤ := (Finset.Ioo 0 (M + 1)).image (fun j : ℕ => (j : ℤ)) with hA
  set B : Finset ℤ := (Finset.Ioo 0 (M + 1)).image (fun j : ℕ => -(j : ℤ)) with hB
  have hsub : latticeIdx M ⊆ A ∪ B := by
    intro n hn
    obtain ⟨h0, h2⟩ := latticeIdx_ne hn
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨n.natAbs, ?_, ?_⟩)
      · simp only [Finset.mem_Ioo]
        have : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
        constructor <;> omega
      · have : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
        rw [this, abs_of_neg hneg]; ring
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨n.natAbs, ?_, ?_⟩)
      · simp only [Finset.mem_Ioo]
        have : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
        constructor <;> omega
      · have : (n.natAbs : ℤ) = |n| := Int.natCast_natAbs n
        rw [this, abs_of_pos hpos]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hnA
    obtain ⟨j', hj', hj'e⟩ := Finset.mem_image.1 hnB
    simp only [Finset.mem_Ioo] at hj hj'
    omega
  have hnn : ∀ n ∈ A ∪ B, n ∈ A ∪ B → 0 ≤ 1 / ((n : ℝ) ^ 2) := fun n _ _ => by positivity
  calc ∑ n ∈ latticeIdx M, 1 / ((n : ℝ) ^ 2)
      ≤ ∑ n ∈ A ∪ B, 1 / ((n : ℝ) ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ = ∑ n ∈ A, 1 / ((n : ℝ) ^ 2) + ∑ n ∈ B, 1 / ((n : ℝ) ^ 2) := Finset.sum_union hdisj
    _ = 2 * ∑ j ∈ Finset.Ioo 0 (M + 1), ((j : ℝ) ^ 2)⁻¹ := by
        rw [hA, hB, Finset.sum_image (fun a _ b _ h => by exact_mod_cast h),
          Finset.sum_image (fun a _ b _ h => by simpa using h)]
        simp only [Int.cast_natCast, Int.cast_neg, neg_sq, one_div]
        ring
    _ ≤ 4 := by
        have := sum_Ioo_inv_sq_le (α := ℝ) 0 (M + 1)
        norm_num at this
        linarith

/-- Each term of `c_i(v)` (`i ≥ 1`, `v ≥ 0`) is positive and at most `1/(256 n²)`. -/
theorem latticeTerm_bounds {M : ℕ} (hM : 0 < M) {n : ℤ} (hn : n ∈ latticeIdx M) {v : ℝ}
    (hv : 0 ≤ v) {i : ℕ} (hi : 1 ≤ i) :
    0 < 1 / (latticeSymbol M n * (latticeSymbol M n + v) ^ i) ∧
      1 / (latticeSymbol M n * (latticeSymbol M n + v) ^ i) ≤ 1 / 256 * (1 / ((n : ℝ) ^ 2)) := by
  obtain ⟨h0, h2⟩ := latticeIdx_ne hn
  have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have : n ^ 2 = |n| ^ 2 := (sq_abs n).symm
      have h1 : 1 ≤ |n| := Int.one_le_abs h0
      nlinarith
    exact_mod_cast this
  have hx := latticeSymbol_ge hM h2
  have hxpos : 0 < latticeSymbol M n := by linarith
  have hxv : latticeSymbol M n ≤ latticeSymbol M n + v := by linarith
  refine ⟨by positivity, ?_⟩
  have hp : (latticeSymbol M n) ^ 2 ≤ latticeSymbol M n * (latticeSymbol M n + v) ^ i := by
    calc (latticeSymbol M n) ^ 2 = latticeSymbol M n * latticeSymbol M n := by ring
      _ ≤ latticeSymbol M n * (latticeSymbol M n + v) ^ i := by
          apply mul_le_mul_of_nonneg_left _ hxpos.le
          calc latticeSymbol M n = (latticeSymbol M n) ^ 1 := (pow_one _).symm
            _ ≤ (latticeSymbol M n + v) ^ 1 := pow_le_pow_left₀ hxpos.le hxv 1
            _ ≤ (latticeSymbol M n + v) ^ i :=
                pow_le_pow_right₀ (by linarith) hi
  have h256 : 256 * (n : ℝ) ^ 2 ≤ (latticeSymbol M n) ^ 2 := by nlinarith
  calc 1 / (latticeSymbol M n * (latticeSymbol M n + v) ^ i) ≤ 1 / (latticeSymbol M n) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) hp
    _ ≤ 1 / (256 * (n : ℝ) ^ 2) := one_div_le_one_div_of_le (by positivity) h256
    _ = 1 / 256 * (1 / ((n : ℝ) ^ 2)) := by field_simp

/-- `0 < c_i(v) < 1/20` for `v ≥ 0`, `i ≥ 1`, `M ≥ 3` (P4 (5.13)). -/
theorem latticeSum_pos {M : ℕ} (hM : 3 ≤ M) {v : ℝ} (hv : 0 ≤ v) {i : ℕ} (hi : 1 ≤ i) :
    0 < latticeSum M v i := by
  have h1 : (1 : ℤ) ∈ latticeIdx M := by
    simp only [latticeIdx, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, by norm_num, ?_⟩
    simp; omega
  unfold latticeSum
  exact Finset.sum_pos (fun n hn => (latticeTerm_bounds (by omega) hn hv hi).1) ⟨1, h1⟩

theorem latticeSum_lt {M : ℕ} (hM : 3 ≤ M) {v : ℝ} (hv : 0 ≤ v) {i : ℕ} (hi : 1 ≤ i) :
    latticeSum M v i < 1 / 20 := by
  unfold latticeSum
  calc _ ≤ ∑ n ∈ latticeIdx M, 1 / 256 * (1 / ((n : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun n hn => (latticeTerm_bounds (by omega) hn hv hi).2
    _ = 1 / 256 * ∑ n ∈ latticeIdx M, 1 / ((n : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 1 / 256 * 4 := by gcongr; exact sum_inv_sq_latticeIdx M
    _ < 1 / 20 := by norm_num

/-- `0 < c₁(v) − v c₂(v) < c₁(v)` for `v > 0` (P4 (5.13)). -/
theorem latticeSum_diff {M : ℕ} (hM : 3 ≤ M) {v : ℝ} (hv : 0 < v) :
    0 < latticeSum M v 1 - v * latticeSum M v 2 ∧
      latticeSum M v 1 - v * latticeSum M v 2 < latticeSum M v 1 := by
  have e : latticeSum M v 1 - v * latticeSum M v 2 =
      ∑ n ∈ latticeIdx M, 1 / ((latticeSymbol M n + v) ^ 2) := by
    unfold latticeSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨h0, h2⟩ := latticeIdx_ne hn
    have hx := latticeSymbol_ge (by omega : 0 < M) h2
    have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hxpos : 0 < latticeSymbol M n := by linarith
    have : latticeSymbol M n + v ≠ 0 := by linarith
    field_simp
    ring
  rw [e]
  constructor
  · refine Finset.sum_pos (fun n hn => ?_) ⟨1, ?_⟩
    · obtain ⟨h0, h2⟩ := latticeIdx_ne hn
      have hx := latticeSymbol_ge (by omega : 0 < M) h2
      have hn0 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      exact one_div_pos.2 (pow_pos (by linarith) 2)
    · simp only [latticeIdx, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by norm_num, ?_⟩
      simp; omega
  · have := latticeSum_pos hM hv.le (i := 2) (by norm_num)
    linarith [mul_pos hv this]

/-- **The parameter range of Lemma 3.1 holds for the lattice sums of P4 (5.13)**: for `M = L^m ≥ 3`,
`a ∈ [9/10, 3/2]`, `0 < v ≤ 7/32`, the parameters `(a, v, τ, c₁(v), c₂(v))` lie in `InftyRange`. -/
theorem inftyRange_latticeSums {M : ℕ} (hM : 3 ≤ M) {a v : ℝ} (ha1 : 9 / 10 ≤ a) (ha2 : a ≤ 3 / 2)
    (hv0 : 0 < v) (hv1 : v ≤ 7 / 32) :
    InftyRange a v (latticeTau M) (latticeSum M v 1) (latticeSum M v 2) := by
  have hM' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  obtain ⟨hd0, hd1⟩ := latticeSum_diff hM hv0
  refine ⟨ha1, ha2, hv0, hv1, ?_, ?_, latticeSum_pos hM hv0.le (by norm_num),
    latticeSum_lt hM hv0.le (by norm_num), latticeSum_pos hM hv0.le (by norm_num),
    latticeSum_lt hM hv0.le (by norm_num), hd0, hd1⟩
  · unfold latticeTau
    have : ((M : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM2
    linarith
  · unfold latticeTau
    have : 0 ≤ ((M : ℝ) ^ 2)⁻¹ := by positivity
    linarith

end Balaban.Flow
