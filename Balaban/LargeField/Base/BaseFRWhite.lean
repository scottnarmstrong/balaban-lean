/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NoncommRing

/-!
# Finite-range whitening of a matrix with `‖K‖ < 1` (route FR-1, row A3-1 (a)/(b))

For a complex matrix `K` on a finite set with `‖K‖ ≤ q < 1` (operator norm on `ℓ²`) the series
`S(K) = ∑_n w_n Kⁿ`, `w_n = C(2n, n)/4ⁿ` (the coefficients of `(1 - t)^{-1/2}`), is the square root
of `(1 - K)⁻¹`: `S(K)² (1 - K) = 1`, `‖S(K)‖ ≤ (1 - q)^{-1/2}`. Its truncation
`S_R(K) = ∑_{n ≤ R} w_n Kⁿ` has finite range: if `K x y = 0` for `δ x y > r` then `S_R(K) x y = 0`
for `δ x y > R r`, and the defect `D_R = S_R(K)² (1 - K) - 1` vanishes beyond `(2R + 1) r` and is
small, `‖D_R‖ ≤ 4 (1 - q)^{-1/2} q^{R+1}/(1 - q)`. The entries of `S_R(K)` and `D_R` are polynomials
in the entries of `K`, hence analytic. This is the analytic core of the local whitening
`u = β^{-1/2} W ψ'` of the first step (`W ≈ A_e^{-1/2}`, `A_e = c (1 - K_e)`); it extends the
route FR of `KF0FRWhite.lean`, where `K = -Δ + ν` is constant and the walk coefficients are
positive, to matrices that depend on the background.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Finset
open scoped Matrix.Norms.L2Operator


namespace Balaban.LargeField.FRWhite

/-- The coefficients `w_n = C(2n,n)/4^n` of `(1 - t)^{-1/2}`. -/
noncomputable def sqrtCoef (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

theorem sqrtCoef_nonneg (n : ℕ) : 0 ≤ sqrtCoef n := by unfold sqrtCoef; positivity

theorem sqrtCoef_le_one (n : ℕ) : sqrtCoef n ≤ 1 := by
  unfold sqrtCoef
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.centralBinom_le_four_pow n

theorem sqrtCoef_zero : sqrtCoef 0 = 1 := by simp [sqrtCoef]

theorem succ_mul_sqrtCoef_succ (n : ℕ) :
    ((n : ℝ) + 1) * sqrtCoef (n + 1) = (2 * n + 1) / 2 * sqrtCoef n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have h' : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * n + 1) * (Nat.centralBinom n : ℝ) := by exact_mod_cast h
  unfold sqrtCoef
  rw [pow_succ]
  field_simp
  linarith

/-- The Cauchy square of the series: `∑_{i+j=n} w_i w_j = 1` (the series squares to `1/(1-t)`). -/
theorem sum_antidiagonal_sqrtCoef (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, sqrtCoef p.1 * sqrtCoef p.2 = 1 := by
  induction n with
  | zero => simp [sqrtCoef_zero]
  | succ n ih =>
    set c : ℕ → ℝ := fun m => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, sqrtCoef p.1 * sqrtCoef p.2 with hc
    set dd : ℕ → ℝ := fun m =>
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (p.1 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2) with hd
    -- symmetry: 2 d_m = m c_m
    have hsym : ∀ m, 2 * dd m = m * c m := by
      intro m
      have h1 : dd m = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (p.2 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2) := by
        rw [hd]
        simp only
        rw [← Finset.Nat.sum_antidiagonal_swap]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [mul_comm]
      have h2 : dd m + dd m = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          ((p.1 : ℝ) + p.2) * (sqrtCoef p.1 * sqrtCoef p.2) := by
        conv_lhs => arg 2; rw [h1]
        rw [hd]
        simp only
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
      have h3 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, ((p.1 : ℝ) + p.2) * (sqrtCoef p.1 * sqrtCoef p.2)
          = m * c m := by
        rw [hc]; simp only
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [← this]; push_cast; ring
      linarith
    -- shift: d_{m+1} = d_m + c_m / 2
    have hshift : dd (n + 1) = dd n + c n / 2 := by
      rw [hd]; simp only
      rw [Finset.Nat.sum_antidiagonal_succ]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      have : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((p.1 + 1 : ℕ) : ℝ) * (sqrtCoef (p.1 + 1) * sqrtCoef p.2) =
          (p.1 : ℝ) * (sqrtCoef p.1 * sqrtCoef p.2) + (1 / 2) * (sqrtCoef p.1 * sqrtCoef p.2) := by
        intro p _
        have h := succ_mul_sqrtCoef_succ p.1
        push_cast
        calc ((p.1 : ℝ) + 1) * (sqrtCoef (p.1 + 1) * sqrtCoef p.2)
            = (((p.1 : ℝ) + 1) * sqrtCoef (p.1 + 1)) * sqrtCoef p.2 := by ring
          _ = _ := by rw [h]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hc]; simp only; ring
    have h1 := hsym (n + 1)
    have h2 := hsym n
    rw [hshift] at h1
    have : c (n + 1) = c n := by
      push_cast at h1
      nlinarith
    show c (n + 1) = 1
    rw [this]; exact ih


section Banach

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

/-- The series `S(K) = ∑_n w_n Kⁿ`. -/
noncomputable def sqrtSeries (K : 𝔸) : 𝔸 := ∑' n : ℕ, ((sqrtCoef n : ℝ) : ℂ) • K ^ n

/-- The truncation `S_R(K) = ∑_{n ≤ R} w_n Kⁿ`. -/
noncomputable def sqrtTrunc (K : 𝔸) (R : ℕ) : 𝔸 :=
  ∑ n ∈ range (R + 1), ((sqrtCoef n : ℝ) : ℂ) • K ^ n

variable {K : 𝔸} {q : ℝ}

theorem norm_term_le (hK : ‖K‖ ≤ q) (n : ℕ) :
    ‖((sqrtCoef n : ℝ) : ℂ) • K ^ n‖ ≤ sqrtCoef n * q ^ n := by
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (sqrtCoef_nonneg n)]
  exact mul_le_mul_of_nonneg_left ((norm_pow_le K n).trans (pow_le_pow_left₀ (norm_nonneg _) hK n))
    (sqrtCoef_nonneg n)

theorem summable_sqrtCoef_mul_pow (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable fun n : ℕ => sqrtCoef n * q ^ n :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (sqrtCoef_nonneg n) (pow_nonneg hq0 n))
    (fun n => by
      calc sqrtCoef n * q ^ n ≤ 1 * q ^ n :=
            mul_le_mul_of_nonneg_right (sqrtCoef_le_one n) (pow_nonneg hq0 n)
        _ = q ^ n := one_mul _)
    (summable_geometric_of_lt_one hq0 hq)

theorem summable_norm_term (hK : ‖K‖ ≤ q) (hq0 : 0 ≤ q) (hq : q < 1) :
    Summable fun n : ℕ => ‖((sqrtCoef n : ℝ) : ℂ) • K ^ n‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hK)
    (summable_sqrtCoef_mul_pow hq0 hq)

/-- `∑ w_n qⁿ = (1 - q)^{-1/2}`. -/
theorem tsum_sqrtCoef_mul_pow (hq0 : 0 ≤ q) (hq : q < 1) :
    ∑' n : ℕ, sqrtCoef n * q ^ n = Real.sqrt (1 - q)⁻¹ := by
  have hs := summable_sqrtCoef_mul_pow hq0 hq
  have hsn : Summable fun n : ℕ => ‖sqrtCoef n * q ^ n‖ := by
    simpa [Real.norm_of_nonneg (mul_nonneg (sqrtCoef_nonneg _) (pow_nonneg hq0 _))] using hs
  have hsq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsn hsn
  have h2 : (∑' n : ℕ, sqrtCoef n * q ^ n) * (∑' n : ℕ, sqrtCoef n * q ^ n) = (1 - q)⁻¹ := by
    rw [hsq]
    have : ∀ n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (sqrtCoef kl.1 * q ^ kl.1) * (sqrtCoef kl.2 * q ^ kl.2) = q ^ n := by
      intro n
      have : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (sqrtCoef kl.1 * q ^ kl.1) * (sqrtCoef kl.2 * q ^ kl.2) =
            (sqrtCoef kl.1 * sqrtCoef kl.2) * q ^ n := by
        intro kl hkl
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
        rw [← this, pow_add]; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, sum_antidiagonal_sqrtCoef, one_mul]
    simp only [this]
    exact tsum_geometric_of_lt_one hq0 hq
  have h0 : 0 ≤ ∑' n : ℕ, sqrtCoef n * q ^ n :=
    tsum_nonneg fun n => mul_nonneg (sqrtCoef_nonneg n) (pow_nonneg hq0 n)
  rw [← h2, ← sq, Real.sqrt_sq h0]

theorem norm_sqrtSeries_le (hK : ‖K‖ ≤ q) (hq0 : 0 ≤ q) (hq : q < 1) :
    ‖sqrtSeries K‖ ≤ Real.sqrt (1 - q)⁻¹ := by
  have hf := summable_norm_term hK hq0 hq
  have hs := summable_sqrtCoef_mul_pow hq0 hq
  have h1 : ‖sqrtSeries K‖ ≤ ∑' n : ℕ, ‖((sqrtCoef n : ℝ) : ℂ) • K ^ n‖ :=
    norm_tsum_le_tsum_norm hf
  have h2 : ∑' n : ℕ, ‖((sqrtCoef n : ℝ) : ℂ) • K ^ n‖ ≤ ∑' n : ℕ, sqrtCoef n * q ^ n :=
    Summable.tsum_le_tsum (fun n => norm_term_le hK n) hf hs
  rw [← tsum_sqrtCoef_mul_pow hq0 hq]
  exact h1.trans h2

theorem norm_sqrtTrunc_le (hK : ‖K‖ ≤ q) (hq0 : 0 ≤ q) (hq : q < 1) (R : ℕ) :
    ‖sqrtTrunc K R‖ ≤ Real.sqrt (1 - q)⁻¹ := by
  unfold sqrtTrunc
  rw [← tsum_sqrtCoef_mul_pow hq0 hq]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun n _ => norm_term_le hK n).trans ?_
  exact (summable_sqrtCoef_mul_pow hq0 hq).sum_le_tsum _
    (fun n _ => mul_nonneg (sqrtCoef_nonneg n) (pow_nonneg hq0 n))

/-- `S(K)² (1 - K) = 1`. -/
theorem sqrtSeries_mul_self_mul (hK : ‖K‖ ≤ q) (hq0 : 0 ≤ q) (hq : q < 1) :
    sqrtSeries K * sqrtSeries K * (1 - K) = 1 := by
  have hf := summable_norm_term hK hq0 hq
  have hsq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hf
  have hK1 : ‖K‖ < 1 := lt_of_le_of_lt hK hq

  have e1 : sqrtSeries K * sqrtSeries K = ∑' n : ℕ, K ^ n := by
    unfold sqrtSeries
    rw [hsq]
    refine tsum_congr fun n => ?_
    have : ∀ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (((sqrtCoef kl.1 : ℝ) : ℂ) • K ^ kl.1) * (((sqrtCoef kl.2 : ℝ) : ℂ) • K ^ kl.2) =
          (((sqrtCoef kl.1 * sqrtCoef kl.2 : ℝ)) : ℂ) • K ^ n := by
      intro kl hkl
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
      rw [smul_mul_smul_comm, ← pow_add, this]
      push_cast; rfl
    rw [Finset.sum_congr rfl this, ← Finset.sum_smul, ← Complex.ofReal_sum,
      sum_antidiagonal_sqrtCoef]
    simp
  rw [e1]
  exact geom_series_mul_neg K hK1

/-- The tail of the series. -/
theorem norm_sqrtSeries_sub_sqrtTrunc_le (hK : ‖K‖ ≤ q) (hq0 : 0 ≤ q) (hq : q < 1) (R : ℕ) :
    ‖sqrtSeries K - sqrtTrunc K R‖ ≤ q ^ (R + 1) / (1 - q) := by
  have hf := summable_norm_term hK hq0 hq
  have hs : Summable fun n : ℕ => ((sqrtCoef n : ℝ) : ℂ) • K ^ n :=
    hf.of_norm
  have h := hs.sum_add_tsum_nat_add (R + 1)
  have e : sqrtSeries K - sqrtTrunc K R =
      ∑' n : ℕ, ((sqrtCoef (n + (R + 1)) : ℝ) : ℂ) • K ^ (n + (R + 1)) := by
    unfold sqrtSeries sqrtTrunc
    rw [← h]; abel
  rw [e]
  have hg : Summable fun n : ℕ => q ^ (n + (R + 1)) := by
    simpa [pow_add, mul_comm] using (summable_geometric_of_lt_one hq0 hq).mul_left (q ^ (R + 1))
  have hb : ∀ n : ℕ, ‖((sqrtCoef (n + (R + 1)) : ℝ) : ℂ) • K ^ (n + (R + 1))‖ ≤ q ^ (n + (R + 1)) :=
    fun n => (norm_term_le hK (n + (R + 1))).trans (by
      calc sqrtCoef (n + (R + 1)) * q ^ (n + (R + 1)) ≤ 1 * q ^ (n + (R + 1)) :=
            mul_le_mul_of_nonneg_right (sqrtCoef_le_one _) (pow_nonneg hq0 _)
        _ = _ := one_mul _)
  calc _ ≤ ∑' n : ℕ, q ^ (n + (R + 1)) :=
        (norm_tsum_le_tsum_norm ((hf.comp_injective (add_left_injective (R + 1))))).trans
          (Summable.tsum_le_tsum hb ((hf.comp_injective (add_left_injective (R + 1)))) hg)
    _ = q ^ (R + 1) / (1 - q) := by
        simp only [pow_add]
        rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq]; field_simp

end Banach


section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entries of a matrix are bounded by its `ℓ²` operator norm. -/
theorem norm_entry_le_l2 (M : Matrix ι ι ℂ) (x y : ι) : ‖M x y‖ ≤ ‖M‖ := by
  have h := Matrix.l2_opNorm_mulVec M (EuclideanSpace.single y (1 : ℂ))
  have hx := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℂ).symm
    (M.mulVec (EuclideanSpace.single y (1 : ℂ)))) x
  have e : (EuclideanSpace.equiv ι ℂ).symm
      (M.mulVec (EuclideanSpace.single y (1 : ℂ))) x = M x y := by
    simp
  rw [e] at hx
  have h1 : ‖(EuclideanSpace.single y (1 : ℂ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  exact hx.trans h

variable (δ : ι → ι → ℕ)

/-- The distance function is zero on the diagonal. -/
def DistSelf (δ : ι → ι → ℕ) : Prop := ∀ x, δ x x = 0

/-- The triangle inequality. -/
def DistTri (δ : ι → ι → ℕ) : Prop := ∀ x y z, δ x z ≤ δ x y + δ y z

/-- The matrix `M` has range `r` for the distance `δ`: `M x y = 0` when `δ x y > r`. -/
def HasRange (M : Matrix ι ι ℂ) (r : ℕ) : Prop := ∀ x y, r < δ x y → M x y = 0

variable {δ}

theorem HasRange.mono {M : Matrix ι ι ℂ} {r r' : ℕ} (h : HasRange δ M r) (hr : r ≤ r') :
    HasRange δ M r' := fun x y hxy => h x y (lt_of_le_of_lt hr hxy)

omit [DecidableEq ι] in
theorem HasRange.mul [DecidableEq ι] (hδ : DistTri δ) {A B : Matrix ι ι ℂ} {r s : ℕ} (hA : HasRange δ A r)
    (hB : HasRange δ B s) : HasRange δ (A * B) (r + s) := by
  intro x y hxy
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases h1 : r < δ x z
  · rw [hA x z h1, zero_mul]
  · have h2 : s < δ z y := by
      have := hδ x z y
      omega
    rw [hB z y h2, mul_zero]

theorem HasRange.one (hδ0 : DistSelf δ) : HasRange δ (1 : Matrix ι ι ℂ) 0 := by
  intro x y hxy
  have hne : x ≠ y := by
    rintro rfl
    rw [hδ0] at hxy
    exact lt_irrefl _ hxy
  simp [hne]

omit [DecidableEq ι] in
theorem HasRange.add {A B : Matrix ι ι ℂ} {r : ℕ} (hA : HasRange δ A r) (hB : HasRange δ B r) :
    HasRange δ (A + B) r := fun x y hxy => by
  simp [hA x y hxy, hB x y hxy]

omit [DecidableEq ι] in
theorem HasRange.sub {A B : Matrix ι ι ℂ} {r : ℕ} (hA : HasRange δ A r) (hB : HasRange δ B r) :
    HasRange δ (A - B) r := fun x y hxy => by
  simp [hA x y hxy, hB x y hxy]

omit [DecidableEq ι] in
theorem HasRange.smul {A : Matrix ι ι ℂ} {r : ℕ} (hA : HasRange δ A r) (c : ℂ) :
    HasRange δ (c • A) r := fun x y hxy => by
  simp [hA x y hxy]

theorem HasRange.pow (hδ0 : DistSelf δ) (hδ : DistTri δ) {K : Matrix ι ι ℂ} {r : ℕ} (hK : HasRange δ K r) (n : ℕ) :
    HasRange δ (K ^ n) (n * r) := by
  induction n with
  | zero => simpa using HasRange.one hδ0
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact HasRange.mul hδ ih hK

omit [Fintype ι] in
theorem HasRange.sum {s : Finset ℕ} {f : ℕ → Matrix ι ι ℂ} {r : ℕ}
    (h : ∀ n ∈ s, HasRange δ (f n) r) : HasRange δ (∑ n ∈ s, f n) r := fun x y hxy => by
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun n hn => h n hn x y hxy

/-- The truncation `S_R(K)` has range `R r`. -/
theorem sqrtTrunc_hasRange (hδ0 : DistSelf δ) (hδ : DistTri δ) {K : Matrix ι ι ℂ} {r : ℕ} (hK : HasRange δ K r) (R : ℕ) :
    HasRange δ (sqrtTrunc K R) (R * r) := by
  unfold sqrtTrunc
  refine HasRange.sum fun n hn => ?_
  have hn' : n ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  exact ((HasRange.pow hδ0 hδ hK n).smul _).mono (Nat.mul_le_mul_right r hn')

/-- The defect of the truncated whitening: `D_R = S_R(K)² (1 - K) - 1`. -/
noncomputable def whiteDefect (K : Matrix ι ι ℂ) (R : ℕ) : Matrix ι ι ℂ :=
  sqrtTrunc K R * sqrtTrunc K R * (1 - K) - 1

/-- The defect vanishes beyond `(2R + 1) r`. -/
theorem whiteDefect_hasRange (hδ0 : DistSelf δ) (hδ : DistTri δ) {K : Matrix ι ι ℂ} {r : ℕ} (hK : HasRange δ K r) (R : ℕ) :
    HasRange δ (whiteDefect K R) ((2 * R + 1) * r) := by
  have hS := sqrtTrunc_hasRange hδ0 hδ hK R
  have h1 : HasRange δ (1 - K) r := (HasRange.one hδ0).mono (Nat.zero_le r) |>.sub hK
  have h2 := HasRange.mul hδ (HasRange.mul hδ hS hS) h1
  have e : R * r + R * r + r = (2 * R + 1) * r := by ring
  rw [e] at h2
  exact h2.sub (((HasRange.one hδ0).mono (Nat.zero_le _)))

/-- **The defect is small**: `‖D_R‖ ≤ 4 (1 - q)^{-1/2} q^{R+1}/(1 - q)`. -/
theorem norm_whiteDefect_le [Nonempty ι] {K : Matrix ι ι ℂ} {q : ℝ} (hK : ‖K‖ ≤ q) (hq0 : 0 ≤ q)
    (hq : q < 1) (R : ℕ) :
    ‖whiteDefect K R‖ ≤ 4 * Real.sqrt (1 - q)⁻¹ * (q ^ (R + 1) / (1 - q)) := by
  set S := sqrtSeries K
  set T := sqrtTrunc K R
  have hSS : S * S * (1 - K) = 1 := sqrtSeries_mul_self_mul hK hq0 hq
  have e : whiteDefect K R = ((T - S) * T + S * (T - S)) * (1 - K) := by
    have h1 : (T - S) * T + S * (T - S) = T * T - S * S := by noncomm_ring
    have h2 : whiteDefect K R = T * T * (1 - K) - S * S * (1 - K) := by
      unfold whiteDefect
      rw [hSS]
    rw [h2, h1, sub_mul]
  have hT := norm_sqrtTrunc_le hK hq0 hq R
  have hS' := norm_sqrtSeries_le hK hq0 hq
  have hD : ‖T - S‖ ≤ q ^ (R + 1) / (1 - q) := by
    rw [norm_sub_rev]; exact norm_sqrtSeries_sub_sqrtTrunc_le hK hq0 hq R
  have hK1 : ‖1 - K‖ ≤ 2 := by
    calc ‖1 - K‖ ≤ ‖(1 : Matrix ι ι ℂ)‖ + ‖K‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith
      _ = 2 := by norm_num
  have hσ : 0 ≤ Real.sqrt (1 - q)⁻¹ := Real.sqrt_nonneg _
  have hDn : 0 ≤ q ^ (R + 1) / (1 - q) := div_nonneg (pow_nonneg hq0 _) (by linarith)
  rw [e]
  calc ‖((T - S) * T + S * (T - S)) * (1 - K)‖
      ≤ ‖(T - S) * T + S * (T - S)‖ * ‖1 - K‖ := norm_mul_le _ _
    _ ≤ (‖T - S‖ * ‖T‖ + ‖S‖ * ‖T - S‖) * 2 := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ((q ^ (R + 1) / (1 - q)) * Real.sqrt (1 - q)⁻¹ +
          Real.sqrt (1 - q)⁻¹ * (q ^ (R + 1) / (1 - q))) * 2 := by gcongr
    _ = 4 * Real.sqrt (1 - q)⁻¹ * (q ^ (R + 1) / (1 - q)) := by ring


/-- Row sums of a matrix of range `ρ`: `∑_y |M x y| ≤ #{y : δ x y ≤ ρ} · ‖M‖`. -/
theorem sum_norm_row_le {M : Matrix ι ι ℂ} {ρ : ℕ} (hM : HasRange δ M ρ) (x : ι) :
    ∑ y, ‖M x y‖ ≤
      ((Finset.univ.filter fun y => δ x y ≤ ρ).card : ℝ) * ‖M‖ := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun y => δ x y ≤ ρ)]
  · calc ∑ y ∈ Finset.univ.filter (fun y => δ x y ≤ ρ), ‖M x y‖
        ≤ ∑ _y ∈ Finset.univ.filter (fun y => δ x y ≤ ρ), ‖M‖ :=
          Finset.sum_le_sum fun y _ => norm_entry_le_l2 M x y
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  · intro y _ hy
    by_contra hc
    exact hy (by rw [hM x y (not_le.mp hc), norm_zero])

end Matrices

section Analytic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem analyticOnNhd_entry {f : Matrix ι ι ℂ → Matrix ι ι ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (x y : ι) :
    AnalyticOnNhd ℂ (fun K => f K x y) Set.univ := by
  let e : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ x y)
  intro K hK
  exact e.analyticAt (f K) |>.comp (hf K hK)

theorem analyticOnNhd_pow (n : ℕ) :
    AnalyticOnNhd ℂ (fun K : Matrix ι ι ℂ => K ^ n) Set.univ := fun _ _ =>
  analyticAt_id.pow n

/-- The entries of the truncation `S_R(K)` are polynomials in the entries of `K`, hence analytic on
the whole matrix space. -/
theorem analyticOnNhd_sqrtTrunc (R : ℕ) :
    AnalyticOnNhd ℂ (fun K : Matrix ι ι ℂ => sqrtTrunc K R) Set.univ := fun K hK => by
  unfold sqrtTrunc
  exact Finset.analyticAt_fun_sum _ fun n _ =>
    (analyticAt_const.fun_smul (analyticOnNhd_pow n K hK))

theorem analyticOnNhd_sqrtTrunc_entry (R : ℕ) (x y : ι) :
    AnalyticOnNhd ℂ (fun K : Matrix ι ι ℂ => sqrtTrunc K R x y) Set.univ :=
  analyticOnNhd_entry (analyticOnNhd_sqrtTrunc R) x y

/-- The defect `D_R` is a polynomial in the matrix `K`. -/
theorem analyticOnNhd_whiteDefect (R : ℕ) :
    AnalyticOnNhd ℂ (fun K : Matrix ι ι ℂ => whiteDefect K R) Set.univ := fun K hK => by
  unfold whiteDefect
  have h := analyticOnNhd_sqrtTrunc (ι := ι) R K hK
  exact ((h.mul h).mul (analyticAt_const.sub analyticAt_id)).sub analyticAt_const

theorem analyticOnNhd_whiteDefect_entry (R : ℕ) (x y : ι) :
    AnalyticOnNhd ℂ (fun K : Matrix ι ι ℂ => whiteDefect K R x y) Set.univ :=
  analyticOnNhd_entry (analyticOnNhd_whiteDefect R) x y

end Analytic

end Balaban.LargeField.FRWhite
