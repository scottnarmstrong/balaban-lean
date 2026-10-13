/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0KilledWalks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant walk formula for the good-region operator (package H37-3, part 2)

`D` a set of sites of the torus, `G = Dᶜ`, `K_Λ = -Δ + ν = a_ν 1 - A`, `K_G` the principal
submatrix on `G` (`kwOpSub`; its padded form is `kwOp = a_ν 1 - A_G`).  With `a_ν = 2d + ν`,
`q = 2d/(2d + ν)`:

* `kw_logdet_hasSum`: `log det K_Λ - log det K_G - |D| log a_ν = - ∑_{k ≥ 1} (tr A^k - tr A_G^k)/(k a_ν^k)`,
  absolutely convergent, with `det K_Λ, det K_G > 0` (`kw_logdet_eq`).
* `kwTraceDiff_nonneg`, `kwTraceDiff_le`: `0 ≤ tr A^n - tr A_G^n ≤ 2 n |D| (2d)^n`
  (constant `2`: the telescoping identity `A^n - A_G^n = ∑_i A^i (A - A_G) A_G^{n-1-i}` and the
  fact that `A - A_G` has total mass at most `4d|D|`).  The sharp walk count `n |D| (2d)^n` of the
  note is not formalized; the constant `2` is the only change.
* `kw_loop_sum_le`, `kw_loop_tail_le`: the loop sum lies in `[0, 2|D| q/(1-q)]` and the terms of
  length `≥ R` total at most `2|D| q^R/(1-q)`; here `q/(1-q) = 2d/ν`.
* `kw_det_ratio_bounds`: `exp(-2|D| q/(1-q)) ≤ det K_Λ/(det K_G a_ν^{|D|}) ≤ 1`.
* `kw_jacobi`: `det K_G = det K_Λ · det ((K_Λ⁻¹)_{DD})` (Jacobi / Schur complement).

These are facts about the Dirichlet-type reference operator on a region with holes; the conditional
integral with boundary data, the linked expansion and Root-F are NOT treated here.
-/

@[expose] public section

open Matrix Finset Balaban.Green

namespace Balaban

namespace KW

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem rowSum_mul_le {P Q : Matrix ι ι ℝ} (hP : ∀ x y, 0 ≤ P x y) {p q : ℝ}
    (hp : ∀ x, ∑ y, P x y ≤ p) (hq : ∀ x, ∑ y, Q x y ≤ q) (hQ : ∀ x y, 0 ≤ Q x y) (x : ι) :
    ∑ y, (P * Q) x y ≤ p * q := by
  simp_rw [Matrix.mul_apply]
  rw [Finset.sum_comm]
  calc ∑ z, ∑ y, P x z * Q z y = ∑ z, P x z * ∑ y, Q z y := by simp_rw [← Finset.mul_sum]
    _ ≤ ∑ z, P x z * q := Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hq z) (hP _ _)
    _ = (∑ z, P x z) * q := by rw [Finset.sum_mul]
    _ ≤ p * q := mul_le_mul_of_nonneg_right (hp x) ((Finset.sum_nonneg fun y _ => hQ x y).trans
        (hq x))

omit [DecidableEq ι] in
/-- `tr (E M) ≤ r ∑ E` for nonnegative `E, M` with row sums of `M` at most `r`. -/
theorem trace_mul_le {E M : Matrix ι ι ℝ} (hE : ∀ x y, 0 ≤ E x y) (hM : ∀ x y, 0 ≤ M x y) {r : ℝ}
    (hr : ∀ x, ∑ y, M x y ≤ r) : (E * M).trace ≤ r * ∑ x, ∑ y, E x y := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  have : M y x ≤ r := (Finset.single_le_sum (f := fun x' => M y x') (fun x' _ => hM y x')
    (Finset.mem_univ x)).trans (hr y)
  nlinarith [hE x y]

/-- The telescoping identity `A^{n+1} - B^{n+1} = ∑_{i ≤ n} A^i (A - B) B^{n-i}`. -/
theorem pow_sub_pow_telescope {R : Type*} [Ring R] (A B : R) (n : ℕ) :
    A ^ (n + 1) - B ^ (n + 1) = ∑ i ∈ Finset.range (n + 1), A ^ i * (A - B) * B ^ (n - i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n + 1), Nat.sub_self, pow_zero, mul_one]
    have h : ∑ i ∈ Finset.range (n + 1), A ^ i * (A - B) * B ^ (n + 1 - i) =
        (∑ i ∈ Finset.range (n + 1), A ^ i * (A - B) * B ^ (n - i)) * B := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have : n + 1 - i = (n - i) + 1 := by
        have := Finset.mem_range.1 hi; omega
      rw [this, pow_succ]; simp only [mul_assoc]
    rw [h, ← ih]
    noncomm_ring

end Generic

end KW

variable {d m : ℕ} [NeZero m]

/-- Total mass of `A - A_G`: at most `4d|D|`. -/
theorem kwAdj_sub_total_le (D : Finset (Torus d m)) :
    ∑ x, ∑ y, (kwAdj d m - kwAdjG d m D) x y ≤ 4 * d * D.card := by
  have hle : ∀ x y, (kwAdj d m - kwAdjG d m D) x y ≤
      (if x ∈ D then kwAdj d m x y else 0) + (if y ∈ D then kwAdj d m x y else 0) := by
    intro x y
    simp only [Matrix.sub_apply, kwAdjG, Matrix.of_apply]
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;> simp [hx, hy, kwAdj_nonneg x y]
  calc ∑ x, ∑ y, (kwAdj d m - kwAdjG d m D) x y
      ≤ ∑ x, ∑ y, ((if x ∈ D then kwAdj d m x y else 0) +
          (if y ∈ D then kwAdj d m x y else 0)) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hle x y
    _ = (∑ x, ∑ y, (if x ∈ D then kwAdj d m x y else 0)) +
        ∑ x, ∑ y, (if y ∈ D then kwAdj d m x y else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = 2 * d * D.card + 2 * d * D.card := by
        have h1 : ∀ x : Torus d m, ∑ y, (if x ∈ D then kwAdj d m x y else 0) =
            if x ∈ D then (2 * d : ℝ) else 0 := by
          intro x; split_ifs
          · exact kwAdj_rowSum x
          · simp
        have h2 : ∀ y : Torus d m, ∑ x, (if y ∈ D then kwAdj d m x y else 0) =
            if y ∈ D then (2 * d : ℝ) else 0 := by
          intro y; split_ifs
          · rw [← kwAdj_rowSum y]; exact Finset.sum_congr rfl fun x _ => kwAdj_symm x y
          · simp
        rw [Finset.sum_comm (f := fun x y => if y ∈ D then kwAdj d m x y else 0)]
        simp only [h1, h2, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ = 4 * d * D.card := by ring

/-- `tr A^n - tr A_G^n`: the number of rooted closed walks of length `n` on the torus that visit
`D` (with adjacency multiplicity). -/
def kwTraceDiff (d m : ℕ) [NeZero m] (D : Finset (Torus d m)) (n : ℕ) : ℝ :=
  (kwAdj d m ^ n).trace - (kwAdjG d m D ^ n).trace

theorem kwTraceDiff_nonneg (D : Finset (Torus d m)) (n : ℕ) : 0 ≤ kwTraceDiff d m D n := by
  unfold kwTraceDiff
  rw [sub_nonneg]
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.sum_le_sum fun x _ =>
    KW.pow_entry_mono (kwAdjG_nonneg D) (kwAdjG_le D) n x x

/-- **Trace bound** (T4): `0 ≤ tr A^n - tr A_G^n ≤ 2 n |D| (2d)^n`. -/
theorem kwTraceDiff_le (D : Finset (Torus d m)) (n : ℕ) :
    kwTraceDiff d m D n ≤ 2 * n * D.card * (2 * d : ℝ) ^ n := by
  cases n with
  | zero => simp [kwTraceDiff]
  | succ k =>
    unfold kwTraceDiff
    rw [← Matrix.trace_sub, KW.pow_sub_pow_telescope, Matrix.trace_sum]
    have hE : ∀ x y, 0 ≤ (kwAdj d m - kwAdjG d m D) x y := fun x y => by
      rw [Matrix.sub_apply, sub_nonneg]; exact kwAdjG_le D x y
    have hA0 : ∀ x y, 0 ≤ kwAdj d m x y := kwAdj_nonneg
    have hrowA : ∀ x, ∑ y, kwAdj d m x y ≤ 2 * d := fun x => (kwAdj_rowSum x).le
    have hd : (0 : ℝ) ≤ 2 * d := by positivity
    have hterm : ∀ i ∈ Finset.range (k + 1),
        (kwAdj d m ^ i * (kwAdj d m - kwAdjG d m D) * kwAdjG d m D ^ (k - i)).trace ≤
          (2 * d : ℝ) ^ k * (4 * d * D.card) := by
      intro i hi
      have hik : i + (k - i) = k := by have := Finset.mem_range.1 hi; omega
      have hM0 : ∀ x y, 0 ≤ (kwAdjG d m D ^ (k - i) * kwAdj d m ^ i) x y := fun x y => by
        rw [Matrix.mul_apply]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (KW.pow_entry_nonneg (kwAdjG_nonneg D) _ _ _)
          (KW.pow_entry_nonneg hA0 _ _ _)
      have hMr : ∀ x, ∑ y, (kwAdjG d m D ^ (k - i) * kwAdj d m ^ i) x y ≤ (2 * d : ℝ) ^ k := by
        intro x
        have := KW.rowSum_mul_le (KW.pow_entry_nonneg (kwAdjG_nonneg D) (k - i))
          (KW.pow_rowSum_le (kwAdjG_nonneg D) hd (kwAdjG_rowSum_le D) (k - i))
          (KW.pow_rowSum_le hA0 hd hrowA i) (KW.pow_entry_nonneg hA0 i) x
        rwa [← pow_add, add_comm, hik] at this
      calc (kwAdj d m ^ i * (kwAdj d m - kwAdjG d m D) * kwAdjG d m D ^ (k - i)).trace
          = ((kwAdj d m - kwAdjG d m D) * (kwAdjG d m D ^ (k - i) * kwAdj d m ^ i)).trace := by
            rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
        _ ≤ (2 * d : ℝ) ^ k * ∑ x, ∑ y, (kwAdj d m - kwAdjG d m D) x y :=
            KW.trace_mul_le hE hM0 hMr
        _ ≤ _ := mul_le_mul_of_nonneg_left (kwAdj_sub_total_le D) (by positivity)
    calc ∑ i ∈ Finset.range (k + 1),
          (kwAdj d m ^ i * (kwAdj d m - kwAdjG d m D) * kwAdjG d m D ^ (k - i)).trace
        ≤ ∑ i ∈ Finset.range (k + 1), (2 * d : ℝ) ^ k * (4 * d * D.card) :=
          Finset.sum_le_sum hterm
      _ = 2 * ((k + 1 : ℕ) : ℝ) * D.card * (2 * d : ℝ) ^ (k + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-! ### The determinant walk formula -/

/-- The loop term `(tr A^k - tr A_G^k)/(k a_ν^k)` (zero for `k = 0`). -/
noncomputable def kwLoopTerm (d m : ℕ) [NeZero m] (ν : ℝ) (D : Finset (Torus d m)) (k : ℕ) : ℝ :=
  kwTraceDiff d m D k / ((k : ℝ) * (2 * d + ν) ^ k)

section Formula

variable {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m))

include hν

omit hν in
theorem kwLoopTerm_zero : kwLoopTerm d m ν D 0 = 0 := by
  simp [kwLoopTerm]

theorem kwLoopTerm_nonneg (k : ℕ) : 0 ≤ kwLoopTerm d m ν D k := by
  unfold kwLoopTerm
  exact div_nonneg (kwTraceDiff_nonneg D k) (by have := kw_a_pos (d := d) hν; positivity)

theorem kwLoopTerm_le (k : ℕ) : kwLoopTerm d m ν D k ≤ 2 * D.card * kwQ d ν ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [kwLoopTerm_zero D]
  · have ha := kw_a_pos (d := d) hν
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    unfold kwLoopTerm
    rw [div_le_iff₀ (by positivity)]
    refine (kwTraceDiff_le D k).trans (le_of_eq ?_)
    unfold kwQ
    rw [div_pow]
    field_simp

theorem kwLoop_hasSum_shift :
    HasSum (fun n : ℕ => kwLoopTerm d m ν D (n + 1))
      (Real.log (kwOpSub d m ν D).det + D.card * Real.log (2 * d + ν) -
        Real.log (latticeLaplacian d m ν).det) := by
  have ha := kw_a_pos (d := d) hν
  have hT0 := KW.logdet_series (kwT_isHermitian (ν := ν) (∅ : Finset (Torus d m)))
    (kwQ_lt_one hν) (kwT_absRow_le hν ∅)
  have hT := KW.logdet_series (kwT_isHermitian (ν := ν) D) (kwQ_lt_one hν) (kwT_absRow_le hν D)
  have hs := hT0.2.sub hT.2
  have hterm : ∀ n : ℕ, (kwT d m ν ∅ ^ (n + 1)).trace / ((n : ℝ) + 1) -
      (kwT d m ν D ^ (n + 1)).trace / ((n : ℝ) + 1) = kwLoopTerm d m ν D (n + 1) := by
    intro n
    have e : ∀ E : Finset (Torus d m), (kwT d m ν E ^ (n + 1)).trace =
        ((2 * d + ν)⁻¹) ^ (n + 1) * (kwAdjG d m E ^ (n + 1)).trace := by
      intro E; rw [kwT, smul_pow, Matrix.trace_smul, smul_eq_mul]
    rw [e, e, kwAdjG_empty, kwLoopTerm, kwTraceDiff]
    push_cast
    rw [inv_pow]
    field_simp
  simp only [hterm] at hs
  convert hs using 1
  -- identify the value
  have d0 : (kwOp d m ν ∅).det = (2 * d + ν) ^ Fintype.card (Torus d m) * (1 - kwT d m ν ∅).det := by
    rw [kwOp_eq_smul hν, Matrix.det_smul]
  have dD : (kwOp d m ν D).det = (2 * d + ν) ^ Fintype.card (Torus d m) * (1 - kwT d m ν D).det := by
    rw [kwOp_eq_smul hν, Matrix.det_smul]
  have hK : (latticeLaplacian d m ν).det = (kwOp d m ν ∅).det := by rw [kwOp_empty]
  have hS := kwOp_det ν D
  have hKG : 0 < (kwOpSub d m ν D).det := by
    have := kwOp_det_pos hν D
    rw [hS] at this
    exact pos_of_mul_pos_right this (pow_pos ha _).le
  have p0 := hT0.1
  have pD := hT.1
  have l0 : Real.log (kwOp d m ν ∅).det = Fintype.card (Torus d m) * Real.log (2 * d + ν) +
      Real.log (1 - kwT d m ν ∅).det := by
    rw [d0, Real.log_mul (pow_pos ha _).ne' p0.ne', Real.log_pow]
  have lD : Real.log (kwOp d m ν D).det = Fintype.card (Torus d m) * Real.log (2 * d + ν) +
      Real.log (1 - kwT d m ν D).det := by
    rw [dD, Real.log_mul (pow_pos ha _).ne' pD.ne', Real.log_pow]
  have lS : Real.log (kwOp d m ν D).det = D.card * Real.log (2 * d + ν) +
      Real.log (kwOpSub d m ν D).det := by
    rw [hS, Real.log_mul (pow_pos ha _).ne' hKG.ne', Real.log_pow]
  rw [hK]
  linarith

theorem kwOpSub_det_pos : 0 < (kwOpSub d m ν D).det := by
  have := kwOp_det_pos hν D
  rw [kwOp_det] at this
  exact pos_of_mul_pos_right this (pow_pos (kw_a_pos hν) _).le

theorem kwLoop_hasSum :
    HasSum (kwLoopTerm d m ν D)
      (Real.log (kwOpSub d m ν D).det + D.card * Real.log (2 * d + ν) -
        Real.log (latticeLaplacian d m ν).det) := by
  have h := kwLoop_hasSum_shift hν D
  have h' : HasSum (fun n => kwLoopTerm d m ν D (n + 1))
      ((Real.log (kwOpSub d m ν D).det + D.card * Real.log (2 * d + ν) -
        Real.log (latticeLaplacian d m ν).det) - ∑ i ∈ Finset.range 1, kwLoopTerm d m ν D i) := by
    simpa [kwLoopTerm_zero D] using h
  exact (hasSum_nat_add_iff' 1).1 h'

theorem latticeLaplacian_det_pos : 0 < (latticeLaplacian d m ν).det := by
  have := kwOp_det_pos hν (∅ : Finset (Torus d m))
  rwa [kwOp_empty] at this

/-- **Exact determinant walk formula** (d) (H37.7):
`log det K_Λ - log det K_G - |D| log a_ν = - ∑_{k ≥ 1} (tr A^k - tr A_G^k)/(k a_ν^k)`; the series
is absolutely convergent (nonnegative terms, `kwLoop_hasSum`). -/
theorem kw_logdet_eq :
    Real.log (latticeLaplacian d m ν).det - Real.log (kwOpSub d m ν D).det -
      D.card * Real.log (2 * d + ν) = -∑' k, kwLoopTerm d m ν D k := by
  rw [(kwLoop_hasSum hν D).tsum_eq]; ring

/-- The loop sum is nonnegative and at most `2|D| q/(1-q) = 4d|D|/ν`. -/
theorem kw_loop_sum_le : 0 ≤ ∑' k, kwLoopTerm d m ν D k ∧
    ∑' k, kwLoopTerm d m ν D k ≤ 2 * D.card * (kwQ d ν / (1 - kwQ d ν)) := by
  have hs := kwLoop_hasSum hν D
  refine ⟨hs.tsum_eq ▸ hs.nonneg (kwLoopTerm_nonneg hν D), ?_⟩
  have hg := (hasSum_geometric_of_lt_one (kwQ_nonneg (d := d) hν) (kwQ_lt_one (d := d) hν)).mul_left
    (2 * D.card : ℝ)
  have hg' := (hasSum_nat_add_iff' 1 (f := fun k : ℕ => 2 * D.card * kwQ d ν ^ k)).2 hg
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at hg'
  have hs1 := (hasSum_nat_add_iff' 1 (f := kwLoopTerm d m ν D)).2 hs
  simp only [Finset.range_one, Finset.sum_singleton, kwLoopTerm_zero D, sub_zero] at hs1
  rw [hs.tsum_eq]
  have := hasSum_le (fun n => kwLoopTerm_le hν D (n + 1)) hs1 hg'
  have e : 2 * (D.card : ℝ) * (1 - kwQ d ν)⁻¹ - 2 * D.card = 2 * D.card * (kwQ d ν / (1 - kwQ d ν)) := by
    have : (1 - kwQ d ν) ≠ 0 := (sub_pos.2 (kwQ_lt_one hν)).ne'
    field_simp
    ring
  linarith

theorem kwQ_div_one_sub : kwQ d ν / (1 - kwQ d ν) = 2 * d / ν := by
  have ha := (kw_a_pos (d := d) hν).ne'
  rw [one_sub_kwQ hν]; unfold kwQ; field_simp

/-- **Tail of the loop sum** (d): the terms of length `≥ R` are nonnegative and total at most
`2|D| q^R/(1-q)`. -/
theorem kw_loop_tail_le (R : ℕ) :
    0 ≤ ∑' n, kwLoopTerm d m ν D (n + R) ∧
      ∑' n, kwLoopTerm d m ν D (n + R) ≤ 2 * D.card * kwQ d ν ^ R / (1 - kwQ d ν) := by
  have hs := (hasSum_nat_add_iff' R (f := kwLoopTerm d m ν D)).2 (kwLoop_hasSum hν D)
  refine ⟨hs.tsum_eq ▸ hs.nonneg (fun n => kwLoopTerm_nonneg hν D _), ?_⟩
  have hg := (hasSum_geometric_of_lt_one (kwQ_nonneg (d := d) hν) (kwQ_lt_one (d := d) hν)).mul_left
    (2 * D.card * kwQ d ν ^ R : ℝ)
  have := hasSum_le (fun n => (by
    have h := kwLoopTerm_le hν D (n + R)
    rw [pow_add] at h
    linarith : kwLoopTerm d m ν D (n + R) ≤ 2 * D.card * kwQ d ν ^ R * kwQ d ν ^ n)) hs hg
  rw [hs.tsum_eq]
  calc _ ≤ _ := this
    _ = _ := by rw [div_eq_mul_inv]

/-- **Determinant scale** (e): `exp(-4d|D|/ν) ≤ det K_Λ/(det K_G a_ν^{|D|}) ≤ 1`
(`4d|D|/ν = 2|D| q/(1-q)`). -/
theorem kw_det_ratio_bounds :
    Real.exp (-(2 * D.card * (2 * d / ν))) ≤
      (latticeLaplacian d m ν).det / ((kwOpSub d m ν D).det * (2 * d + ν) ^ D.card) ∧
    (latticeLaplacian d m ν).det / ((kwOpSub d m ν D).det * (2 * d + ν) ^ D.card) ≤ 1 := by
  have h1 := latticeLaplacian_det_pos (d := d) (m := m) hν
  have h2 := kwOpSub_det_pos hν D
  have h3 : 0 < (2 * d + ν) ^ D.card := pow_pos (kw_a_pos hν) _
  have hl := kw_logdet_eq hν D
  have hr : (latticeLaplacian d m ν).det / ((kwOpSub d m ν D).det * (2 * d + ν) ^ D.card) =
      Real.exp (-∑' k, kwLoopTerm d m ν D k) := by
    rw [← hl, ← Real.log_pow, Real.exp_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2,
      Real.exp_log h3, div_div]
  obtain ⟨hn, hu⟩ := kw_loop_sum_le hν D
  rw [kwQ_div_one_sub hν] at hu
  rw [hr]
  refine ⟨Real.exp_le_exp.2 (by linarith), ?_⟩
  rw [Real.exp_le_one_iff]; linarith

end Formula

/-! ### Jacobi's identity (Schur complement) -/

/-- **Jacobi's complementary-minor identity**: for an invertible `K` and a set `p` of indices,
`det K · det ((K⁻¹)_{pp}) = det K_{p^c p^c}`. -/
theorem det_mul_det_inv_block {α : Type*} [Fintype α] [DecidableEq α] (K : Matrix α α ℝ)
    (hK : IsUnit K.det) (p : α → Prop) [DecidablePred p] [Fintype {x // p x}] [Fintype {x // ¬ p x}] :
    K.det * ((K⁻¹).submatrix (Subtype.val : {x // p x} → α) Subtype.val).det =
      (K.submatrix (Subtype.val : {x // ¬ p x} → α) Subtype.val).det := by
  let e := Equiv.sumCompl p
  set K' := K.submatrix e e with hK'
  set S' := K⁻¹.submatrix e e with hS'
  have hKS : K' * S' = 1 := by
    rw [hK', hS', Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hK,
      Matrix.submatrix_one_equiv]
  have hKe : K' = Matrix.fromBlocks K'.toBlocks₁₁ K'.toBlocks₁₂ K'.toBlocks₂₁ K'.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks K').symm
  have hSe : S' = Matrix.fromBlocks S'.toBlocks₁₁ S'.toBlocks₁₂ S'.toBlocks₂₁ S'.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks S').symm
  set E := K'.toBlocks₁₁
  set B := K'.toBlocks₁₂
  set C := K'.toBlocks₂₁
  set A := K'.toBlocks₂₂
  set P := S'.toBlocks₁₁
  set Q := S'.toBlocks₁₂
  set R := S'.toBlocks₂₁
  set T := S'.toBlocks₂₂
  have h1 : Matrix.fromBlocks (E * P + B * R) (E * Q + B * T) (C * P + A * R) (C * Q + A * T) =
      Matrix.fromBlocks 1 0 0 1 := by
    rw [← Matrix.fromBlocks_multiply, ← hKe, ← hSe, hKS, Matrix.fromBlocks_one]
  obtain ⟨e1, -, e3, -⟩ := Matrix.fromBlocks_inj.1 h1
  have h2 : K' * Matrix.fromBlocks P 0 R 1 = Matrix.fromBlocks 1 B 0 A := by
    rw [hKe, Matrix.fromBlocks_multiply]
    simp [e1, e3]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one, one_mul, Matrix.det_submatrix_equiv_self] at h3
  have h4 : A = K.submatrix (Subtype.val : {x // ¬ p x} → α) Subtype.val := by
    ext i j; simp [A, hK', Matrix.toBlocks₂₂, e]
  have h5 : P = K⁻¹.submatrix (Subtype.val : {x // p x} → α) Subtype.val := by
    ext i j; simp [P, hS', Matrix.toBlocks₁₁, e]
  rw [← h4, ← h5]
  exact h3

/-- **Determinant scale** (e): `det K_G = det K_Λ · det ((K_Λ⁻¹)_{DD})`. -/
theorem kw_jacobi {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m)) :
    (kwOpSub d m ν D).det = (latticeLaplacian d m ν).det *
      ((latticeLaplacian d m ν)⁻¹.submatrix (Subtype.val : {x // x ∈ D} → Torus d m)
        Subtype.val).det :=
  (det_mul_det_inv_block (latticeLaplacian d m ν)
    (latticeLaplacian_det_pos hν).ne'.isUnit (fun x => x ∈ D)).symm

/-! ### Non-vacuity: `d = 3`, `m = 3`, `ν = 1/8`, `D = {0}` -/

theorem one_le_torusDist_of_ne {x y : Torus d m} (h : x ≠ y) : 1 ≤ torusDist d m x y := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hsub : x i - y i ≠ 0 := sub_ne_zero.2 hi
  have hpos : 1 ≤ (cycRep (x i - y i)).natAbs := by
    by_contra hc
    have h0 : cycRep (x i - y i) = 0 := Int.natAbs_eq_zero.1 (by omega)
    apply hsub
    rw [← cast_cycRep (x i - y i), h0]; simp
  unfold torusDist
  calc (1 : ℝ) ≤ ((cycRep (x i - y i)).natAbs : ℝ) := by exact_mod_cast hpos
    _ ≤ _ := Finset.single_le_sum (f := fun j => ((cycRep (x j - y j)).natAbs : ℝ))
        (fun j _ => Nat.cast_nonneg _) (Finset.mem_univ i)

/-- The one-site hole in the torus `(ℤ/3ℤ)^3`. -/
def kwInstD : Finset (Torus 3 3) := {0}

/-- The good-region operator of the instance is invertible. -/
theorem kw_instance_isUnit : IsUnit (kwOp 3 3 (1 / 8 : ℝ) kwInstD).det :=
  (kwOp_det_pos (by norm_num) kwInstD).ne'.isUnit

/-- Inward decay in the instance: a unit source at the site `e₀` (a neighbour of the hole) is felt
at the other neighbour `e₁` with weight at most `8 · 48/49`. -/
theorem kw_instance_decay :
    |((kwOp 3 3 (1 / 8 : ℝ) kwInstD)⁻¹ *ᵥ (fun y => if y = Pi.single 0 1 then (1 : ℝ) else 0))
        (Pi.single 1 1)| ≤ 1 / (1 / 8 : ℝ) * kwQ 3 (1 / 8 : ℝ) ^ 1 := by
  refine kwOp_inv_mulVec_decay (by norm_num) kwInstD _ (B := 1) (fun y => ?_) _ 1 (fun y hy => ?_)
  · split_ifs <;> simp
  · have hy' : y = Pi.single 0 1 := by by_contra h; exact hy (by simp [h])
    subst hy'
    have hne : (Pi.single 1 1 : Torus 3 3) ≠ Pi.single 0 1 := by
      intro h
      have := congrFun h 0
      simp at this
    simpa using one_le_torusDist_of_ne hne

/-- The determinant walk formula in the instance. -/
theorem kw_instance_logdet :
    Real.log (latticeLaplacian 3 3 (1 / 8 : ℝ)).det - Real.log (kwOpSub 3 3 (1 / 8 : ℝ) kwInstD).det -
      (kwInstD.card : ℝ) * Real.log (2 * 3 + 1 / 8) = -∑' k, kwLoopTerm 3 3 (1 / 8 : ℝ) kwInstD k := by
  simpa using kw_logdet_eq (d := 3) (m := 3) (by norm_num : (0 : ℝ) < 1 / 8) kwInstD

/-! ### The value of the `k = 2` loop term: `tr A² - tr A_G² = 4d` for a one-site hole -/

/-- The `2d` unit steps `±e_μ`. -/
def kwDir (μ : Fin d) (b : Bool) : Torus d m :=
  if b then Pi.single μ 1 else -Pi.single μ 1

theorem kwAdj_eq_sum_dirs (x y : Torus d m) :
    kwAdj d m x y = ∑ j : Fin d × Bool, if y = x + kwDir j.1 j.2 then (1 : ℝ) else 0 := by
  rw [kwAdj_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e2 : (x = y + Pi.single μ 1) ↔ (y = x + -Pi.single μ 1) := by
    constructor
    · intro h; subst h; abel
    · intro h; subst h; abel
  rw [Fintype.sum_bool]
  simp [kwDir, e2]

omit [NeZero m] in
theorem kwDir_injective (h1 : (1 : ZMod m) ≠ 0) (h2 : (1 : ZMod m) ≠ -1) :
    Function.Injective (fun j : Fin d × Bool => (kwDir j.1 j.2 : Torus d m)) := by
  rintro ⟨μ, b⟩ ⟨ν, c⟩ h
  have hμ := congrFun h μ
  simp only [kwDir] at hμ
  by_cases hνμ : ν = μ
  · subst hνμ
    cases b <;> cases c <;> simp_all
  · exfalso
    cases b <;> cases c <;> simp_all [Ne.symm hνμ]

omit [NeZero m] in
theorem kwDir_ne_zero (h1 : (1 : ZMod m) ≠ 0) (μ : Fin d) (b : Bool) :
    (kwDir μ b : Torus d m) ≠ 0 := by
  intro h
  have := congrFun h μ
  cases b <;> simp_all [kwDir]

theorem kwAdj_diag (h1 : (1 : ZMod m) ≠ 0) (x : Torus d m) : kwAdj d m x x = 0 := by
  rw [kwAdj_eq_sum_dirs]
  refine Finset.sum_eq_zero fun j _ => ?_
  have := kwDir_ne_zero h1 (d := d) (m := m) j.1 j.2
  simp [this]

theorem kwAdj_sq_rowSum (h1 : (1 : ZMod m) ≠ 0) (h2 : (1 : ZMod m) ≠ -1) (z : Torus d m) :
    ∑ y, kwAdj d m z y ^ 2 = 2 * d := by
  have hinj := kwDir_injective (d := d) (m := m) h1 h2
  have e1 : ∀ y, kwAdj d m z y ^ 2 = ∑ j : Fin d × Bool, ∑ k : Fin d × Bool,
      (if y = z + kwDir j.1 j.2 then (1 : ℝ) else 0) * (if y = z + kwDir k.1 k.2 then 1 else 0) := by
    intro y
    rw [sq, kwAdj_eq_sum_dirs, Finset.sum_mul_sum]
  have e2 : ∀ a b : Torus d m, ∑ y : Torus d m, (if y = a then (1 : ℝ) else 0) *
      (if y = b then 1 else 0) = if a = b then 1 else 0 := by
    intro a b
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  simp_rw [e1]
  rw [Finset.sum_comm]
  have e3 : ∀ j : Fin d × Bool, ∑ y : Torus d m, ∑ k : Fin d × Bool,
      (if y = z + kwDir j.1 j.2 then (1 : ℝ) else 0) * (if y = z + kwDir k.1 k.2 then 1 else 0) =
      1 := by
    intro j
    rw [Finset.sum_comm]
    simp_rw [e2]
    have : ∀ k : Fin d × Bool, (z + kwDir j.1 j.2 = z + kwDir k.1 k.2) ↔ j = k := fun k => by
      rw [add_right_inj]
      exact (hinj.eq_iff (a := j) (b := k))
    simp_rw [this]
    simp
  simp_rw [e3]
  simp
  ring

/-- For a one-site hole the `k = 2` trace difference is `4d`: `2d` closed walks of length two
rooted at the hole and `2d` rooted at its neighbours. -/
theorem kwTraceDiff_two_single (h1 : (1 : ZMod m) ≠ 0) (h2 : (1 : ZMod m) ≠ -1) (z : Torus d m) :
    kwTraceDiff d m {z} 2 = 4 * d := by
  have hzz := kwAdj_diag h1 (d := d) z
  have hsq := kwAdj_sq_rowSum h1 h2 z
  have hpt : ∀ x y : Torus d m, kwAdj d m x y * kwAdj d m y x - kwAdjG d m {z} x y * kwAdjG d m {z} y x =
      (if x = z then kwAdj d m x y ^ 2 else 0) + (if y = z then kwAdj d m x y ^ 2 else 0) := by
    intro x y
    have hs : kwAdj d m y x = kwAdj d m x y := kwAdj_symm y x
    have hs' : kwAdjG d m {z} y x = kwAdjG d m {z} x y := kwAdjG_symm _ y x
    rw [hs, hs']
    by_cases hx : x = z <;> by_cases hy : y = z
    · subst hx; subst hy; simp [hzz, kwAdjG]
    · simp [kwAdjG, hx, hy, sq]
    · simp [kwAdjG, hx, hy, sq]
    · simp [kwAdjG, hx, hy]
  unfold kwTraceDiff
  simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp_rw [hpt]
  have hA : ∀ x : Torus d m, ∑ y, (if x = z then kwAdj d m x y ^ 2 else 0) =
      if x = z then ∑ y, kwAdj d m x y ^ 2 else 0 := by
    intro x; split_ifs <;> simp
  simp only [Finset.sum_add_distrib, hA, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have : ∑ x : Torus d m, kwAdj d m x z ^ 2 = 2 * d := by
    rw [← hsq]; exact Finset.sum_congr rfl fun x _ => by rw [kwAdj_symm x z]
  rw [hsq, this]; ring

theorem kwTraceDiff_one (h1 : (1 : ZMod m) ≠ 0) (D : Finset (Torus d m)) :
    kwTraceDiff d m D 1 = 0 := by
  have hz : ∀ x : Torus d m, kwAdjG d m D x x = 0 := fun x => by
    simp [kwAdjG, kwAdj_diag h1 x]
  simp [kwTraceDiff, Matrix.trace, Matrix.diag, kwAdj_diag h1, hz]

/-- In the instance the `k = 1` loop term vanishes and the `k = 2` term equals
`4d/(2 a²) = 6/(49/8)² = 384/2401`: the closed walks of length two through the hole. -/
theorem kw_instance_loop_two :
    kwTraceDiff 3 3 kwInstD 1 = 0 ∧ kwTraceDiff 3 3 kwInstD 2 = 12 ∧
      kwLoopTerm 3 3 (1 / 8 : ℝ) kwInstD 2 = 384 / 2401 := by
  have h1 : (1 : ZMod 3) ≠ 0 := by decide
  have h2 : (1 : ZMod 3) ≠ -1 := by decide
  have e2 : kwTraceDiff 3 3 kwInstD 2 = 12 := by
    have := kwTraceDiff_two_single h1 h2 (d := 3) (0 : Torus 3 3)
    rw [kwInstD]; rw [this]; norm_num
  refine ⟨kwTraceDiff_one h1 _, e2, ?_⟩
  unfold kwLoopTerm
  rw [e2]; norm_num

end Balaban
