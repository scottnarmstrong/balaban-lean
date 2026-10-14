/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalOpLogDet
public import Balaban.Green.FinalConnectedSupport

import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized log-determinant of the defect (W784, FINALPHYS leaf L3)

This construction is proposed in FINALFAM; the papers print no formula (Roland question 18
pending).  `K(s, t)` is the tagged defect of the macro cover, `1 - K(s, t)` is invertible on the
closed polydisc `‖s p‖ ≤ e^κ` (`FinalOpLogDet.lean`).

* `det_one_sub_eq_exp_tsum_trace`: if the row sums of `K` are at most `q < 1`, then
  `det (1 - K) = exp (-∑_{n ≥ 1} tr K^n / n)` with a convergent series (Jacobi's formula along the
  ray, no spectral theory).
* `eq_neg_tsum_trace_of_exp_eq`, `eq_neg_tsum_taggedK`: every continuous logarithm of `det (1 - K)`
  that vanishes at `0` is the trace series on the closed polydisc;
  `exists_series_log_det_taggedDefect` combines this with the analytic logarithm of
  `FinalOpLogDet.lean`.
* `coef_eq_of_agree_on_region`: the mixed coefficient of the logarithm at `C` depends only on the
  operator on `Y(C) × Y(C)`; no smallness is needed (it uses that `K(s)` at `s` supported on `C`
  has rows only in `Y(C)` and that the logarithm is unique on the convex set of such `s`).
* `taggedK_split_of_separated`, `coef_eq_zero_of_separated_taggedK`, `coef_eq_zero_final_of_separated`:
  the coefficient at a set `C` with two nonempty parts with disjoint box regions vanishes
  (`tr K^n` splits because the cross products vanish).
* `norm_coef_le_taggedK`, `norm_coef_le_final`: `‖coef ell C‖ ≤ |C| (8M+1)^d (q/(1-q)) / (e^κ-1)^|C|`,
  uniform in the torus (a box has at most `(8M+1)^d` points, `card_macBoxF_le`).
* `det_mul_det_boxResolvent_eq_prod_exp_coef`: `det (finalOp + t) · det (∑_z χ_z G_z)` is the
  product over cell sets `C` of `exp (coef ell C)`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace Balaban.Green

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_rowsum_pow_le (K : Matrix ι ι ℂ) {q : ℝ} (hK : ∀ x, ∑ y, ‖K x y‖ ≤ q) :
    ∀ m : ℕ, ∀ x, ∑ y, ‖(K ^ m) x y‖ ≤ q ^ m := by
  have hq : ∀ (h : Nonempty ι), 0 ≤ q := fun ⟨x⟩ => (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hK x)
  intro m
  induction m with
  | zero =>
    intro x
    have : ∀ y, ‖(1 : Matrix ι ι ℂ) x y‖ = if x = y then 1 else 0 := fun y => by
      by_cases h : x = y <;> simp [Matrix.one_apply, h]
    simp [this]
  | succ m ih =>
    intro x
    rw [pow_succ]
    calc ∑ y, ‖(K ^ m * K) x y‖ ≤ ∑ y, ∑ z, ‖(K ^ m) x z‖ * ‖K z y‖ := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [Matrix.mul_apply]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => norm_mul_le _ _)
      _ = ∑ z, ‖(K ^ m) x z‖ * ∑ y, ‖K z y‖ := by
          rw [Finset.sum_comm]; simp [Finset.mul_sum]
      _ ≤ ∑ z, ‖(K ^ m) x z‖ * q := Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hK z) (norm_nonneg _)
      _ = (∑ z, ‖(K ^ m) x z‖) * q := by rw [Finset.sum_mul]
      _ ≤ q ^ m * q := by
          have : 0 ≤ q := hq ⟨x⟩
          exact mul_le_mul_of_nonneg_right (ih x) this
      _ = q ^ (m + 1) := by ring

theorem norm_trace_pow_le_of_rowsum (K : Matrix ι ι ℂ) {q : ℝ} (hK : ∀ x, ∑ y, ‖K x y‖ ≤ q) (m : ℕ) :
    ‖(K ^ m).trace‖ ≤ Fintype.card ι * q ^ m := by
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖(K ^ m).diag x‖ ≤ ∑ _x : ι, q ^ m := Finset.sum_le_sum fun x _ => by
        refine le_trans ?_ (matrix_rowsum_pow_le K hK m x)
        exact Finset.single_le_sum (f := fun y => ‖(K ^ m) x y‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ x)
    _ = _ := by simp


section Normed

open scoped Matrix.Norms.Operator

theorem linfty_norm_le_of_rowsum (K : Matrix ι ι ℂ) {q : ℝ} (hq : 0 ≤ q) (hK : ∀ x, ∑ y, ‖K x y‖ ≤ q) :
    ‖K‖ ≤ q := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ.sup fun i : ι => ∑ j, ‖K i j‖₊) ≤ q.toNNReal :=
    Finset.sup_le fun i _ => by
      rw [← NNReal.coe_le_coe, NNReal.coe_sum, Real.coe_toNNReal q hq]
      simpa using hK i
  exact (NNReal.coe_le_coe.2 h).trans_eq (Real.coe_toNNReal q hq)

theorem det_one_sub_eq_exp_tsum_of_nonempty [Nonempty ι] (K : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hK : ∀ x, ∑ y, ‖K x y‖ ≤ q) :
    Summable (fun n : ℕ => (K ^ (n + 1)).trace / ((n : ℂ) + 1)) ∧
    (1 - K).det = Complex.exp (-∑' n : ℕ, (K ^ (n + 1)).trace / ((n : ℂ) + 1)) := by
  set ρ : ℝ := 2 / (1 + q) with hρ
  have h1q : 0 < 1 + q := by linarith
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ h1q]; linarith
  have hρq : ρ * q < 1 := by
    rw [hρ, div_mul_eq_mul_div, div_lt_one h1q]; linarith
  have hρ0 : 0 < ρ := by linarith
  set c : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hKn : ‖K‖ ≤ q := linfty_norm_le_of_rowsum K hq0 hK
  have hgeom : Summable (fun n : ℕ => c * q * (ρ * q) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hρq).mul_left _
  have htr := norm_trace_pow_le_of_rowsum K hK
  -- the series and its derivative
  let g : ℕ → ℂ → ℂ := fun n z => z ^ (n + 1) * ((K ^ (n + 1)).trace / ((n : ℂ) + 1))
  let g' : ℕ → ℂ → ℂ := fun n z => z ^ n * (K ^ (n + 1)).trace
  have hn1 : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => by exact_mod_cast Nat.succ_ne_zero n
  have hg : ∀ n z, HasDerivAt (g n) (g' n z) z := by
    intro n z
    have := (hasDerivAt_pow (n + 1) z).mul_const ((K ^ (n + 1)).trace / ((n : ℂ) + 1))
    convert this using 1
    simp only [g']
    push_cast
    field_simp [hn1 n]
  have hg'b : ∀ n, ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖g' n z‖ ≤ c * q * (ρ * q) ^ n := by
    intro n z hz
    have hz' : ‖z‖ ≤ ρ := (mem_ball_zero_iff.1 hz).le
    simp only [g', norm_mul, norm_pow]
    calc ‖z‖ ^ n * ‖(K ^ (n + 1)).trace‖ ≤ ρ ^ n * (c * q ^ (n + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz' _) (htr (n + 1)) (norm_nonneg _)
            (by positivity)
      _ = c * q * (ρ * q) ^ n := by ring
  have hS : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n z) z := fun z hz =>
    hasDerivAt_tsum_of_isPreconnected hgeom Metric.isOpen_ball
      (convex_ball (0 : ℂ) ρ).isPreconnected (fun n y _ => hg n y) hg'b
      (Metric.mem_ball_self hρ0) (by simp [g]) hz
  -- the matrix side
  obtain ⟨hKbound⟩ : Nonempty (∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖z • K‖ < 1) := by
    refine ⟨fun z hz => ?_⟩
    calc ‖z • K‖ ≤ ‖z‖ * ‖K‖ := norm_smul_le _ _
      _ ≤ ρ * q := mul_le_mul (mem_ball_zero_iff.1 hz).le hKn (norm_nonneg _) hρ0.le
      _ < 1 := hρq
  -- the resolvent
  have hres : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      HasSum (fun i => (z • K) ^ i) (∑' i, (z • K) ^ i) := fun z hz =>
    (summable_geometric_of_norm_lt_one (hKbound z hz)).hasSum
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap ι ℂ ℂ)
  have hLtr : ∀ A, L A = A.trace := fun A => rfl
  have hT : ∀ z ∈ Metric.ball (0 : ℂ) ρ,
      ∑' n, g' n z = ((∑' i, (z • K) ^ i) * K).trace := by
    intro z hz
    have h1 := L.hasSum ((hres z hz).mul_right K)
    refine (HasSum.tsum_eq ?_).trans (hLtr _)
    convert h1 using 1
    funext n
    simp only [g', hLtr, _root_.smul_pow, Matrix.smul_mul, Matrix.trace_smul, ← pow_succ, smul_eq_mul]
  -- the determinant
  have hdet : ∀ z ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt (fun μ : ℂ => (1 - μ • K).det)
      (-(1 - z • K).det * ∑' n, g' n z) z := by
    intro z hz
    set R : Matrix ι ι ℂ := ∑' i, (z • K) ^ i with hR
    have hR1 : (1 - z • K) * R = 1 := mul_neg_geom_series _ (hKbound z hz)
    set M : Matrix ι ι ℂ := -(R * K) with hM
    have hfac : ∀ μ : ℂ, 1 - μ • K = (1 - z • K) * (1 + (μ - z) • M) := by
      intro μ
      rw [hM, mul_add, mul_one, mul_smul_comm, mul_neg, ← mul_assoc, hR1, one_mul, smul_neg, sub_smul]
      abel
    have hP : HasDerivAt (fun h : ℂ => (1 + h • M).det) M.trace 0 := by
      have e : (fun h : ℂ => (1 + h • M).det) = fun h => 1 + M.trace * h +
          ((det (1 + (X : ℂ[X]) • M.map C)).divX.divX).eval h * h ^ 2 := by
        funext h; exact Matrix.det_one_add_smul h M
      rw [e]
      set Q := (det (1 + (X : ℂ[X]) • M.map C)).divX.divX
      have h1 := ((hasDerivAt_id (0 : ℂ)).const_mul M.trace).const_add 1
      have h2 := (Q.hasDerivAt 0).mul (hasDerivAt_pow 2 (0 : ℂ))
      convert h1.add h2 using 1
      · funext h; rfl
      · simp
    have hP' : HasDerivAt (fun μ : ℂ => (1 + (μ - z) • M).det) M.trace z := by
      have hid : HasDerivAt (fun μ : ℂ => μ - z) 1 z := (hasDerivAt_id z).sub_const z
      have hP0 : HasDerivAt (fun h : ℂ => (1 + h • M).det) M.trace (z - z) := by
        rwa [sub_self]
      simpa [Function.comp_def] using HasDerivAt.comp (h₂ := fun h : ℂ => (1 + h • M).det) (h := fun μ : ℂ => μ - z) z hP0 hid
    have := hP'.const_mul (1 - z • K).det
    have e : (fun μ : ℂ => (1 - μ • K).det) = fun μ => (1 - z • K).det * (1 + (μ - z) • M).det := by
      funext μ; rw [hfac μ, Matrix.det_mul]
    rw [e]
    convert this using 1
    rw [hT z hz, hM, Matrix.trace_neg, ← hR]
    ring
  -- the constant
  have hF : ∀ z ∈ Metric.ball (0 : ℂ) ρ, HasDerivAt
      (fun μ : ℂ => (1 - μ • K).det * Complex.exp (∑' n, g n μ)) 0 z := by
    intro z hz
    have := (hdet z hz).mul (hS z hz).cexp
    convert this using 1
    ring
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) ρ).isPreconnected
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hF z hz).deriv) (Metric.mem_ball_self hρ0)
    (show (1 : ℂ) ∈ Metric.ball (0 : ℂ) ρ by simpa using hρ1)
  have hsum : Summable (fun n : ℕ => (K ^ (n + 1)).trace / ((n : ℂ) + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left (c * q)) fun n => ?_
    rw [norm_div]
    have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; exact_mod_cast Nat.succ_pos n
    calc ‖(K ^ (n + 1)).trace‖ / ‖((n : ℂ) + 1)‖ ≤ ‖(K ^ (n + 1)).trace‖ :=
          div_le_self (norm_nonneg _) hn
      _ ≤ c * q ^ (n + 1) := htr (n + 1)
      _ = c * q * q ^ n := by ring
  refine ⟨hsum, ?_⟩
  simp only [one_smul, g, one_pow, one_mul, zero_smul, sub_zero, Matrix.det_one, zero_pow (Nat.succ_ne_zero _),
    zero_mul, tsum_zero, Complex.exp_zero, mul_one] at hconst
  rw [Complex.exp_neg]
  exact eq_inv_of_mul_eq_one_left hconst.symm

end Normed

theorem eq_of_exp_eq_of_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {x₀ : X} (hx₀ : x₀ ∈ S) {f g : X → ℂ} (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) (h0 : f x₀ = g x₀)
    (he : ∀ x ∈ S, Complex.exp (f x) = Complex.exp (g x)) : ∀ x ∈ S, f x = g x := by
  set φ : X → ℝ := fun y => (f y - g y).im / (2 * Real.pi) with hφ
  have hpi : 0 < 2 * Real.pi := by positivity
  have hint : ∀ y ∈ S, ∃ m : ℤ, φ y = m ∧ f y - g y = m * (2 * Real.pi * Complex.I) := by
    intro y hy
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (he y hy)
    have hm' : f y - g y = m * (2 * Real.pi * Complex.I) := by
      rw [hm]; ring
    refine ⟨m, ?_, hm'⟩
    simp only [hφ, hm']
    field_simp
    simp [Complex.mul_im]
    ring
  have hφc : ContinuousOn φ S := ((Complex.continuous_im.comp_continuousOn (hf.sub hg))).div_const _
  have hφ0 : φ x₀ = 0 := by simp [hφ, h0]
  intro x hx
  obtain ⟨n, hn, hn'⟩ := hint x hx
  have hn0 : n = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem : (-1 / 2 : ℝ) ∈ Set.Icc (φ x) (φ x₀) := by
        rw [hn, hφ0]
        have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        constructor <;> linarith
      obtain ⟨y, hy, hy'⟩ := hS.intermediate_value hx hx₀ hφc hmem
      obtain ⟨m, hm, -⟩ := hint y hy
      have h2 : (2 * m : ℝ) = -1 := by rw [← hm, hy']; norm_num
      have : (2 * m : ℤ) = -1 := by exact_mod_cast h2
      omega
    · have hmem : (1 / 2 : ℝ) ∈ Set.Icc (φ x₀) (φ x) := by
        rw [hn, hφ0]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hgt
        constructor <;> linarith
      obtain ⟨y, hy, hy'⟩ := hS.intermediate_value hx₀ hx hφc hmem
      obtain ⟨m, hm, -⟩ := hint y hy
      have h2 : (2 * m : ℝ) = 1 := by rw [← hm, hy']; norm_num
      have : (2 * m : ℤ) = 1 := by exact_mod_cast h2
      omega
  rw [hn0] at hn'
  simpa [sub_eq_zero] using hn'


/-- **The determinant as the exponential of the trace series.**  If the row sums of `K` are at most
`q < 1`, then `∑_n tr(K^{n+1})/(n+1)` converges and
`det (1 - K) = exp (-∑_{n ≥ 1} tr(K^n)/n)`. -/
theorem det_one_sub_eq_exp_tsum_trace (K : Matrix ι ι ℂ) {q : ℝ} (hq1 : q < 1)
    (hK : ∀ x, ∑ y, ‖K x y‖ ≤ q) :
    Summable (fun n : ℕ => (K ^ (n + 1)).trace / ((n : ℂ) + 1)) ∧
    (1 - K).det = Complex.exp (-∑' n : ℕ, (K ^ (n + 1)).trace / ((n : ℂ) + 1)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨?_, ?_⟩
    · simp [Matrix.trace]
    · simp [Matrix.trace]
  · obtain ⟨x⟩ := hι
    have : Nonempty ι := ⟨x⟩
    exact det_one_sub_eq_exp_tsum_of_nonempty K
      ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hK x)) hq1 hK

/-- If the rows of `K` outside `S` vanish and its row sums are at most `q`, then
`‖tr (K^m)‖ ≤ |S| q^m` for `m ≥ 1`. -/
theorem norm_trace_pow_le_of_rows_zero (K : Matrix ι ι ℂ) {q : ℝ} (hK : ∀ x, ∑ y, ‖K x y‖ ≤ q)
    (S : Finset ι) (hS : ∀ x ∉ S, ∀ y, K x y = 0) {m : ℕ} (hm : 1 ≤ m) :
    ‖(K ^ m).trace‖ ≤ S.card * q ^ m := by
  classical
  have hdiag : ∀ x ∉ S, (K ^ m) x x = 0 := by
    intro x hx
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_eq_zero fun z _ => by rw [hS x hx z, zero_mul]
  unfold Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖(K ^ m).diag x‖ ≤ ∑ x : ι, if x ∈ S then q ^ m else 0 :=
        Finset.sum_le_sum fun x _ => by
          by_cases hx : x ∈ S
          · simp only [hx, ite_true]
            refine le_trans ?_ (matrix_rowsum_pow_le K hK m x)
            exact Finset.single_le_sum (f := fun y => ‖(K ^ m) x y‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ x)
          · simp only [hx, ite_false]
            simp [Matrix.diag, hdiag x hx]
    _ = S.card * q ^ m := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        simp

/-- **The trace series is the branch of the logarithm.**  Let `K` be a continuous matrix family on a
preconnected set `S` with `K x₀ = 0` and row sums at most `q < 1` on `S`.  A function `ell`,
continuous on `S`, with `ell x₀ = 0` and `det (1 - K x) = exp (ell x)` on `S`, equals
`-∑_{n ≥ 1} tr (K x)^n / n` on `S`. -/
theorem eq_neg_tsum_trace_of_exp_eq {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {x₀ : X} (hx₀ : x₀ ∈ S) (K : X → Matrix ι ι ℂ) (hKc : Continuous K)
    (hK0 : K x₀ = 0) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hK : ∀ x ∈ S, ∀ i, ∑ j, ‖K x i j‖ ≤ q) {ell : X → ℂ} (hell : ContinuousOn ell S)
    (h0 : ell x₀ = 0) (hdet : ∀ x ∈ S, (1 - K x).det = Complex.exp (ell x)) :
    ∀ x ∈ S, ell x = -∑' n : ℕ, ((K x) ^ (n + 1)).trace / ((n : ℂ) + 1) := by
  set c : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hc
  have hterm : ∀ n : ℕ, Continuous fun x => ((K x) ^ (n + 1)).trace / ((n : ℂ) + 1) := fun n =>
    ((hKc.pow (n + 1)).matrix_trace).div_const _
  have hbd : ∀ n : ℕ, ∀ x ∈ S, ‖((K x) ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤ c * q * q ^ n := by
    intro n x hx
    rw [norm_div]
    have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; exact_mod_cast Nat.succ_pos n
    calc ‖((K x) ^ (n + 1)).trace‖ / ‖((n : ℂ) + 1)‖ ≤ ‖((K x) ^ (n + 1)).trace‖ :=
          div_le_self (norm_nonneg _) hn
      _ ≤ c * q ^ (n + 1) := norm_trace_pow_le_of_rowsum (K x) (hK x hx) (n + 1)
      _ = c * q * q ^ n := by ring
  have hcont : ContinuousOn (fun x => -∑' n : ℕ, ((K x) ^ (n + 1)).trace / ((n : ℂ) + 1)) S :=
    (continuousOn_tsum (fun n => (hterm n).continuousOn)
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (c * q)) hbd).neg
  have hzero : -∑' n : ℕ, ((K x₀) ^ (n + 1)).trace / ((n : ℂ) + 1) = 0 := by
    simp [hK0]
  intro x hx
  refine eq_of_exp_eq_of_continuousOn hS hx₀ hell hcont (by rw [h0, hzero]) (fun y hy => ?_) x hx
  rw [← hdet y hy, (det_one_sub_eq_exp_tsum_trace (K y) hq1 (hK y hy)).2]

theorem add_pow_succ_of_mul_eq_zero {A : Type*} [Ring A] {a b : A} (hab : a * b = 0)
    (hba : b * a = 0) (n : ℕ) : (a + b) ^ (n + 1) = a ^ (n + 1) + b ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, pow_succ a (n + 1), pow_succ b (n + 1)]
    have h1 : a ^ (n + 1) * b = 0 := by rw [pow_succ, mul_assoc, hab, mul_zero]
    have h2 : b ^ (n + 1) * a = 0 := by rw [pow_succ, mul_assoc, hba, mul_zero]
    rw [h1, h2]
    abel

end Generic

section Macro

open Balaban.Localization Balaban.Analysis

variable {d N₀ M : ℕ} [NeZero N₀]

local notation "𝐊[" U ", " t ", " s "]" =>
  taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
    (macTags d N₀ M) U t s

theorem polydisc_eq_ball {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R) :
    polydisc (0 : ι → ℂ) (fun _ => R) = Metric.ball (0 : ι → ℂ) R := by
  ext z
  simp only [polydisc, Set.mem_ofPred_eq, mem_ball_zero_iff, Pi.zero_apply, sub_zero]
  exact (pi_norm_lt_iff hR).symm

theorem convex_supportedOn {ι : Type*} (C : Finset ι) : Convex ℝ (supportedOn C : Set (ι → ℂ)) := by
  intro x hx y hy a b _ _ _ i hi
  simp [hx i hi, hy i hi]

/-- The tagged defect vanishes at `s = 0`, for every matrix. -/
theorem taggedK_zero_of_matrix (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) :
    𝐊[U, t, (0 : MacIdx d N₀ M → ℂ)] = 0 := by
  ext x y
  simp [taggedK, taggedMat, tagMon_macTags_zero hM hd]

theorem continuous_taggedK (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) :
    Continuous fun s : MacIdx d N₀ M → ℂ => 𝐊[U, t, s] :=
  continuous_matrix fun x y => continuous_iff_continuousAt.2 fun s0 =>
    (taggedMat_analytic _ _ _ x y s0).continuousAt

/-- At a parameter supported on `C`, the rows of the tagged defect outside `Y(C)` vanish. -/
theorem taggedK_row_eq_zero_of_not_mem_region (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {C : Finset (MacIdx d N₀ M)}
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ supportedOn C) {x : L1Torus d N₀}
    (hx : x ∉ macRegion d N₀ M C) (y : L1Torus d N₀) : 𝐊[U, t, s] x y = 0 := by
  unfold taggedK
  rw [taggedMat_apply_of_supportedOn _ _ _ hs]
  exact Finset.sum_eq_zero fun z hz =>
    absurd (macTags_cover_box_and_ends hM hd (Finset.mem_filter.1 hz).2).2.1 hx

/-- A box of the macro cover has at most `(8M + 1)^d` points, independently of the torus. -/
theorem card_macBoxF_le (hM : 0 < M) (z : MacIdx d N₀ M) :
    (macBoxF d N₀ M z).card ≤ (8 * M + 1) ^ d := by
  classical
  obtain ⟨y0, hy0⟩ := macCore_nonempty (d := d) (m := N₀) (M := M) z
  have hsub : macBoxF d N₀ M z ⊆ Fintype.piFinset (fun i : Fin d =>
      Finset.univ.filter fun v : ZMod N₀ => (cycRep (y0 i - v)).natAbs ≤ 4 * M) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff (macCore_nonempty (d := d) (m := N₀) (M := M) z)).1
      (mem_macBoxF.1 hx)
    refine Fintype.mem_piFinset.2 fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hMm : M ≤ N₀
    · have h1 : (cycRep (y i - x i)).natAbs < 2 * M := by
        have := (dist_coord_le y x i).trans_lt (by rwa [dist_comm] at hxy)
        exact_mod_cast this
      have h2 : (cycRep (y0 i - y i)).natAbs < 2 * M :=
        macCell_dist_lt hM hMm ((hy0 i).trans (hy i).symm)
      have h3 := natAbs_cycRep_add_le (y0 i - y i) (y i - x i)
      rw [sub_add_sub_cancel] at h3
      omega
    · have h1 := natAbs_cycRep_sub_le (y0 i) (x i)
      have h2 := ZMod.val_lt (y0 i)
      have h3 := ZMod.val_lt (x i)
      omega
  calc (macBoxF d N₀ M z).card ≤ _ := Finset.card_le_card hsub
    _ = ∏ i : Fin d, (Finset.univ.filter fun v : ZMod N₀ =>
        (cycRep (y0 i - v)).natAbs ≤ 4 * M).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (8 * M + 1) := Finset.prod_le_prod fun i _ =>
        (card_cyc_ball_le (y0 i) (4 * M)).trans (by omega)
    _ = (8 * M + 1) ^ d := by simp

/-- The union of the boxes of the cells of `C` has at most `|C| (8M + 1)^d` points. -/
theorem card_biUnion_macBoxF_le (hM : 0 < M) (C : Finset (MacIdx d N₀ M)) :
    (C.biUnion (macBoxF d N₀ M)).card ≤ C.card * (8 * M + 1) ^ d := by
  calc _ ≤ ∑ p ∈ C, (macBoxF d N₀ M p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ C, (8 * M + 1) ^ d := Finset.sum_le_sum fun p _ => card_macBoxF_le hM p
    _ = C.card * (8 * M + 1) ^ d := by simp

theorem mem_biUnion_macBoxF {C : Finset (MacIdx d N₀ M)} {x : L1Torus d N₀} :
    x ∈ C.biUnion (macBoxF d N₀ M) ↔ x ∈ macRegion d N₀ M C := by
  classical
  simp only [Finset.mem_biUnion, mem_macBoxF, mem_macRegion]

/-- **Locality of the log-determinant in the operator.**  Let `ell` and `ell'` be continuous
logarithms of `det (1 - K(s, t))` for two matrices `U`, `U'` on the polydisc of radius `R > 1`
(`ell 0 = ell' 0 = 0`).  If `U` and `U'` agree on `Y(C) × Y(C)`, then `ell` and `ell'` have the same
mixed coefficient at `C`. -/
theorem coef_eq_of_agree_on_region (hM : 0 < M) (hd : 0 < d) {R : ℝ} (hR : 1 < R)
    {U U' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (t : ℝ) {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    {ell ell' : (MacIdx d N₀ M → ℂ) → ℂ} (hell : ContinuousOn ell (Metric.ball 0 R))
    (hell' : ContinuousOn ell' (Metric.ball 0 R)) (h0 : ell 0 = 0) (h0' : ell' 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) R,
      (1 - 𝐊[U, t, s]).det = Complex.exp (ell s))
    (hdet' : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) R,
      (1 - 𝐊[U', t, s]).det = Complex.exp (ell' s)) :
    coef ell C = coef ell' C := by
  classical
  have hR0 : 0 < R := by linarith
  set S : Set (MacIdx d N₀ M → ℂ) := Metric.ball 0 R ∩ supportedOn C with hSdef
  have hSconv : Convex ℝ S := (convex_ball _ _).inter (convex_supportedOn C)
  have h0S : (0 : MacIdx d N₀ M → ℂ) ∈ S := ⟨Metric.mem_ball_self hR0, fun i _ => rfl⟩
  have heq : ∀ s ∈ S, ell s = ell' s := by
    refine eq_of_exp_eq_of_continuousOn hSconv.isPreconnected h0S (hell.mono Set.inter_subset_left)
      (hell'.mono Set.inter_subset_left) (by rw [h0, h0']) fun s hs => ?_
    rw [← hdet s hs.1, ← hdet' s hs.1,
      (taggedGfin_congr_of_agree_on_region hM hd Finset.univ hU hs.2).2.1]
  have hproj : ∀ f : (MacIdx d N₀ M → ℂ) → ℂ, coef f C =
      coef (fun s => f (fun i => if i ∈ C then s i else 0)) C := fun f =>
    coef_congr fun w hw => by
      congr 1; funext i; by_cases hi : i ∈ C
      · simp [hi]
      · simp [hi, hw i hi]
  rw [hproj ell, hproj ell']
  refine coef_congr_polydisc hR (fun s hs => heq _ ⟨?_, fun i hi => by simp [hi]⟩) C
  rw [← polydisc_eq_ball hR0]
  intro i
  by_cases hi : i ∈ C
  · simpa [hi] using hs i
  · simpa [hi] using hR0

/-- **The log-determinant is the trace series on the closed polydisc.**  If the row sums of the
tagged defect `K(s, t)` of `U` are at most `q < 1` on the closed polydisc `‖s p‖ ≤ e^κ`, then every
continuous logarithm `ell` of `det (1 - K(s, t))` with `ell 0 = 0` equals
`-∑_{n ≥ 1} tr K(s, t)^n / n` there. -/
theorem eq_neg_tsum_taggedK (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {κ q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x,
      ∑ y, ‖𝐊[U, t, s] x y‖ ≤ q)
    {ell : (MacIdx d N₀ M → ℂ) → ℂ} (hell : ContinuousOn ell (Metric.closedBall 0 (Real.exp κ)))
    (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ),
      (1 - 𝐊[U, t, s]).det = Complex.exp (ell s)) :
    ∀ s ∈ Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ),
      ell s = -∑' n : ℕ, ((𝐊[U, t, s]) ^ (n + 1)).trace / ((n : ℂ) + 1) := by
  have hκ : (0 : ℝ) < Real.exp κ := Real.exp_pos κ
  exact eq_neg_tsum_trace_of_exp_eq (convex_closedBall _ _).isPreconnected
    (Metric.mem_closedBall_self hκ.le) (fun s => 𝐊[U, t, s]) (continuous_taggedK U t)
    (taggedK_zero_of_matrix hM hd U t) hq0 hq1
    (fun s hs i => hKU s (fun p => (norm_le_pi_norm s p).trans (mem_closedBall_zero_iff.1 hs)) i)
    hell h0 hdet

/-- **The tagged defect splits over a separated decomposition of the support.**  Let
`C = A ⊔ (C \ A)` with the boxes of `A` disjoint from the boxes of `C \ A`, and `s` supported on
`C`.  Then `K(s) = K(s|_A) + K(s|_{C \ A})` and the two summands multiply to zero in both orders. -/
theorem taggedK_split_of_separated (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {C A : Finset (MacIdx d N₀ M)}
    (hAC : A ⊆ C) (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)))
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ supportedOn C) :
    𝐊[U, t, s] = 𝐊[U, t, fun i => if i ∈ A then s i else 0] +
        𝐊[U, t, fun i => if i ∈ C \ A then s i else 0] ∧
      𝐊[U, t, fun i => if i ∈ A then s i else 0] *
        𝐊[U, t, fun i => if i ∈ C \ A then s i else 0] = 0 ∧
      𝐊[U, t, fun i => if i ∈ C \ A then s i else 0] *
        𝐊[U, t, fun i => if i ∈ A then s i else 0] = 0 := by
  classical
  set c : MacIdx d N₀ M → L1Torus d N₀ → ℂ := fun z u => ((macChi d N₀ M z u : ℝ) : ℂ) with hc
  set B : Finset (MacIdx d N₀ M) := C \ A with hBdef
  have hAB : Disjoint A B := Finset.disjoint_sdiff
  have hBC : B ⊆ C := Finset.sdiff_subset
  have hBA : Disjoint B A := hAB.symm
  have hsep' : ∀ a ∈ A, ∀ b ∈ B, ∀ p, p ∈ macBox d N₀ M a → p ∈ macBox d N₀ M b → False :=
    fun a ha b hb p h1 h2 => Set.disjoint_left.1 hsep (mem_macRegion.2 ⟨a, ha, h1⟩)
      (mem_macRegion.2 ⟨b, hb, h2⟩)
  have hCAB : C ⊆ A ∪ B := by
    intro i hi
    by_cases hiA : i ∈ A
    · exact Finset.mem_union_left _ hiA
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hi, hiA⟩)
  have hcB : ∀ z w, c z w ≠ 0 → w ∈ macBoxF d N₀ M z := fun z w h =>
    macChi_ne_zero_mem_macBoxF hM h
  have hKy : ∀ z x y, boxR U (macBoxF d N₀ M z) (c z) t x y ≠ 0 → y ∈ macBox d N₀ M z :=
    fun z x y h => mem_macBoxF.1 (mem_of_boxR_ne_zero (hcB z) h)
  have hsplitTags : ∀ z x y, y ∈ macBox d N₀ M z → (macTags d N₀ M z x y).Nonempty ∧
      (macTags d N₀ M z x y ⊆ A ∨ macTags d N₀ M z x y ⊆ B ∨ ¬ macTags d N₀ M z x y ⊆ C) :=
    fun z x y hy => ⟨⟨_, macZ_end_mem_macTags hM hd z x y⟩, by
      by_cases hVC : macTags d N₀ M z x y ⊆ C
      · rcases macTags_subset_or hM hd hy hsep' (hVC.trans hCAB) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hVC)⟩
  have hend : ∀ z x y, macZ M y ∈ macTags d N₀ M z x y := fun z x y =>
    macZ_end_mem_macTags hM hd z x y
  have hstart : ∀ z x y, macZ M x ∈ macTags d N₀ M z x y := fun z x y =>
    macZ_start_mem_macTags hM hd z x y
  refine ⟨?_, ?_, ?_⟩
  · exact taggedMat_split _ _ _ hAB hAC hBC hs (fun _ => rfl) (fun _ => rfl)
      fun z _ x y h => hsplitTags z x y (hKy z x y h)
  · exact taggedMat_mul_eq_zero _ _ _ _ hAB (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)
  · exact taggedMat_mul_eq_zero _ _ _ _ hBA (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)

/-- **Vanishing of the log-determinant coefficient at a separated support.**  Let the row sums of
the tagged defect be at most `q < 1` on the closed polydisc `‖s p‖ ≤ e^κ`, `κ > 0`, and let `ell`
be analytic on the polydisc of radius `ρ' > e^κ` with `ell 0 = 0` and
`det (1 - K(s, t)) = exp (ell s)` there.  If `C = A ⊔ (C \ A)` with both parts nonempty and the
boxes of `A` disjoint from the boxes of `C \ A`, then the coefficient of `ell` at `C` vanishes. -/
theorem coef_eq_zero_of_separated_taggedK (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {κ q : ℝ} (hκ : 0 < κ) (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x,
      ∑ y, ‖𝐊[U, t, s] x y‖ ≤ q)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
      (1 - 𝐊[U, t, s]).det = Complex.exp (ell s))
    {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty) (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef ell C = 0 := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  have hcb : Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
    Metric.closedBall_subset_ball hρ'
  have hser := eq_neg_tsum_taggedK hM hd U t hq0 hq1 hKU (hell.continuousOn.mono hcb) h0
    (fun s hs => hdet s (hcb hs))
  have hbd : ∀ s : MacIdx d N₀ M → ℂ, ‖s‖ ≤ Real.exp κ → ∀ p, ‖s p‖ ≤ Real.exp κ :=
    fun s hs p => (norm_le_pi_norm s p).trans hs
  have hproj : ∀ (X : Finset (MacIdx d N₀ M)) (s : MacIdx d N₀ M → ℂ), ‖s‖ ≤ Real.exp κ →
      ‖(fun i => if i ∈ X then s i else 0 : MacIdx d N₀ M → ℂ)‖ ≤ Real.exp κ := by
    intro X s hs
    refine (pi_norm_le_iff_of_nonneg hR0.le).2 fun p => ?_
    by_cases hp : p ∈ X
    · simpa [hp] using (norm_le_pi_norm s p).trans hs
    · simpa [hp] using hR0.le
  refine coef_eq_zero_of_split hR (hell.mono ?_) Finset.disjoint_sdiff hAC Finset.sdiff_subset hA hB
    (fun s hs hsC => ?_)
  · intro s hs
    rw [polydisc_eq_ball hR0] at hs
    exact Metric.ball_subset_ball hρ'.le hs
  · rw [polydisc_eq_ball hR0] at hs
    have hs1 : ‖s‖ ≤ Real.exp κ := (mem_ball_zero_iff.1 hs).le
    obtain ⟨hK, h1, h2⟩ := taggedK_split_of_separated hM hd U t hAC hsep hsC
    have hsA := hproj A s hs1
    have hsB := hproj (C \ A) s hs1
    have hsum := fun (r : MacIdx d N₀ M → ℂ) (hr : ‖r‖ ≤ Real.exp κ) =>
      det_one_sub_eq_exp_tsum_trace (𝐊[U, t, r]) hq1 (hKU r (hbd r hr))
    rw [hser s (mem_closedBall_zero_iff.2 hs1), hser _ (mem_closedBall_zero_iff.2 hsA),
      hser _ (mem_closedBall_zero_iff.2 hsB), ← neg_add, hK]
    congr 1
    rw [← (hsum _ hsA).1.tsum_add (hsum _ hsB).1]
    refine tsum_congr fun n => ?_
    rw [add_pow_succ_of_mul_eq_zero h1 h2, Matrix.trace_add, add_div]

/-- **Volume-uniform bound of the coefficients of the log-determinant.**  Under the hypotheses of
`coef_eq_zero_of_separated_taggedK` (without the decomposition),
`‖coef ell C‖ ≤ |C| (8M + 1)^d (q / (1 - q)) / (e^κ - 1)^{|C|}`.  The constant does not depend on
the torus: only the cells of `C` and the box size `(8M + 1)^d` enter. -/
theorem norm_coef_le_taggedK (hM : 0 < M) (hd : 0 < d)
    (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) {κ q : ℝ} (hκ : 0 < κ) (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x,
      ∑ y, ‖𝐊[U, t, s] x y‖ ≤ q)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
      (1 - 𝐊[U, t, s]).det = Complex.exp (ell s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ell C‖ ≤ (C.card * ((8 * M + 1) ^ d * (q / (1 - q)))) /
      (Real.exp κ - 1) ^ C.card := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  have hcb : Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
    Metric.closedBall_subset_ball hρ'
  have hser := eq_neg_tsum_taggedK hM hd U t hq0 hq1 hKU (hell.continuousOn.mono hcb) h0
    (fun s hs => hdet s (hcb hs))
  have hpoly : polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ) ⊆ Metric.ball 0 ρ' := by
    intro s hs
    rw [polydisc_eq_ball hR0] at hs
    exact Metric.ball_subset_ball hρ'.le hs
  have hproj : coef ell C = coef (fun s => ell (fun i => if i ∈ C then s i else 0)) C :=
    coef_congr fun w hw => by
      congr 1; funext i; by_cases hi : i ∈ C
      · simp [hi]
      · simp [hi, hw i hi]
  rw [hproj]
  set Y : Finset (L1Torus d N₀) := C.biUnion (macBoxF d N₀ M) with hY
  have hYc : (Y.card : ℝ) ≤ C.card * (8 * M + 1) ^ d := by exact_mod_cast card_biUnion_macBoxF_le hM C
  set B : ℝ := C.card * ((8 * M + 1) ^ d * (q / (1 - q))) with hB
  have hq' : 0 ≤ q / (1 - q) := div_nonneg hq0 (by linarith)
  refine norm_coef_le hR (analyticOnNhd_comp_proj (hell.mono hpoly) C hR0) (B := B) ?_ C
  intro s hs
  rw [polydisc_eq_ball hR0] at hs
  have hs1 : ‖s‖ ≤ Real.exp κ := (mem_ball_zero_iff.1 hs).le
  have hsC : ‖(fun i => if i ∈ C then s i else 0 : MacIdx d N₀ M → ℂ)‖ ≤ Real.exp κ := by
    refine (pi_norm_le_iff_of_nonneg hR0.le).2 fun p => ?_
    by_cases hp : p ∈ C
    · simpa [hp] using (norm_le_pi_norm s p).trans hs1
    · simpa [hp] using hR0.le
  set sC : MacIdx d N₀ M → ℂ := fun i => if i ∈ C then s i else 0 with hsCdef
  have hsupp : sC ∈ supportedOn C := fun i hi => by simp [hsCdef, hi]
  rw [hser sC (mem_closedBall_zero_iff.2 hsC), norm_neg]
  have hterm : ∀ n : ℕ, ‖((𝐊[U, t, sC]) ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤
      Y.card * q * q ^ n := by
    intro n
    rw [norm_div]
    have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; exact_mod_cast Nat.succ_pos n
    calc ‖((𝐊[U, t, sC]) ^ (n + 1)).trace‖ / ‖((n : ℂ) + 1)‖ ≤
          ‖((𝐊[U, t, sC]) ^ (n + 1)).trace‖ := div_le_self (norm_nonneg _) hn
      _ ≤ Y.card * q ^ (n + 1) := norm_trace_pow_le_of_rows_zero _
          (hKU sC (fun p => (norm_le_pi_norm sC p).trans hsC))
          Y (fun x hx y => taggedK_row_eq_zero_of_not_mem_region hM hd U t hsupp
            (fun h => hx (mem_biUnion_macBoxF.2 h)) y) (Nat.succ_pos n)
      _ = Y.card * q * q ^ n := by ring
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Y.card * q)
  calc ‖∑' n : ℕ, ((𝐊[U, t, sC]) ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤
        Y.card * q * (1 - q)⁻¹ := tsum_of_norm_bounded hgeo hterm
    _ = Y.card * (q / (1 - q)) := by rw [div_eq_mul_inv]; ring
    _ ≤ B := by
        rw [hB]
        calc (Y.card : ℝ) * (q / (1 - q)) ≤ (C.card * (8 * M + 1) ^ d) * (q / (1 - q)) :=
              mul_le_mul_of_nonneg_right hYc hq'
          _ = _ := by ring

end Macro

section Final

open Balaban.Localization Balaban.Analysis

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

local notation "𝐊[" U ", " t ", " s "]" =>
  taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
    (macTags d N₀ M) U t s

/-- The row sums of the tagged defect of the final operator are at most `1/4` on the closed
polydisc `‖s p‖ ≤ e^κ`. -/
theorem taggedK_rowsum_le_quarter (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, ‖taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
      (macTags d N₀ M) (finalOp d L N₀ k v a) t s x y‖ ≤ 1 / 4 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have h := taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ le_rfl
    (div_nonneg (pdEps_pos hd).le (by norm_num)) hκM hs x
  simpa using h.trans hq

/-- **The localized log-determinant of the defect as a trace series.**  Under the hypotheses of
`exists_analytic_log_det_taggedDefect` there are `ρ' > e^κ` and `ell`, analytic on the polydisc
`‖s p‖ < ρ'`, with `det (1 - K(s, t)) = exp (ell s)` there, `ell 0 = 0`, `exp (ell 1)` equal to the
product `det (finalOp + t) · det (∑_z χ_z G_z)`, and, on the closed polydisc `‖s p‖ ≤ e^κ`,
`ell s = -∑_{n ≥ 1} tr K(s, t)^n / n` with the series convergent. -/
theorem exists_series_log_det_taggedDefect (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) :
    ∃ ρ' : ℝ, Real.exp κ < ρ' ∧ ∃ ell : (MacIdx d N₀ M → ℂ) → ℂ,
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ') ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s).det = Complex.exp (ell s)) ∧
      ell 0 = 0 ∧
      Complex.exp (ell (fun _ => 1)) = (shiftMat (finalOp d L N₀ k v a) t).det *
        (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det ∧
      ∀ s ∈ Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ),
        Summable (fun n : ℕ => ((taggedK Finset.univ (macBoxF d N₀ M)
          (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t s)
            ^ (n + 1)).trace / ((n : ℂ) + 1)) ∧
        ell s = -∑' n : ℕ, ((taggedK Finset.univ (macBoxF d N₀ M)
          (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) (finalOp d L N₀ k v a) t s)
            ^ (n + 1)).trace / ((n : ℂ) + 1) := by
  obtain ⟨ρ', hρ', ell, h1, h2, h3, h4⟩ := exists_analytic_log_det_taggedDefect (N₀ := N₀) hd hk
    hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ
  have hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x,
      ∑ y, ‖𝐊[finalOp d L N₀ k v a, t, s] x y‖ ≤ 1 / 4 := fun s hs x =>
    taggedK_rowsum_le_quarter hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ hs x
  have hcb : Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
    Metric.closedBall_subset_ball hρ'
  have hser := eq_neg_tsum_taggedK hM hd (finalOp d L N₀ k v a) t (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hKU (h1.continuousOn.mono hcb) h3
    (fun s hs => h2 s (hcb hs))
  refine ⟨ρ', hρ', ell, h1, h2, h3, h4, fun s hs => ⟨?_, hser s hs⟩⟩
  exact (det_one_sub_eq_exp_tsum_trace (𝐊[finalOp d L N₀ k v a, t, s]) (by norm_num : (1 / 4 : ℝ) < 1)
    (hKU s fun p => (norm_le_pi_norm s p).trans (mem_closedBall_zero_iff.1 hs))).1

/-- **Volume-uniform coefficient bound for the final operator.**  For `ell` as in
`exists_series_log_det_taggedDefect` (with `κ > 0`),
`‖coef ell C‖ ≤ |C| (8M + 1)^d (1/3) / (e^κ - 1)^{|C|}`; the constant does not depend on `N₀`. -/
theorem norm_coef_le_final (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
      (1 - 𝐊[finalOp d L N₀ k v a, t, s]).det = Complex.exp (ell s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ell C‖ ≤ (C.card * ((8 * M + 1) ^ d * (1 / 3))) / (Real.exp κ - 1) ^ C.card := by
  have h := norm_coef_le_taggedK hM hd (finalOp d L N₀ k v a) t hκ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) (fun s hs x => taggedK_rowsum_le_quarter hd hk hv0 hv1 ha1 ha2
      hmass ht hM hκ.le hMB hMκ hs x) hρ' hell h0 hdet C
  have e : (1 / 4 : ℝ) / (1 - 1 / 4) = 1 / 3 := by norm_num
  rwa [e] at h

/-- **Connected supports for the final operator.**  For `ell` as in
`exists_series_log_det_taggedDefect` (with `κ > 0`), the coefficient at `C` vanishes when
`C = A ⊔ (C \ A)` with both parts nonempty and the boxes of `A` disjoint from those of `C \ A`. -/
theorem coef_eq_zero_final_of_separated (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
      (1 - 𝐊[finalOp d L N₀ k v a, t, s]).det = Complex.exp (ell s))
    {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty) (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef ell C = 0 :=
  coef_eq_zero_of_separated_taggedK hM hd (finalOp d L N₀ k v a) t hκ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) (fun s hs x => taggedK_rowsum_le_quarter hd hk hv0 hv1 ha1 ha2
      hmass ht hM hκ.le hMB hMκ hs x) hρ' hell h0 hdet hAC hA hB hsep

/-- **The interpolated determinant as a product over cell sets.**  For `ell` as in
`exists_series_log_det_taggedDefect` (with `κ > 0`),
`det (finalOp + t) · det (∑_z χ_z G_z) = ∏_C exp (coef ell C)`, the product over all sets `C` of
cells; the factors with `C` not connected equal `1`
(`coef_eq_zero_final_of_separated`), and each remaining factor depends only on the operator on
`Y(C)` (`coef_eq_of_agree_on_region`) and is bounded uniformly in the volume
(`norm_coef_le_final`). -/
theorem det_mul_det_boxResolvent_eq_prod_exp_coef {t κ : ℝ} (hκ : 0 < κ)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ'))
    (h1 : Complex.exp (ell (fun _ => 1)) = (shiftMat (finalOp d L N₀ k v a) t).det *
      (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det) :
    (shiftMat (finalOp d L N₀ k v a) t).det *
      (∑ z : MacIdx d N₀ M, Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t).det =
      ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ell C) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  have hsum := sum_coef_eq hR (hell.mono (fun s hs => by
    rw [polydisc_eq_ball hR0] at hs
    exact Metric.ball_subset_ball hρ'.le hs))
  rw [← taggedG_one Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
    (macTags d N₀ M) (finalOp d L N₀ k v a) t, ← h1,
    show (fun _ : MacIdx d N₀ M => (1 : ℂ)) = 1 from rfl, hsum, Complex.exp_sum]

end Final

end Balaban.Green
