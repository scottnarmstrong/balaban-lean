/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLogDetLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local expansion of `½ log det (1 + D)` for a finite-range defect

Let `D` be a complex matrix on a finite set `ι` of sites with a distance `δ`, of range `r`
(`δ x y > r → D x y = 0`) and with row sums at most `q < 1`.  The series of the logarithm of the
determinant is a sum of local terms,
`½ ∑_n (−1)^n tr(D^{n+1}) / (n+1) = ∑_x ∑_n t_{x,n}`, `t_{x,n} = ½ (−1)^n (D^{n+1})_{xx} / (n+1)`
(`defectTerm`).  These are the defect-determinant terms of the whitening of the first step.

* `det_one_add_eq_exp_sum_defectTerm`: `det (1 + D) = exp (2 ∑_x ∑_n t_{x,n})`
  (from `Green.det_one_sub_eq_exp_tsum_trace` with `K = −D`);
* `norm_defectTerm_le`: `|t_{x,n}| ≤ ½ q^{n+1}`;
* `pow_apply_eq_of_agree`, `defectTerm_eq_of_agree`: `(D^m)_{xx}` and `t_{x,n}` only see the
  entries of `D` in the ball of radius `m r` (resp. `(n+1) r`) around `x`, so they agree for two
  matrices that correspond on the balls (the two-torus form);
* `sum_defectPolyTerm`, `sum_norm_defectPolyTerm_le`: grouping the terms by a polymer `hull x n`
  with `size (hull x n) ≤ c (n+1)`, the polymer terms sum to `∑_n t_{x,n}` and
  `∑_Y |t_Y| e^{κ size Y} ≤ e^{κ c} q` when `q e^{κ c} ≤ 1/2`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Finset Matrix

section Series

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The local terms of `½ log det (1 + D)`**: `t_{x,n} = ½ (−1)^n (D^{n+1})_{xx} / (n+1)`. -/
noncomputable def defectTerm (D : Matrix ι ι ℂ) (x : ι) (n : ℕ) : ℂ :=
  (1 / 2 : ℂ) * ((-1 : ℂ) ^ n * (D ^ (n + 1)) x x / ((n : ℂ) + 1))

/-- The local terms are bounded by `½ q^{n+1}` when the row sums of `D` are at most `q`. -/
theorem norm_defectTerm_le (D : Matrix ι ι ℂ) {q : ℝ} (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι)
    (n : ℕ) : ‖defectTerm D x n‖ ≤ 1 / 2 * q ^ (n + 1) := by
  have h1 : ‖(D ^ (n + 1)) x x‖ ≤ q ^ (n + 1) :=
    (Finset.single_le_sum (f := fun y => ‖(D ^ (n + 1)) x y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ x)).trans (Green.matrix_rowsum_pow_le D hK (n + 1) x)
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have e : ‖(-1 : ℂ) ^ n * (D ^ (n + 1)) x x / ((n : ℂ) + 1)‖ =
      ‖(D ^ (n + 1)) x x‖ / ((n : ℝ) + 1) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hc]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  have h2 : ‖(D ^ (n + 1)) x x‖ / ((n : ℝ) + 1) ≤ q ^ (n + 1) :=
    (div_le_self (norm_nonneg _) hn).trans h1
  unfold defectTerm
  rw [norm_mul, h12, e]
  linarith

/-- The terms are summable over `n`. -/
theorem summable_defectTerm (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι) : Summable fun n => defectTerm D x n := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => 1 / 2 * q ^ (n + 1)) ?_
    (fun n => norm_defectTerm_le D hK x n)
  exact ((summable_geometric_of_lt_one hq0 hq1).mul_left q |>.mul_left (1 / 2)).congr
    fun n => by ring

/-- **The determinant of `1 + D` as the exponential of the sum of the local terms.** -/
theorem det_one_add_eq_exp_sum_defectTerm (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) :
    (1 + D).det = Complex.exp (2 * ∑ x, ∑' n, defectTerm D x n) := by
  have hK' : ∀ x, ∑ y, ‖(-D) x y‖ ≤ q := fun x => by simpa using hK x
  obtain ⟨hs, hdet⟩ := Green.det_one_sub_eq_exp_tsum_trace (-D) hq1 hK'
  rw [sub_neg_eq_add] at hdet
  rw [hdet]
  congr 1
  have hpow : ∀ m : ℕ, ((-D) ^ m).trace = (-1 : ℂ) ^ m * (D ^ m).trace := by
    intro m
    have : (-D) = (-1 : ℂ) • D := by simp
    rw [this, smul_pow, Matrix.trace_smul, smul_eq_mul]
  have hsw : ∑ x, ∑' n, defectTerm D x n = ∑' n, ∑ x, defectTerm D x n :=
    (Summable.tsum_finsetSum fun x _ => summable_defectTerm D hq0 hq1 hK x).symm
  rw [hsw, ← tsum_neg, ← Summable.tsum_mul_left]
  · refine tsum_congr fun n => ?_
    rw [hpow (n + 1)]
    unfold defectTerm
    rw [← Finset.mul_sum]
    simp only [Matrix.trace, Matrix.diag, ← Finset.sum_div, ← Finset.mul_sum]
    ring
  · exact summable_sum fun x _ => summable_defectTerm D hq0 hq1 hK x

end Series

section Local

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **The entry `(D^m)_{ux}` only sees the ball.**  If `D` has range `r` for the distance `δ`
(`δ` satisfies the triangle inequality in the form `δ x w ≤ δ x u + δ u w`), then for
`δ x u + m r ≤ ρ` the entry `(D^m)_{ux}` equals that of the power of the restriction of `D` to the
ball `{w | δ x w ≤ ρ}` of radius `ρ` about `x`. -/
theorem pow_apply_eq_restrict (δ : ι → ι → ℕ) (htri : ∀ x u w, δ x w ≤ δ x u + δ u w)
    (D : Matrix ι ι ℂ) {r : ℕ} (hr : ∀ x y, r < δ x y → D x y = 0) (x : ι) {ρ : ℕ}
    (hx : δ x x ≤ ρ) :
    ∀ (m : ℕ) (u : ι) (hu : δ x u + m * r ≤ ρ),
      (D ^ m) u x =
        ((D.submatrix (fun w : {w // δ x w ≤ ρ} => w.1) (fun w : {w // δ x w ≤ ρ} => w.1)) ^ m)
          ⟨u, by nlinarith [Nat.zero_le (m * r)]⟩ ⟨x, hx⟩ := by
  intro m
  induction m with
  | zero =>
    intro u hu
    simp only [pow_zero, Matrix.one_apply]
    by_cases h : u = x
    · subst h; simp
    · have : (⟨u, by simpa using hu⟩ : {w // δ x w ≤ ρ}) ≠ ⟨x, hx⟩ := fun h' =>
        h (congrArg Subtype.val h')
      simp [h, this]
  | succ m ih =>
    intro u hu
    set A := D.submatrix (fun w : {w // δ x w ≤ ρ} => w.1) (fun w : {w // δ x w ≤ ρ} => w.1)
      with hA
    rw [pow_succ' D, pow_succ' A, Matrix.mul_apply, Matrix.mul_apply]
    have hout : ∀ w, w ∉ Finset.univ.filter (fun w => δ x w ≤ ρ) → D u w * (D ^ m) w x = 0 := by
      intro w hw
      have hD : D u w = 0 := by
        by_contra hne
        have h1 : δ u w ≤ r := by
          by_contra h; exact hne (hr u w (by omega))
        apply hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := htri x u w
        nlinarith
      rw [hD, zero_mul]
    calc ∑ j, D u j * (D ^ m) j x
        = ∑ j ∈ Finset.univ.filter (fun w => δ x w ≤ ρ), D u j * (D ^ m) j x :=
          (Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => hout w hw)).symm
      _ = ∑ j : {w // δ x w ≤ ρ}, D u j.1 * (D ^ m) j.1 x :=
          Finset.sum_subtype _ (fun w => by simp) (fun w => D u w * (D ^ m) w x)
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hD : D u j.1 = 0
          · simp [hA, hD]
          · have h1 : δ u j.1 ≤ r := by
              by_contra h; exact hD (hr u j.1 (by omega))
            have h2 := htri x u j.1
            have h3 : δ x j.1 + m * r ≤ ρ := by nlinarith
            rw [ih j.1 h3]
            simp [hA]

theorem pow_submatrix_equiv {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ ≃ κ') (A : Matrix κ κ ℂ) (m : ℕ) :
    (A.submatrix e.symm e.symm) ^ m = (A ^ m).submatrix e.symm e.symm := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_succ, ih, Matrix.submatrix_mul_equiv]

/-- **The diagonal entry `(D^m)_{xx}` agrees for matrices that correspond on the ball.**  Let `D`,
`D'` have range `r` for the distances `δ`, `δ'` (triangle inequality as in
`pow_apply_eq_restrict`), and let `e` be a bijection of the balls of radius `ρ ≥ m r` about `x`,
`x'` taking `x` to `x'` and carrying the entries of `D` to those of `D'`.  Then
`(D^m)_{xx} = (D'^m)_{x'x'}`. -/
theorem pow_diag_eq_of_agree (δ : ι → ι → ℕ) (δ' : ι' → ι' → ℕ)
    (htri : ∀ x u w, δ x w ≤ δ x u + δ u w) (htri' : ∀ x u w, δ' x w ≤ δ' x u + δ' u w)
    (hδ0 : ∀ x, δ x x = 0) (hδ0' : ∀ x, δ' x x = 0)
    (D : Matrix ι ι ℂ) (D' : Matrix ι' ι' ℂ) {r : ℕ} (hr : ∀ x y, r < δ x y → D x y = 0)
    (hr' : ∀ x y, r < δ' x y → D' x y = 0) (x : ι) (x' : ι') {ρ m : ℕ} (hm : m * r ≤ ρ)
    (e : {w // δ x w ≤ ρ} ≃ {w // δ' x' w ≤ ρ})
    (hex : (e ⟨x, by rw [hδ0]; exact Nat.zero_le _⟩).1 = x')
    (hD : ∀ u v, D' (e u).1 (e v).1 = D u v) : (D ^ m) x x = (D' ^ m) x' x' := by
  have hx : δ x x ≤ ρ := by rw [hδ0]; exact Nat.zero_le _
  have hx' : δ' x' x' ≤ ρ := by rw [hδ0']; exact Nat.zero_le _
  rw [pow_apply_eq_restrict δ htri D hr x hx m x (by rw [hδ0]; omega),
    pow_apply_eq_restrict δ' htri' D' hr' x' hx' m x' (by rw [hδ0']; omega)]
  have hsub : (D'.submatrix (fun w : {w // δ' x' w ≤ ρ} => w.1)
      (fun w : {w // δ' x' w ≤ ρ} => w.1)) =
      (D.submatrix (fun w : {w // δ x w ≤ ρ} => w.1) (fun w : {w // δ x w ≤ ρ} => w.1)).submatrix
        e.symm e.symm := by
    ext i j
    simp only [Matrix.submatrix_apply]
    have := hD (e.symm i) (e.symm j)
    simpa using this
  rw [hsub, pow_submatrix_equiv e, Matrix.submatrix_apply]
  have h1 : e.symm ⟨x', hx'⟩ = ⟨x, hx⟩ := by
    rw [Equiv.symm_apply_eq]; exact Subtype.ext hex.symm
  rw [h1]

/-- **The local terms agree for matrices that correspond on the ball of radius `(n+1) r`.** -/
theorem defectTerm_eq_of_agree (δ : ι → ι → ℕ) (δ' : ι' → ι' → ℕ)
    (htri : ∀ x u w, δ x w ≤ δ x u + δ u w) (htri' : ∀ x u w, δ' x w ≤ δ' x u + δ' u w)
    (hδ0 : ∀ x, δ x x = 0) (hδ0' : ∀ x, δ' x x = 0)
    (D : Matrix ι ι ℂ) (D' : Matrix ι' ι' ℂ) {r : ℕ} (hr : ∀ x y, r < δ x y → D x y = 0)
    (hr' : ∀ x y, r < δ' x y → D' x y = 0) (x : ι) (x' : ι') (n : ℕ)
    (e : {w // δ x w ≤ (n + 1) * r} ≃ {w // δ' x' w ≤ (n + 1) * r})
    (hex : (e ⟨x, by rw [hδ0]; exact Nat.zero_le _⟩).1 = x')
    (hD : ∀ u v, D' (e u).1 (e v).1 = D u v) : defectTerm D' x' n = defectTerm D x n := by
  unfold defectTerm
  rw [pow_diag_eq_of_agree δ δ' htri htri' hδ0 hδ0' D D' hr hr' x x' le_rfl e hex hD]

end Local

section Polymers

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Type*} [Fintype P] [DecidableEq P]

/-- **The polymer term**: the sum of the local terms `t_{x,n}` whose hull `hull x n` is `Y`. -/
noncomputable def defectPolyTerm (hull : ι → ℕ → P) (D : Matrix ι ι ℂ) (x : ι) (Y : P) : ℂ :=
  ∑' n, if hull x n = Y then defectTerm D x n else 0

/-- **Regrouping by polymers**: the polymer terms sum to `∑_n t_{x,n}`. -/
theorem sum_defectPolyTerm (hull : ι → ℕ → P) (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι) :
    ∑ Y, defectPolyTerm hull D x Y = ∑' n, defectTerm D x n := by
  have hs := summable_defectTerm D hq0 hq1 hK x
  have hY : ∀ Y : P, Summable fun n => if hull x n = Y then defectTerm D x n else 0 := by
    intro Y
    refine Summable.of_norm_bounded (g := fun n => ‖defectTerm D x n‖) hs.norm fun n => ?_
    split_ifs <;> simp
  unfold defectPolyTerm
  rw [← Summable.tsum_finsetSum fun Y _ => hY Y]
  refine tsum_congr fun n => ?_
  simp

/-- **Decay of the polymer terms.**  If the hull of the ball of radius `(n+1) r` has size
`size (hull x n) ≤ c (n+1)` and `q e^{κ c} ≤ 1/2`, then
`∑_Y |t_Y| e^{κ size Y} ≤ e^{κ c} q`. -/
theorem sum_norm_defectPolyTerm_le (hull : ι → ℕ → P) (size : P → ℝ) (D : Matrix ι ι ℂ)
    {q κ c : ℝ} (hq0 : 0 ≤ q) (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (hρ : q * Real.exp (κ * c) ≤ 1 / 2) (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q)
    (hsize : ∀ x n, size (hull x n) ≤ c * ((n : ℝ) + 1)) (x : ι) :
    ∑ Y, ‖defectPolyTerm hull D x Y‖ * Real.exp (κ * size Y) ≤ Real.exp (κ * c) * q := by
  set ρ := q * Real.exp (κ * c) with hρd
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  have hq1 : q < 1 := by
    have : 1 ≤ Real.exp (κ * c) := Real.one_le_exp (by positivity)
    nlinarith
  have hs := summable_defectTerm D hq0 hq1 hK x
  -- the termwise bound
  have hb : ∀ n : ℕ, ‖defectTerm D x n‖ * Real.exp (κ * size (hull x n)) ≤
      1 / 2 * ρ ^ (n + 1) := by
    intro n
    have h1 := norm_defectTerm_le D hK x n
    have h2 : Real.exp (κ * size (hull x n)) ≤ Real.exp (κ * c) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      have := hsize x n
      push_cast
      nlinarith
    calc ‖defectTerm D x n‖ * Real.exp (κ * size (hull x n))
        ≤ (1 / 2 * q ^ (n + 1)) * Real.exp (κ * c) ^ (n + 1) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = 1 / 2 * ρ ^ (n + 1) := by rw [hρd, mul_pow]; ring
  have hgs : Summable fun n : ℕ => 1 / 2 * ρ ^ (n + 1) :=
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ |>.mul_left (1 / 2)).congr
      fun n => by ring
  have hsn : Summable fun n => ‖defectTerm D x n‖ * Real.exp (κ * size (hull x n)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hb hgs
  -- bound each polymer term
  have hY : ∀ Y : P, ‖defectPolyTerm hull D x Y‖ ≤
      ∑' n, if hull x n = Y then ‖defectTerm D x n‖ else 0 := by
    intro Y
    unfold defectPolyTerm
    have hsY : Summable fun n => if hull x n = Y then ‖defectTerm D x n‖ else 0 :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp) (fun n => by
        split_ifs <;> simp) hs.norm
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun n => ?_))
    · exact hsY.congr fun n => by split_ifs <;> simp
    · split_ifs <;> simp
  have hsY : ∀ Y : P, Summable fun n => (if hull x n = Y then ‖defectTerm D x n‖ else 0) *
      Real.exp (κ * size Y) := by
    intro Y
    refine Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) (fun n => ?_)
      hsn
    split_ifs with h
    · rw [h]
    · simp; positivity
  calc ∑ Y, ‖defectPolyTerm hull D x Y‖ * Real.exp (κ * size Y)
      ≤ ∑ Y, (∑' n, if hull x n = Y then ‖defectTerm D x n‖ else 0) *
          Real.exp (κ * size Y) :=
        Finset.sum_le_sum fun Y _ =>
          mul_le_mul_of_nonneg_right (hY Y) (Real.exp_pos _).le
    _ = ∑ Y, ∑' n, (if hull x n = Y then ‖defectTerm D x n‖ else 0) *
          Real.exp (κ * size Y) :=
        Finset.sum_congr rfl fun Y _ => (tsum_mul_right).symm
    _ = ∑' n, ∑ Y, (if hull x n = Y then ‖defectTerm D x n‖ else 0) *
          Real.exp (κ * size Y) :=
        (Summable.tsum_finsetSum fun Y _ => hsY Y).symm
    _ = ∑' n, ‖defectTerm D x n‖ * Real.exp (κ * size (hull x n)) := by
        refine tsum_congr fun n => ?_
        simp [ite_mul]
    _ ≤ ∑' n : ℕ, 1 / 2 * ρ ^ (n + 1) := hsn.tsum_le_tsum hb hgs
    _ = 1 / 2 * (ρ * (1 - ρ)⁻¹) := by
        rw [tsum_mul_left]
        congr 1
        have : (fun n : ℕ => ρ ^ (n + 1)) = fun n => ρ * ρ ^ n := by
          funext n; ring
        rw [this, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ ρ := by
        have h1 : (1 - ρ)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        nlinarith
    _ = Real.exp (κ * c) * q := by rw [hρd]; ring

end Polymers

end Balaban.LargeField.Base
