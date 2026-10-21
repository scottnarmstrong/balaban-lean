/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseDefectLogDet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local terms of `½ log det (1 + D)` regrouped by the set of sites visited by a walk

The entry `(D^m)_{xy}` is a sum over walks `x = z_0, z_1, …, z_m = y` of `∏ D(z_i, z_{i+1})`.
Grouping the walks by the set `S` of sites they visit gives `walkW D m x y S`, defined by the
recursion on the first step, with
`∑_S walkW D m x y S = (D^m)_{xy}` (`sum_walkW`) and `∑_y ∑_S |walkW D m x y S| ≤ q^m` when the
row sums of `D` are at most `q` (`sum_norm_walkW_le`).  A non-zero `walkW D m x y S` has `x, y ∈ S`,
at most `m + 1` sites, and every site of `S` is reached from `x` inside `S` by steps with
`D ≠ 0` (`walkW_ne_zero_imp`).

For a label `lab S` of the visited set (the polymer hull of the set), the polymer term
`walkPolyTerm lab D x Y` collects the walks with `lab S = Y`.  They sum to `∑_n t_{x,n}`
(`sum_walkPolyTerm`), and if `size (lab S) ≤ c |S|` for the sets `S` visited by walks from `x`, then
`∑_Y |t_Y| e^{κ size Y} ≤ e^{2κc} q` when `q e^{κ c} ≤ 1/2` (`sum_norm_walkPolyTerm_le`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Finset Matrix

section Walks

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Walk sums resolved by the set of visited sites.**  `walkW D m x y S` is the sum of
`∏ D(z_i, z_{i+1})` over the walks `x = z_0, …, z_m = y` whose set of sites is `S`. -/
noncomputable def walkW (D : Matrix ι ι ℂ) : ℕ → ι → ι → Finset ι → ℂ
  | 0, x, y, S => if x = y ∧ S = {x} then 1 else 0
  | m + 1, x, y, S => ∑ w, ∑ S', if S = insert x S' then D x w * walkW D m w y S' else 0

/-- Summing over the visited sets gives the matrix power. -/
theorem sum_walkW (D : Matrix ι ι ℂ) (m : ℕ) :
    ∀ x y, ∑ S, walkW D m x y S = (D ^ m) x y := by
  induction m with
  | zero =>
    intro x y
    by_cases h : x = y
    · subst h; simp [walkW]
    · simp [walkW, h]
  | succ m ih =>
    intro x y
    rw [pow_succ', Matrix.mul_apply]
    simp only [walkW]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.mul_sum, ih]

/-- The row sums of the visited-set resolved walk sums. -/
theorem sum_norm_walkW_le (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (m : ℕ) :
    ∀ x, ∑ y, ∑ S, ‖walkW D m x y S‖ ≤ q ^ m := by
  induction m with
  | zero =>
    intro x
    simp only [walkW]
    have : ∀ y, ∑ S : Finset ι, ‖(if x = y ∧ S = {x} then (1 : ℂ) else 0)‖ =
        if x = y then 1 else 0 := by
      intro y
      by_cases h : x = y
      · subst h
        have h1 : ∀ S : Finset ι, ‖(if S = {x} then (1 : ℂ) else 0)‖ =
            if S = {x} then 1 else 0 := fun S => by split_ifs <;> simp
        simp [h1]
      · simp [h]
    simp [this]
  | succ m ih =>
    intro x
    have hb : ∀ y S, ‖walkW D (m + 1) x y S‖ ≤
        ∑ w, ∑ S', if S = insert x S' then ‖D x w‖ * ‖walkW D m w y S'‖ else 0 := by
      intro y S
      simp only [walkW]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S' _ => ?_)
      split_ifs
      · exact (norm_mul _ _).le
      · simp
    calc ∑ y, ∑ S, ‖walkW D (m + 1) x y S‖
        ≤ ∑ y, ∑ S, ∑ w, ∑ S', if S = insert x S' then ‖D x w‖ * ‖walkW D m w y S'‖ else 0 :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun S _ => hb y S
      _ = ∑ w, ‖D x w‖ * ∑ y, ∑ S', ‖walkW D m w y S'‖ := by
          have : ∀ y, ∑ S : Finset ι, ∑ w, ∑ S', (if S = insert x S' then
              ‖D x w‖ * ‖walkW D m w y S'‖ else 0) =
              ∑ w, ∑ S', ‖D x w‖ * ‖walkW D m w y S'‖ := by
            intro y
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [Finset.sum_comm]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          simp only [this]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum]
          simp only [Finset.mul_sum]
      _ ≤ ∑ w, ‖D x w‖ * q ^ m :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (ih w) (norm_nonneg _)
      _ = (∑ w, ‖D x w‖) * q ^ m := by rw [Finset.sum_mul]
      _ ≤ q * q ^ m := mul_le_mul_of_nonneg_right (hK x) (by positivity)
      _ = q ^ (m + 1) := by ring

/-- **Support of the visited-set resolved walk sums.**  If `walkW D m x y S ≠ 0` then `x, y ∈ S`,
`S` has at most `m + 1` sites, and every site of `S` is reached from `x` inside `S` by steps with
`D ≠ 0`. -/
theorem walkW_ne_zero_imp (D : Matrix ι ι ℂ) (m : ℕ) :
    ∀ x y S, walkW D m x y S ≠ 0 → x ∈ S ∧ y ∈ S ∧ S.card ≤ m + 1 ∧
      ∀ s ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ D a b ≠ 0) x s := by
  induction m with
  | zero =>
    intro x y S h
    simp only [walkW] at h
    by_cases hc : x = y ∧ S = {x}
    · obtain ⟨rfl, rfl⟩ := hc
      refine ⟨by simp, by simp, by simp, fun s hs => ?_⟩
      rw [Finset.mem_singleton.1 hs]
    · simp [hc] at h
  | succ m ih =>
    intro x y S h
    simp only [walkW] at h
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨S', -, hS'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    by_cases hc : S = insert x S'
    · simp only [hc, ite_true] at hS'
      obtain ⟨hDw, hW⟩ := mul_ne_zero_iff.1 hS'
      obtain ⟨hw1, hy1, hcard, hch⟩ := ih w y S' hW
      subst hc
      have hsub : S' ⊆ insert x S' := Finset.subset_insert _ _
      refine ⟨Finset.mem_insert_self _ _, hsub hy1,
        (Finset.card_insert_le _ _).trans (by omega), fun s hs => ?_⟩
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head ⟨Finset.mem_insert_self _ _, hsub hw1, hDw⟩
          (Relation.ReflTransGen.mono (fun a b ⟨ha, hb, hD⟩ => ⟨hsub ha, hsub hb, hD⟩) w s (hch s hs))
    · simp [hc] at hS'

/-- **The local term of one visited set**: the part of `t_{x,n}` from the walks with visited set
`S`. -/
noncomputable def walkTerm (D : Matrix ι ι ℂ) (x : ι) (n : ℕ) (S : Finset ι) : ℂ :=
  (1 / 2 : ℂ) * ((-1 : ℂ) ^ n * walkW D (n + 1) x x S / ((n : ℂ) + 1))

/-- The visited-set terms sum to the local term `t_{x,n}`. -/
theorem sum_walkTerm (D : Matrix ι ι ℂ) (x : ι) (n : ℕ) :
    ∑ S, walkTerm D x n S = defectTerm D x n := by
  unfold walkTerm defectTerm
  rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, sum_walkW]

theorem norm_walkTerm_le (D : Matrix ι ι ℂ) (x : ι) (n : ℕ) (S : Finset ι) :
    ‖walkTerm D x n S‖ ≤ 1 / 2 * ‖walkW D (n + 1) x x S‖ := by
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hc : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have e : ‖(-1 : ℂ) ^ n * walkW D (n + 1) x x S / ((n : ℂ) + 1)‖ =
      ‖walkW D (n + 1) x x S‖ / ((n : ℝ) + 1) := by
    rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hc]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  unfold walkTerm
  rw [norm_mul, h12, e]
  have := div_le_self (norm_nonneg (walkW D (n + 1) x x S)) hn
  linarith

/-- The visited-set terms of `t_{x,n}` have total size at most `½ q^{n+1}`. -/
theorem sum_norm_walkTerm_le (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι) (n : ℕ) :
    ∑ S, ‖walkTerm D x n S‖ ≤ 1 / 2 * q ^ (n + 1) := by
  calc ∑ S, ‖walkTerm D x n S‖ ≤ ∑ S, 1 / 2 * ‖walkW D (n + 1) x x S‖ :=
        Finset.sum_le_sum fun S _ => norm_walkTerm_le D x n S
    _ = 1 / 2 * ∑ S, ‖walkW D (n + 1) x x S‖ := by rw [← Finset.mul_sum]
    _ ≤ 1 / 2 * ∑ y, ∑ S, ‖walkW D (n + 1) x y S‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.single_le_sum (f := fun y => ∑ S, ‖walkW D (n + 1) x y S‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x)
    _ ≤ 1 / 2 * q ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (sum_norm_walkW_le D hq0 hK (n + 1) x) (by norm_num)

section Polymers

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **The polymer term of the walks**: the sum over `n` of the local terms of the walks from `x`
whose visited set has label `Y`. -/
noncomputable def walkPolyTerm (lab : Finset ι → P) (D : Matrix ι ι ℂ) (x : ι) (Y : P) : ℂ :=
  ∑' n, ∑ S, if lab S = Y then walkTerm D x n S else 0

omit [Fintype P] in
theorem summable_walkPoly (lab : Finset ι → P) (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι) (Y : P) :
    Summable fun n => ∑ S, if lab S = Y then walkTerm D x n S else 0 := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => 1 / 2 * q ^ (n + 1)) ?_ fun n => ?_
  · exact ((summable_geometric_of_lt_one hq0 hq1).mul_left q |>.mul_left (1 / 2)).congr
      fun n => by ring
  · refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun S _ => ?_)
      (sum_norm_walkTerm_le D hq0 hK x n))
    split_ifs <;> simp

/-- **Regrouping the local terms by the label of the visited set.** -/
theorem sum_walkPolyTerm (lab : Finset ι → P) (D : Matrix ι ι ℂ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι) :
    ∑ Y, walkPolyTerm lab D x Y = ∑' n, defectTerm D x n := by
  unfold walkPolyTerm
  rw [← Summable.tsum_finsetSum fun Y _ => summable_walkPoly lab D hq0 hq1 hK x Y]
  refine tsum_congr fun n => ?_
  rw [Finset.sum_comm, ← sum_walkTerm]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp

/-- **Decay of the polymer terms of the walks.**  Let `size (lab S) ≤ c |S|` for every set `S`
containing `x` and reached from `x` inside `S` by steps with `D ≠ 0`.  If `q e^{κ c} ≤ 1/2`, then
`∑_Y |t_Y| e^{κ size Y} ≤ e^{2 κ c} q`. -/
theorem sum_norm_walkPolyTerm_le (lab : Finset ι → P) (size : P → ℝ) (D : Matrix ι ι ℂ)
    {q κ c : ℝ} (hq0 : 0 ≤ q) (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (hρ : q * Real.exp (κ * c) ≤ 1 / 2) (hK : ∀ x, ∑ y, ‖D x y‖ ≤ q) (x : ι)
    (hsize : ∀ S : Finset ι, x ∈ S →
      (∀ s ∈ S, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ D a b ≠ 0) x s) →
        size (lab S) ≤ c * S.card) :
    ∑ Y, ‖walkPolyTerm lab D x Y‖ * Real.exp (κ * size Y) ≤ Real.exp (2 * κ * c) * q := by
  set ρ := q * Real.exp (κ * c) with hρd
  have hE1 : 1 ≤ Real.exp (κ * c) := Real.one_le_exp (by positivity)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by linarith
  have hq1 : q < 1 := by nlinarith
  -- termwise bound on the visited sets
  have hb : ∀ n : ℕ, ∑ S, ‖walkTerm D x n S‖ * Real.exp (κ * size (lab S)) ≤
      1 / 2 * Real.exp (κ * c) * ρ ^ (n + 1) := by
    intro n
    have h2 : ∀ S : Finset ι, ‖walkTerm D x n S‖ * Real.exp (κ * size (lab S)) ≤
        ‖walkTerm D x n S‖ * Real.exp (κ * c) ^ (n + 2) := by
      intro S
      by_cases h0 : walkW D (n + 1) x x S = 0
      · have : walkTerm D x n S = 0 := by simp [walkTerm, h0]
        simp [this]
      · obtain ⟨hxS, -, hcard, hch⟩ := walkW_ne_zero_imp D (n + 1) x x S h0
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [← Real.exp_nat_mul]
        refine Real.exp_le_exp.2 ?_
        have h3 := hsize S hxS hch
        have h4 : (S.card : ℝ) ≤ ((n : ℝ) + 2) := by
          have : (S.card : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
          push_cast at this; linarith
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left h4 hc]
    calc ∑ S, ‖walkTerm D x n S‖ * Real.exp (κ * size (lab S))
        ≤ ∑ S, ‖walkTerm D x n S‖ * Real.exp (κ * c) ^ (n + 2) :=
          Finset.sum_le_sum fun S _ => h2 S
      _ = (∑ S, ‖walkTerm D x n S‖) * Real.exp (κ * c) ^ (n + 2) := by rw [Finset.sum_mul]
      _ ≤ (1 / 2 * q ^ (n + 1)) * Real.exp (κ * c) ^ (n + 2) :=
          mul_le_mul_of_nonneg_right (sum_norm_walkTerm_le D hq0 hK x n) (by positivity)
      _ = 1 / 2 * Real.exp (κ * c) * ρ ^ (n + 1) := by
          rw [hρd, mul_pow]; ring
  have hgs : Summable fun n : ℕ => 1 / 2 * Real.exp (κ * c) * ρ ^ (n + 1) :=
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ |>.mul_left
      (1 / 2 * Real.exp (κ * c))).congr fun n => by ring
  have hsn : Summable fun n => ∑ S, ‖walkTerm D x n S‖ * Real.exp (κ * size (lab S)) :=
    Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun S _ => by positivity) hb hgs
  have hsY : ∀ Y : P, Summable fun n => ∑ S, (if lab S = Y then ‖walkTerm D x n S‖ else 0) *
      Real.exp (κ * size Y) := by
    intro Y
    refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun S _ => by
      split_ifs <;> positivity) (fun n => Finset.sum_le_sum fun S _ => ?_) hsn
    split_ifs with h
    · rw [h]
    · simp; positivity
  have hY : ∀ Y : P, ‖walkPolyTerm lab D x Y‖ ≤
      ∑' n, ∑ S, if lab S = Y then ‖walkTerm D x n S‖ else 0 := by
    intro Y
    unfold walkPolyTerm
    have hgeo : Summable fun n : ℕ => 1 / 2 * q ^ (n + 1) :=
      ((summable_geometric_of_lt_one hq0 hq1).mul_left q |>.mul_left (1 / 2)).congr
        fun n => by ring
    have hsY' : Summable fun n => ∑ S, if lab S = Y then ‖walkTerm D x n S‖ else 0 := by
      refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun S _ => by
        split_ifs <;> simp) (fun n => ?_) hgeo
      refine (Finset.sum_le_sum fun S _ => ?_).trans (sum_norm_walkTerm_le D hq0 hK x n)
      split_ifs <;> simp
    have hnorm : ∀ n, ‖∑ S, if lab S = Y then walkTerm D x n S else 0‖ ≤
        ∑ S, if lab S = Y then ‖walkTerm D x n S‖ else 0 := fun n =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => by split_ifs <;> simp)
    have hsn' : Summable fun n => ‖∑ S, if lab S = Y then walkTerm D x n S else 0‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hsY'
    exact (norm_tsum_le_tsum_norm hsn').trans (Summable.tsum_le_tsum hnorm hsn' hsY')
  calc ∑ Y, ‖walkPolyTerm lab D x Y‖ * Real.exp (κ * size Y)
      ≤ ∑ Y, (∑' n, ∑ S, if lab S = Y then ‖walkTerm D x n S‖ else 0) *
          Real.exp (κ * size Y) :=
        Finset.sum_le_sum fun Y _ => mul_le_mul_of_nonneg_right (hY Y) (Real.exp_pos _).le
    _ = ∑ Y, ∑' n, ∑ S, (if lab S = Y then ‖walkTerm D x n S‖ else 0) *
          Real.exp (κ * size Y) := by
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [← tsum_mul_right]
        exact tsum_congr fun n => by rw [Finset.sum_mul]
    _ = ∑' n, ∑ Y, ∑ S, (if lab S = Y then ‖walkTerm D x n S‖ else 0) *
          Real.exp (κ * size Y) :=
        (Summable.tsum_finsetSum fun Y _ => hsY Y).symm
    _ = ∑' n, ∑ S, ‖walkTerm D x n S‖ * Real.exp (κ * size (lab S)) := by
        refine tsum_congr fun n => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        simp [ite_mul]
    _ ≤ ∑' n : ℕ, 1 / 2 * Real.exp (κ * c) * ρ ^ (n + 1) := hsn.tsum_le_tsum hb hgs
    _ = 1 / 2 * Real.exp (κ * c) * (ρ * (1 - ρ)⁻¹) := by
        rw [tsum_mul_left]
        congr 1
        have : (fun n : ℕ => ρ ^ (n + 1)) = fun n => ρ * ρ ^ n := by
          funext n; ring
        rw [this, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ Real.exp (κ * c) * ρ := by
        have h1 : (1 - ρ)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
        have : ρ * (1 - ρ)⁻¹ ≤ 2 * ρ := by nlinarith
        nlinarith [Real.exp_pos (κ * c)]
    _ = Real.exp (2 * κ * c) * q := by
        rw [hρd, show 2 * κ * c = κ * c + κ * c by ring, Real.exp_add]; ring

end Polymers

end Walks

end Balaban.LargeField.Base
