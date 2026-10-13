/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.KF0HoleWalk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Killed-walk kernels on two tori agree when the walks do not wind

Coefficient-level agreement only.  The agreement of the integrated terms and the one-scale
theorem are NOT proved here.

Setting: a base point `x̃ ∈ ℤ^d`, a finite set `D̃ ⊂ ℤ^d`, step sequences `w` of length `n`.  The
integer walk visits `zWalkPos x̃ w k = x̃ + (first k steps)`.  On the torus of side `m` the
base point is `intToTorus x̃` and the bad set is the image `D̃.image (intToTorus d m)`.

**Non-wrapping hypothesis** (for `n`-step walks): for every `z ∈ D̃` and every coordinate `μ`,
`|z_μ - x̃_μ| + n < m` (and `|ỹ_μ - x̃_μ| + n < m` for the endpoint `ỹ`).  Then a point of the
walk is congruent mod `m` to a point of `D̃` (or to `ỹ`) only if it is equal to it, so meeting the
bad set on the torus is the same as meeting `D̃` in `ℤ^d`.

* `walkMeets_image_iff`: `WalkMeets (D̃.image (intToTorus d m)) (intToTorus d m x̃) w ↔
  ZWalkMeets D̃ x̃ w`.
* `kwAdjG_pow_eq_zKilledCount`: the entry of `kwAdjG^n` is the integer count `zKilledCount`;
  `kwAdjG_pow_torus_eq` gives the agreement on two tori.
* `sum_range_kwAdjG_pow_torus_eq`, `abs_kwC_sub_le`, `abs_kf0C_sub_kwC_sub_le`: truncated
  kernels agree, full kernels agree up to the walk tail.
* `kwRootedLoopCount`, `kwRootedLoopCount_torus_eq`: the per-root count of closed `n`-step walks
  that meet the bad set agrees on two tori (`kwTraceDiff` is the sum of these over all roots).
-/

@[expose] public section

namespace Balaban.Green

open Matrix

variable {d m m' : ℕ} [NeZero m] [NeZero m']

/-! ### T1: the integer picture -/

omit [NeZero m] in
/-- Two integer vectors with entries differing by less than `m` and equal mod `m` are equal. -/
theorem eq_of_intToTorus_eq_of_lt {a b : Fin d → ℤ} (h : ∀ μ, |a μ - b μ| < m)
    (hab : intToTorus d m a = intToTorus d m b) : a = b := by
  ext μ
  have h1 := congrFun hab μ
  rw [intToTorus_apply, intToTorus_apply] at h1
  have h2 : ((a μ - b μ : ℤ) : ZMod m) = 0 := by push_cast; rw [h1]; ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have := Int.eq_zero_of_abs_lt_dvd h2 (h μ)
  linarith

/-- The position in `ℤ^d` after the first `k` steps of `w`, started at `x̃`. -/
def zWalkPos (x : Fin d → ℤ) {n : ℕ} (w : Fin n → Fin d × Bool) (k : ℕ) : Fin d → ℤ :=
  x + ∑ i : Fin n, if (i : ℕ) < k then stepVec d (w i) else 0

/-- The integer walk `w` from `x̃` visits the finite set `D̃ ⊂ ℤ^d` (the start included). -/
abbrev ZWalkMeets (D : Finset (Fin d → ℤ)) (x : Fin d → ℤ) {n : ℕ}
    (w : Fin n → Fin d × Bool) : Prop :=
  ∃ k ∈ Finset.range (n + 1), zWalkPos x w k ∈ D

omit [NeZero m] in
theorem walkPos_intToTorus {n : ℕ} (x : Fin d → ℤ) (w : Fin n → Fin d × Bool) (k : ℕ) :
    walkPos (intToTorus d m x) w k = intToTorus d m (zWalkPos x w k) := by
  unfold walkPos zWalkPos
  rw [map_add, map_sum]

theorem abs_partial_stepSum_le {n : ℕ} (w : Fin n → Fin d × Bool) (k : ℕ) (μ : Fin d) :
    |(∑ i : Fin n, if (i : ℕ) < k then stepVec d (w i) else 0) μ| ≤ n := by
  rw [Finset.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin n, |(if (i : ℕ) < k then stepVec d (w i) else 0) μ|
      ≤ ∑ _i : Fin n, (1 : ℤ) := Finset.sum_le_sum fun i _ => by
        split_ifs
        · exact abs_stepVec_le _ μ
        · simp
    _ = n := by simp

omit [NeZero m] in
theorem zWalkPos_eq_of_intToTorus_eq {n : ℕ} {x z : Fin d → ℤ} (w : Fin n → Fin d × Bool) (k : ℕ)
    (hz : ∀ μ, |z μ - x μ| + n < m)
    (h : intToTorus d m (zWalkPos x w k) = intToTorus d m z) : zWalkPos x w k = z := by
  refine eq_of_intToTorus_eq_of_lt (fun μ => ?_) h
  have h1 := hz μ
  have h2 := abs_le.1 (abs_partial_stepSum_le w k μ)
  have h3 : zWalkPos x w k μ - z μ =
      (∑ i : Fin n, if (i : ℕ) < k then stepVec d (w i) else 0) μ - (z μ - x μ) := by
    simp [zWalkPos]; ring
  rw [h3, abs_lt]
  constructor <;> linarith [le_abs_self (z μ - x μ), neg_abs_le (z μ - x μ)]

omit [NeZero m] in
/-- **T1.**  Under the non-wrapping hypothesis, an `n`-step walk meets the image of `D̃` on the
torus exactly when the integer walk meets `D̃`. -/
theorem walkMeets_image_iff {n : ℕ} {x : Fin d → ℤ} {D : Finset (Fin d → ℤ)}
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m) (w : Fin n → Fin d × Bool) :
    WalkMeets (D.image (intToTorus d m)) (intToTorus d m x) w ↔ ZWalkMeets D x w := by
  constructor
  · rintro ⟨k, hk, hmem⟩
    rw [walkPos_intToTorus, Finset.mem_image] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    exact ⟨k, hk, by rw [zWalkPos_eq_of_intToTorus_eq w k (hD z hz) hzeq.symm]; exact hz⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, hk, by rw [walkPos_intToTorus]; exact Finset.mem_image_of_mem _ h⟩

omit [NeZero m] in
/-- The endpoint condition: under `|ỹ_μ - x̃_μ| + n < m`, the torus walk ends at the image of
`ỹ` iff the integer walk ends at `ỹ`. -/
theorem end_iff {n : ℕ} {x y : Fin d → ℤ} (hy : ∀ μ, |y μ - x μ| + n < m)
    (w : Fin n → Fin d × Bool) :
    intToTorus d m x + intToTorus d m (stepSum w) = intToTorus d m y ↔ x + stepSum w = y := by
  constructor
  · intro h
    rw [← map_add] at h
    refine eq_of_intToTorus_eq_of_lt (fun μ => ?_) h
    have h1 := hy μ
    have h2 := abs_le.1 (abs_stepSum_le w μ)
    have h3 : (x + stepSum w) μ - y μ = stepSum w μ - (y μ - x μ) := by simp; ring
    rw [h3, abs_lt]
    constructor <;> linarith [le_abs_self (y μ - x μ), neg_abs_le (y μ - x μ)]
  · intro h; rw [← map_add, h]

omit [NeZero m] in
theorem intToTorus_not_mem_image {n : ℕ} {x : Fin d → ℤ} {D : Finset (Fin d → ℤ)} (hx : x ∉ D)
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m) :
    intToTorus d m x ∉ D.image (intToTorus d m) := by
  intro h
  obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.1 h
  refine hx ?_
  have : z = x := eq_of_intToTorus_eq_of_lt (fun μ => by
    have := hD z hz μ
    have := abs_nonneg (z μ - x μ)
    have : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    linarith) hzeq
  rwa [← this]

/-! ### T2: the killed-walk counts -/

open Classical in
/-- The number of `n`-step walks in `ℤ^d` from `x̃` to `ỹ` that never visit `D̃`. -/
noncomputable def zKilledCount (d n : ℕ) (x : Fin d → ℤ) (D : Finset (Fin d → ℤ))
    (y : Fin d → ℤ) : ℝ :=
  ∑ w : Fin n → Fin d × Bool, if x + stepSum w = y ∧ ¬ ZWalkMeets D x w then (1 : ℝ) else 0

/-- **T2 (one torus).**  Under the non-wrapping hypothesis, the `(x, y)` entry of `kwAdjG^n` is
the integer count of avoiding walks. -/
theorem kwAdjG_pow_eq_zKilledCount {n : ℕ} {x y : Fin d → ℤ} {D : Finset (Fin d → ℤ)}
    (hx : x ∉ D) (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m) (hy : ∀ μ, |y μ - x μ| + n < m) :
    (kwAdjG d m (D.image (intToTorus d m)) ^ n) (intToTorus d m x) (intToTorus d m y) =
      zKilledCount d n x D y := by
  rw [kwAdjG_pow_eq_count n _ (intToTorus_not_mem_image hx hD), zKilledCount]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact if_congr (and_congr (end_iff hy w) (not_congr (walkMeets_image_iff hD w))) rfl rfl

/-- **T2.**  The killed-walk counts agree on two tori of sides `m, m'` when both are
non-wrapping for `(x̃, ỹ, D̃, n)`. -/
theorem kwAdjG_pow_torus_eq {n : ℕ} {x y : Fin d → ℤ} {D : Finset (Fin d → ℤ)}
    (hx : x ∉ D) (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m)
    (hD' : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m')
    (hy : ∀ μ, |y μ - x μ| + n < m) (hy' : ∀ μ, |y μ - x μ| + n < m') :
    (kwAdjG d m (D.image (intToTorus d m)) ^ n) (intToTorus d m x) (intToTorus d m y) =
      (kwAdjG d m' (D.image (intToTorus d m')) ^ n) (intToTorus d m' x) (intToTorus d m' y) := by
  rw [kwAdjG_pow_eq_zKilledCount hx hD hy, kwAdjG_pow_eq_zKilledCount hx hD' hy']

/-- Path counts of the full torus, in terms of the integer endpoint (no hole). -/
theorem kf0Adj_pow_torus_eq_int {n : ℕ} {x y : Fin d → ℤ}
    (hy : ∀ μ, |y μ - x μ| + n < m) (hy' : ∀ μ, |y μ - x μ| + n < m') :
    (kf0Adj d m ^ n) (intToTorus d m x) (intToTorus d m y) =
      (kf0Adj d m' ^ n) (intToTorus d m' x) (intToTorus d m' y) := by
  rw [kf0Adj_pow_eq_count, kf0Adj_pow_eq_count]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact if_congr ((end_iff hy w).trans (end_iff hy' w).symm) rfl rfl

/-! ### T3: kernels -/

omit [NeZero m] in
private theorem lt_of_le_lt_aux {n R : ℕ} {a : ℤ} (h : n ≤ R) (h2 : a + R < m) : a + n < m := by
  have : (n : ℤ) ≤ R := by exact_mod_cast h
  linarith

/-- **T3 (truncations).**  For any coefficients `c n` (e.g. the walk weights, or the resolvent
weights `a_ν^{-(n+1)}`), the truncated killed-walk sums agree on two non-wrapping tori. -/
theorem sum_range_kwAdjG_pow_torus_eq (c : ℕ → ℝ) {R : ℕ} {x y : Fin d → ℤ}
    {D : Finset (Fin d → ℤ)} (hx : x ∉ D)
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + R < m) (hD' : ∀ z ∈ D, ∀ μ, |z μ - x μ| + R < m')
    (hy : ∀ μ, |y μ - x μ| + R < m) (hy' : ∀ μ, |y μ - x μ| + R < m') :
    ∑ n ∈ Finset.range (R + 1),
        c n * (kwAdjG d m (D.image (intToTorus d m)) ^ n) (intToTorus d m x) (intToTorus d m y) =
      ∑ n ∈ Finset.range (R + 1), c n *
        (kwAdjG d m' (D.image (intToTorus d m')) ^ n) (intToTorus d m' x) (intToTorus d m' y) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  rw [kwAdjG_pow_torus_eq hx (fun z hz μ => lt_of_le_lt_aux hn' (hD z hz μ))
    (fun z hz μ => lt_of_le_lt_aux hn' (hD' z hz μ))
    (fun μ => lt_of_le_lt_aux hn' (hy μ)) (fun μ => lt_of_le_lt_aux hn' (hy' μ))]

/-- Tail of the killed-walk series: `0 ≤ kwC - (partial sum) ≤` the walk tail bound. -/
theorem kwC_sub_sum_range_le {ν : ℝ} (hν : 0 < ν) (D : Finset (Torus d m)) (R : ℕ)
    (x y : Torus d m) :
    0 ≤ kwC d m ν D x y - ∑ n ∈ Finset.range (R + 1),
        walkWeight d ν n * (kwAdjG d m D ^ n) x y ∧
      kwC d m ν D x y - ∑ n ∈ Finset.range (R + 1),
        walkWeight d ν n * (kwAdjG d m D ^ n) x y ≤
      (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
        (1 - 2 * d / (2 * d + ν)) := by
  have hf := kwC_hasSum (D := D) hν x y
  have hg := kf0C_hasSum hν x y
  have hnf : ∀ n, 0 ≤ walkWeight d ν n * (kwAdjG d m D ^ n) x y := fun n =>
    mul_nonneg (walkWeight_pos hν n).le (KW.pow_entry_nonneg (kwAdjG_nonneg D) n x y)
  have hle : ∀ n, walkWeight d ν n * (kwAdjG d m D ^ n) x y ≤
      walkWeight d ν n * (kf0Adj d m ^ n) x y := fun n =>
    mul_le_mul_of_nonneg_left (kwAdjG_pow_le_kf0Adj_pow n x y) (walkWeight_pos hν n).le
  have e1 := hf.summable.sum_add_tsum_nat_add (R + 1)
  have e2 := hg.summable.sum_add_tsum_nat_add (R + 1)
  rw [hf.tsum_eq] at e1
  rw [hg.tsum_eq] at e2
  have hs1 := (summable_nat_add_iff (R + 1)).2 hf.summable
  have hs2 := (summable_nat_add_iff (R + 1)).2 hg.summable
  have t1 : 0 ≤ ∑' i, walkWeight d ν (i + (R + 1)) * (kwAdjG d m D ^ (i + (R + 1))) x y :=
    tsum_nonneg fun i => hnf _
  have t2 : ∑' i, walkWeight d ν (i + (R + 1)) * (kwAdjG d m D ^ (i + (R + 1))) x y ≤
      ∑' i, walkWeight d ν (i + (R + 1)) * (kf0Adj d m ^ (i + (R + 1))) x y :=
    hs1.tsum_le_tsum (fun i => hle _) hs2
  have h3 := (kf0C_sub_kf0CR hν R x y).2
  rw [kf0CR_apply] at h3
  constructor <;> linarith

/-- **T3 (full kernels).**  The killed-walk kernels `kwC` agree on two non-wrapping tori up to
one walk tail at `R`. -/
theorem abs_kwC_sub_le {ν : ℝ} (hν : 0 < ν) {R : ℕ} {x y : Fin d → ℤ}
    {D : Finset (Fin d → ℤ)} (hx : x ∉ D)
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + R < m) (hD' : ∀ z ∈ D, ∀ μ, |z μ - x μ| + R < m')
    (hy : ∀ μ, |y μ - x μ| + R < m) (hy' : ∀ μ, |y μ - x μ| + R < m') :
    |kwC d m ν (D.image (intToTorus d m)) (intToTorus d m x) (intToTorus d m y) -
        kwC d m' ν (D.image (intToTorus d m')) (intToTorus d m' x) (intToTorus d m' y)| ≤
      (Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
        (1 - 2 * d / (2 * d + ν)) := by
  have a := kwC_sub_sum_range_le hν (D.image (intToTorus d m)) R (intToTorus d m x)
    (intToTorus d m y)
  have b := kwC_sub_sum_range_le hν (D.image (intToTorus d m')) R (intToTorus d m' x)
    (intToTorus d m' y)
  have c := sum_range_kwAdjG_pow_torus_eq (walkWeight d ν) hx hD hD' hy hy'
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- **T3 (hole walks).**  The difference `kf0C - kwC` (walks that meet the bad set) agrees on two
non-wrapping tori up to twice the walk tail. -/
theorem abs_kf0C_sub_kwC_sub_le {ν : ℝ} (hν : 0 < ν) {R : ℕ} {x y : Fin d → ℤ}
    {D : Finset (Fin d → ℤ)} (hx : x ∉ D)
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + R < m) (hD' : ∀ z ∈ D, ∀ μ, |z μ - x μ| + R < m')
    (hy : ∀ μ, |y μ - x μ| + R < m) (hy' : ∀ μ, |y μ - x μ| + R < m') :
    |(kf0C d m ν (intToTorus d m x) (intToTorus d m y) -
          kwC d m ν (D.image (intToTorus d m)) (intToTorus d m x) (intToTorus d m y)) -
        (kf0C d m' ν (intToTorus d m' x) (intToTorus d m' y) -
          kwC d m' ν (D.image (intToTorus d m')) (intToTorus d m' x) (intToTorus d m' y))| ≤
      2 * ((Real.sqrt (2 * d + ν))⁻¹ * (2 * d / (2 * d + ν)) ^ (R + 1) /
        (1 - 2 * d / (2 * d + ν))) := by
  have a := kwC_sub_sum_range_le hν (D.image (intToTorus d m)) R (intToTorus d m x)
    (intToTorus d m y)
  have b := kwC_sub_sum_range_le hν (D.image (intToTorus d m')) R (intToTorus d m' x)
    (intToTorus d m' y)
  have a' := kf0C_sub_kf0CR hν R (intToTorus d m x) (intToTorus d m y)
  have b' := kf0C_sub_kf0CR hν R (intToTorus d m' x) (intToTorus d m' y)
  have c := sum_range_kwAdjG_pow_torus_eq (walkWeight d ν) hx hD hD' hy hy'
  have c' : kf0CR d m ν R (intToTorus d m x) (intToTorus d m y) =
      kf0CR d m' ν R (intToTorus d m' x) (intToTorus d m' y) := by
    rw [kf0CR_apply, kf0CR_apply]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rw [kf0Adj_pow_torus_eq_int (fun μ => lt_of_le_lt_aux hn' (hy μ))
      (fun μ => lt_of_le_lt_aux hn' (hy' μ))]
  rw [abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2, a'.1, a'.2, b'.1, b'.2]

/-! ### T4: rooted loop counts -/

/-- The number of closed `n`-step walks in `ℤ^d` rooted at `x̃` that visit `D̃`. -/
noncomputable def zRootedLoopCount (d n : ℕ) (x : Fin d → ℤ) (D : Finset (Fin d → ℤ)) : ℝ := by
  classical
  exact ∑ w : Fin n → Fin d × Bool, if stepSum w = 0 ∧ ZWalkMeets D x w then (1 : ℝ) else 0

/-- The number of closed `n`-step walks on the torus rooted at `x` that visit `D`: the summand of
`kwTraceDiff_eq_count` at the root `x`. -/
noncomputable def kwRootedLoopCount (d m : ℕ) [NeZero m] (D : Finset (Torus d m)) (n : ℕ)
    (x : Torus d m) : ℝ :=
  ∑ w : Fin n → Fin d × Bool,
    if x + intToTorus d m (stepSum w) = x ∧ WalkMeets D x w then (1 : ℝ) else 0

/-- The loop term `kwTraceDiff` is the sum over all roots of the rooted counts. -/
theorem kwTraceDiff_eq_sum_rooted (D : Finset (Torus d m)) {n : ℕ} (hn : 0 < n) :
    kwTraceDiff d m D n = ∑ x : Torus d m, kwRootedLoopCount d m D n x :=
  kwTraceDiff_eq_count hn

/-- **T4 (one torus).**  The rooted count at `intToTorus x̃` is the integer count. -/
theorem kwRootedLoopCount_eq {n : ℕ} {x : Fin d → ℤ} {D : Finset (Fin d → ℤ)}
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m) (hn : n < m) :
    kwRootedLoopCount d m (D.image (intToTorus d m)) n (intToTorus d m x) =
      zRootedLoopCount d n x D := by
  classical
  rw [kwRootedLoopCount, zRootedLoopCount]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hy : ∀ μ, |x μ - x μ| + n < m := fun μ => by simpa using hn
  refine if_congr (and_congr ?_ (walkMeets_image_iff hD w)) rfl rfl
  have := end_iff hy w
  simpa using this

/-- **T4.**  The rooted loop counts agree on two tori that are non-wrapping for `(x̃, D̃, n)`. -/
theorem kwRootedLoopCount_torus_eq {n : ℕ} {x : Fin d → ℤ} {D : Finset (Fin d → ℤ)}
    (hD : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m) (hD' : ∀ z ∈ D, ∀ μ, |z μ - x μ| + n < m')
    (hn : n < m) (hn' : n < m') :
    kwRootedLoopCount d m (D.image (intToTorus d m)) n (intToTorus d m x) =
      kwRootedLoopCount d m' (D.image (intToTorus d m')) n (intToTorus d m' x) := by
  rw [kwRootedLoopCount_eq hD hn, kwRootedLoopCount_eq hD' hn']

/-! ### T5: an instance -/

/-- `d = 3`, sides `9` and `27`, `D̃ = {0}`, `x̃ = ỹ = e₀`, `n = 2`: the killed-walk entries
agree and are positive (there is a closed 2-step walk `e₀ → e₀ + e₁ → e₀` avoiding `0`). -/
theorem kwAdjG_pow_torus_instance :
    haveI : NeZero 9 := ⟨by norm_num⟩
    haveI : NeZero 27 := ⟨by norm_num⟩
    (kwAdjG 3 9 (({0} : Finset (Fin 3 → ℤ)).image (intToTorus 3 9)) ^ 2)
        (intToTorus 3 9 (Pi.single 0 1)) (intToTorus 3 9 (Pi.single 0 1)) =
      (kwAdjG 3 27 (({0} : Finset (Fin 3 → ℤ)).image (intToTorus 3 27)) ^ 2)
        (intToTorus 3 27 (Pi.single 0 1)) (intToTorus 3 27 (Pi.single 0 1)) ∧
    0 < (kwAdjG 3 9 (({0} : Finset (Fin 3 → ℤ)).image (intToTorus 3 9)) ^ 2)
        (intToTorus 3 9 (Pi.single 0 1)) (intToTorus 3 9 (Pi.single 0 1)) := by
  classical
  have h9 : NeZero 9 := ⟨by norm_num⟩
  have h27 : NeZero 27 := ⟨by norm_num⟩
  have hx : (Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) ∉ ({0} : Finset (Fin 3 → ℤ)) := by
    simp only [Finset.mem_singleton]
    intro h
    have := congrFun h 0
    simp at this
  have hb : ∀ M : ℕ, 2 + 2 < M → ∀ μ : Fin 3,
      |(0 : Fin 3 → ℤ) μ - (Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) μ| + (2 : ℕ) < (M : ℤ) := by
    intro M hM μ
    by_cases h : μ = 0 <;> simp [h] <;> omega
  have hy : ∀ M : ℕ, 2 + 2 < M → ∀ μ : Fin 3,
      |(Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) μ - (Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) μ|
        + (2 : ℕ) < (M : ℤ) := by
    intro M hM μ
    simp; omega
  have e1 := kwAdjG_pow_eq_zKilledCount (m := 9) (n := 2) hx
    (by simpa using fun μ => hb 9 (by norm_num) μ) (hy 9 (by norm_num))
  have e2 := kwAdjG_pow_eq_zKilledCount (m := 27) (n := 2) hx
    (by simpa using fun μ => hb 27 (by norm_num) μ) (hy 27 (by norm_num))
  refine ⟨by rw [e1, e2], ?_⟩
  rw [e1, zKilledCount]
  have hnn : ∀ w : Fin 2 → Fin 3 × Bool, 0 ≤ (if Pi.single (0 : Fin 3) (1 : ℤ) + stepSum w =
      Pi.single (0 : Fin 3) (1 : ℤ) ∧ ¬ ZWalkMeets ({0} : Finset (Fin 3 → ℤ))
        (Pi.single (0 : Fin 3) (1 : ℤ)) w then (1 : ℝ) else 0) := fun w => by
    split_ifs <;> norm_num
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun w _ => hnn w)
    (Finset.mem_univ (![(1, true), (1, false)] : Fin 2 → Fin 3 × Bool)))
  have hc : Pi.single (0 : Fin 3) (1 : ℤ) + stepSum (![(1, true), (1, false)] : Fin 2 → Fin 3 × Bool) =
      Pi.single (0 : Fin 3) (1 : ℤ) ∧ ¬ ZWalkMeets ({0} : Finset (Fin 3 → ℤ))
        (Pi.single (0 : Fin 3) (1 : ℤ)) (![(1, true), (1, false)] : Fin 2 → Fin 3 × Bool) := by
    constructor
    · ext μ
      simp [stepSum, Fin.sum_univ_two, stepVec]
    · rintro ⟨k, hk, hmem⟩
      simp only [Finset.mem_singleton] at hmem
      have h0 := congrFun hmem 0
      have h1 := congrFun hmem 1
      simp [zWalkPos, Fin.sum_univ_two, stepVec] at h0 h1
      split_ifs at h0 h1 <;> simp_all
  simp only [hc]
  norm_num

end Balaban.Green
