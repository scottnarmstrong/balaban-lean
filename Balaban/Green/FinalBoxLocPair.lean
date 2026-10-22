/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalBoxLocTies
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The pair terms of a quadratic form in polymer form (A6-3, the undilated part of the box)

The mismatch `Q = Lᵀ D L - 1` of the localized square root enters the box integral as the even
quadratic factor `exp(-½⟨w, Q w⟩)`.  Its local form puts the pair term `-½ Q(p, q) w_p w_q` on the
blocks of the path `macPath p q` (the axis-parallel shortest path of the macro cover):

* `segPt`, `mem_macPath_iff`: the points of the path are the points of its `d` segments;
* `isAnimal_macPathF`: the path is a connected set of blocks;
* `macCellCount_macPathF_le`: it meets at most `16^d + 9 d 7^d + 7^d |p - q| / M` macro cells
  (`macTags_card_le`);
* `pairLocal Q Y w`, `sum_pairLocal`: `∑_Y pairLocal Q Y w = -½ ⟨w, Q w⟩`; locality
  (`pairLocal_congr`), support on connected sets (`pairLocal_eq_zero_of_not_isAnimal`), evenness
  (`pairLocal_neg`), continuity (`continuous_pairLocal`);
* `pairLocal_bound`: for entries `|Q(p, q)| ≤ ε_Q e^{-r |p - q|}`, `|w| ≤ p₁` and the cell weight
  `e^{α #cells}`, `∑_{Y ∋ x} |pairLocal Q Y w| e^{α #cells(Y)} ≤
  ½ ε_Q p₁² e^{α H_d} (N ballConst(ρ))²`, `ρ = r - α 7^d / M > 0` (`macPath_geodesic`).
-/

@[expose] public section

namespace Balaban.Green

open Finset

section Path

variable {d m : ℕ} [NeZero m]

/-- The points of the `k`-th segment of the path from `x` to `y`: coordinates `i < k` equal
`y i`, coordinates `i > k` equal `x i`, and coordinate `k` is `x k + e`. -/
def segPt (x y : Balaban.Torus d m) (k : Fin d) (e : ℤ) : Balaban.Torus d m :=
  fun i => if i < k then y i else if i = k then x i + (e : ZMod m) else x i

omit [NeZero m] in
theorem segPt_mem_macPath (x y : Balaban.Torus d m) (k : Fin d) {e : ℤ}
    (he : e ∈ Finset.Icc (min 0 (cycRep (y k - x k))) (max 0 (cycRep (y k - x k)))) :
    (segPt x y k e : L1Torus d m) ∈ macPath d m x y := by
  refine ⟨k, fun i hi => by simp [segPt, hi], fun i hi => ?_, ?_⟩
  · have h1 : ¬ i < k := fun h => absurd (h.trans hi) (lt_irrefl _)
    have h2 : i ≠ k := fun h => absurd (h ▸ hi) (lt_irrefl _)
    simp [segPt, h1, h2]
  · simp only [segPt, lt_irrefl, ↓reduceIte]
    exact Finset.mem_image.2 ⟨e, he, rfl⟩

omit [NeZero m] in
theorem exists_segPt_of_mem_macPath {x y : Balaban.Torus d m} {p : Balaban.Torus d m}
    (hp : (p : L1Torus d m) ∈ macPath d m x y) :
    ∃ k : Fin d, ∃ e ∈ Finset.Icc (min 0 (cycRep (y k - x k))) (max 0 (cycRep (y k - x k))),
      p = segPt x y k e := by
  obtain ⟨k, h1, h2, h3⟩ := hp
  obtain ⟨e, he, hpe⟩ := Finset.mem_image.1 h3
  refine ⟨k, e, he, funext fun i => ?_⟩
  rcases lt_trichotomy i k with c | c | c
  · simp [segPt, c, h1 i c]
  · subst c; simp [segPt, hpe]
  · have c1 : ¬ i < k := fun h => absurd (h.trans c) (lt_irrefl _)
    have c2 : i ≠ k := fun h => absurd (h ▸ c) (lt_irrefl _)
    simp [segPt, c1, c2, h2 i c]

omit [NeZero m] in
theorem segPt_succ (x y : Balaban.Torus d m) (k : Fin d) (e : ℤ) :
    segPt x y k (e + 1) = segPt x y k e + Pi.single k 1 := by
  funext i
  by_cases hik : i = k
  · subst hik; simp [segPt]; ring
  · by_cases hlt : i < k <;> simp [segPt, hik, hlt]

omit [NeZero m] in
theorem segPt_zero_val (x y : Balaban.Torus d m) {k : Fin d} (hk : k.val = 0) :
    segPt x y k 0 = x := by
  funext i
  have h1 : ¬ i < k := by rw [Fin.lt_def, hk]; omega
  by_cases hik : i = k <;> simp [segPt, h1, hik]

theorem segPt_end_eq (x y : Balaban.Torus d m) {k k' : Fin d} (hk : k'.val = k.val + 1) :
    segPt x y k (cycRep (y k - x k)) = segPt x y k' 0 := by
  funext i
  have hlt' : i < k' ↔ i ≤ k := by rw [Fin.lt_def, Fin.le_def, hk]; omega
  by_cases hik : i = k
  · subst hik
    have : i < k' := hlt'.2 le_rfl
    simp [segPt, this, cast_cycRep]
  · by_cases hlt : i < k
    · have : i < k' := hlt'.2 hlt.le
      simp [segPt, hlt, this]
    · have h2 : ¬ i < k' := fun h => hik (le_antisymm (hlt'.1 h) (not_lt.1 hlt))
      by_cases h3 : i = k'
      · subst h3; simp [segPt, hlt, hik]
      · simp [segPt, hlt, hik, h2, h3]

open Classical in
/-- The blocks of the path from `x` to `y`. -/
noncomputable def macPathF (d m : ℕ) [NeZero m] (x y : Balaban.Torus d m) :
    Finset (Balaban.Torus d m) :=
  Finset.univ.filter fun p => (p : L1Torus d m) ∈ macPath d m x y

theorem mem_macPathF {x y p : Balaban.Torus d m} :
    p ∈ macPathF d m x y ↔ (p : L1Torus d m) ∈ macPath d m x y := by
  classical
  unfold macPathF
  simp

/-- The induced step of the path graph. -/
private def PStep (X : Finset (Balaban.Torus d m)) (a b : Balaban.Torus d m) : Prop :=
  a ∈ X ∧ b ∈ X ∧ (Polymer.blockGraph d m).Adj a b

omit [NeZero m] in
private theorem pstep_single {X : Finset (Balaban.Torus d m)} {a : Balaban.Torus d m} (k : Fin d)
    (ha : a ∈ X) (hb : a + Pi.single k 1 ∈ X) :
    Relation.ReflTransGen (PStep X) a (a + Pi.single k 1) := by
  by_cases hab : a + Pi.single k 1 = a
  · rw [hab]
  · exact Relation.ReflTransGen.single ⟨ha, hb, Ne.symm hab, k, Or.inl rfl⟩

omit [NeZero m] in
private theorem pstep_symm {X : Finset (Balaban.Torus d m)} {a b : Balaban.Torus d m}
    (h : Relation.ReflTransGen (PStep X) a b) : Relation.ReflTransGen (PStep X) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩ ih

private theorem seg_chain (x y : Balaban.Torus d m) (k : Fin d) {e : ℤ}
    (he : e ∈ Finset.Icc (min 0 (cycRep (y k - x k))) (max 0 (cycRep (y k - x k)))) :
    Relation.ReflTransGen (PStep (macPathF d m x y)) (segPt x y k 0) (segPt x y k e) := by
  set c := cycRep (y k - x k)
  have hmem : ∀ e', min 0 c ≤ e' → e' ≤ max 0 c → segPt x y k e' ∈ macPathF d m x y :=
    fun e' h1 h2 => mem_macPathF.2 (segPt_mem_macPath x y k (Finset.mem_Icc.2 ⟨h1, h2⟩))
  obtain ⟨he1, he2⟩ := Finset.mem_Icc.1 he
  rcases le_or_gt 0 e with h0 | h0
  · revert he2
    refine Int.leInduction (m := 0) (motive := fun e _ => e ≤ max 0 c →
      Relation.ReflTransGen (PStep (macPathF d m x y)) (segPt x y k 0) (segPt x y k e))
      (fun _ => Relation.ReflTransGen.refl) (fun j hj ih hj1 => ?_) e h0
    have hj' : j ≤ max 0 c := by linarith
    refine (ih hj').trans ?_
    rw [segPt_succ]
    exact pstep_single k (hmem j ((min_le_left _ _).trans hj) hj')
      (by rw [← segPt_succ]; exact hmem (j + 1) ((min_le_left _ _).trans (by linarith)) hj1)
  · revert he1
    refine Int.leInductionDown (m := 0) (motive := fun e _ => min 0 c ≤ e →
      Relation.ReflTransGen (PStep (macPathF d m x y)) (segPt x y k 0) (segPt x y k e))
      (fun _ => Relation.ReflTransGen.refl) (fun j hj ih hj1 => ?_) e h0.le
    have hj' : min 0 c ≤ j := by linarith
    refine (ih hj').trans (pstep_symm ?_)
    have e1 : segPt x y k j = segPt x y k (j - 1) + Pi.single k 1 := by
      rw [← segPt_succ, sub_add_cancel]
    rw [e1]
    exact pstep_single k (hmem (j - 1) hj1 (by linarith [le_max_left 0 c]))
      (by rw [← e1]; exact hmem j hj' (hj.trans (le_max_left _ _)))

private theorem start_chain (x y : Balaban.Torus d m) :
    ∀ (j : ℕ) (hj : j < d),
      Relation.ReflTransGen (PStep (macPathF d m x y)) x (segPt x y ⟨j, hj⟩ 0) := by
  intro j
  induction j with
  | zero => intro hj; rw [segPt_zero_val x y (k := ⟨0, hj⟩) rfl]
  | succ j ih =>
    intro hj
    have hj' : j < d := by omega
    have h1 := ih hj'
    have h2 := seg_chain x y ⟨j, hj'⟩ (e := cycRep (y ⟨j, hj'⟩ - x ⟨j, hj'⟩))
      (Finset.mem_Icc.2 ⟨min_le_right _ _, le_max_right _ _⟩)
    rw [segPt_end_eq x y (k := ⟨j, hj'⟩) (k' := ⟨j + 1, hj⟩) rfl] at h2
    exact h1.trans h2

/-- **The path from `x` to `y` is a connected set of blocks.** -/
theorem isAnimal_macPathF (hd : 0 < d) (x y : Balaban.Torus d m) :
    Polymer.IsAnimal (Polymer.blockGraph d m) (macPathF d m x y) := by
  rw [Polymer.isAnimal_iff]
  have hx : x ∈ macPathF d m x y := mem_macPathF.2 (macPath_start hd x y)
  have hall : ∀ p ∈ macPathF d m x y,
      Relation.ReflTransGen (PStep (macPathF d m x y)) x p := by
    intro p hp
    obtain ⟨k, e, he, rfl⟩ := exists_segPt_of_mem_macPath (mem_macPathF.1 hp)
    exact (start_chain x y k.val k.2).trans (seg_chain x y k he)
  exact ⟨⟨x, hx⟩, fun a ha b hb => (pstep_symm (hall a ha)).trans (hall b hb)⟩

/-- The `ℓ¹` distance of two blocks (the metric of `L1Torus`). -/
noncomputable abbrev bdist (x y : Balaban.Torus d m) : ℝ := @dist (L1Torus d m) _ x y

/-- **The cells of the path**: at most `16^d + 9 d 7^d + 7^d |x - y| / M` macro cells meet it. -/
theorem macCellCount_macPathF_le {M : ℕ} (hM : 0 < M) (z : MacIdx d m M)
    (x y : Balaban.Torus d m) :
    (macCellCount d m M (macPathF d m x y) : ℝ) ≤
      (16 ^ d + 9 * d * 7 ^ d) + 7 ^ d * (bdist x y / M) := by
  classical
  refine le_trans ?_ (macTags_card_le hM z x y)
  unfold macCellCount
  refine Nat.cast_le.2 (Finset.card_le_card fun w hw => ?_)
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨p, mem_macPathF.1 hp,
    macCore_subset_box _ hM (mem_macCore_macZ p)⟩⟩

end Path

section Pair

variable {d m N : ℕ} [NeZero m]

open Classical in
/-- **The pair terms of a quadratic form on a set of blocks**: `-½ ∑ Q(p, q) w_p w_q` over the
pairs whose path is `Y`. -/
noncomputable def pairLocal (Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ)
    (Y : Finset (Balaban.Torus d m)) (w : Balaban.Torus d m × Fin N → ℝ) : ℝ :=
  -(1 / 2) * ∑ pq ∈ Finset.univ.filter
      (fun pq : (Balaban.Torus d m × Fin N) × (Balaban.Torus d m × Fin N) =>
        macPathF d m pq.1.1 pq.2.1 = Y), Q pq.1 pq.2 * w pq.1 * w pq.2

/-- **The pair terms sum to the quadratic form**: `∑_Y pairLocal Q Y w = -½ ⟨w, Q w⟩`. -/
theorem sum_pairLocal (Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ)
    (w : Balaban.Torus d m × Fin N → ℝ) :
    ∑ Y, pairLocal Q Y w = -(1 / 2) * ∑ p, ∑ q, Q p q * w p * w q := by
  classical
  unfold pairLocal
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_fiberwise Finset.univ (fun pq : (Balaban.Torus d m × Fin N) ×
    (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1)
    (fun pq => Q pq.1 pq.2 * w pq.1 * w pq.2)).trans (Fintype.sum_prod_type _)

/-- **Locality**: `pairLocal Q Y` reads `w` on `Y × Fin N` only (`0 < d`). -/
theorem pairLocal_congr (hd : 0 < d)
    (Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ)
    (Y : Finset (Balaban.Torus d m)) {w w' : Balaban.Torus d m × Fin N → ℝ}
    (hww : ∀ x ∈ Y, ∀ i, w (x, i) = w' (x, i)) : pairLocal Q Y w = pairLocal Q Y w' := by
  classical
  unfold pairLocal
  congr 1
  refine Finset.sum_congr rfl fun pq hpq => ?_
  have hY := (Finset.mem_filter.1 hpq).2
  have h1 : pq.1.1 ∈ Y := hY ▸ mem_macPathF.2 (macPath_start hd _ _)
  have h2 : pq.2.1 ∈ Y := hY ▸ mem_macPathF.2 (macPath_end hd _ _)
  rw [hww _ h1 pq.1.2, hww _ h2 pq.2.2]

/-- **Support**: `pairLocal Q Y = 0` unless `Y` is a nonempty connected set of blocks. -/
theorem pairLocal_eq_zero_of_not_isAnimal (hd : 0 < d)
    (Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ)
    {Y : Finset (Balaban.Torus d m)} (hY : ¬ Polymer.IsAnimal (Polymer.blockGraph d m) Y)
    (w : Balaban.Torus d m × Fin N → ℝ) : pairLocal Q Y w = 0 := by
  classical
  unfold pairLocal
  rw [Finset.sum_eq_zero, mul_zero]
  intro pq hpq
  have h := isAnimal_macPathF hd pq.1.1 pq.2.1
  rw [(Finset.mem_filter.1 hpq).2] at h
  exact absurd h hY

/-- **Evenness**: `pairLocal Q Y (-w) = pairLocal Q Y w`. -/
theorem pairLocal_neg (Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ)
    (Y : Finset (Balaban.Torus d m)) (w : Balaban.Torus d m × Fin N → ℝ) :
    pairLocal Q Y (-w) = pairLocal Q Y w := by
  unfold pairLocal
  simp only [Pi.neg_apply, mul_neg, neg_mul, neg_neg]

/-- **Continuity** in `w`. -/
theorem continuous_pairLocal
    (Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ)
    (Y : Finset (Balaban.Torus d m)) : Continuous (pairLocal Q Y) := by
  classical
  unfold pairLocal
  refine continuous_const.mul (continuous_finsetSum _ fun pq _ => ?_)
  exact (continuous_const.mul (continuous_apply _)).mul (continuous_apply _)

theorem dist_split_of_mem_macPath {x y p : Balaban.Torus d m}
    (hp : (p : L1Torus d m) ∈ macPath d m x y) :
    bdist x y = bdist x p + bdist p y :=
  (macPath_geodesic hp).symm

/-- **The summed bound of the pair terms**: for `|Q(p, q)| ≤ ε_Q e^{-r |p - q|}`, `|w| ≤ p₁`,
`α ≥ 0`, macro side `M` and `ρ = r - α 7^d / M > 0`,
`∑_{Y ∋ x} |pairLocal Q Y w| e^{α #cells(Y)} ≤ ½ ε_Q p₁² e^{α (16^d + 9 d 7^d)} (N ballConst ρ)²`. -/
theorem pairLocal_bound {M : ℕ} (hM : 0 < M)
    {Q : Balaban.Torus d m × Fin N → Balaban.Torus d m × Fin N → ℝ} {εQ r α p1 : ℝ}
    (hεQ : 0 ≤ εQ) (hQ : ∀ p q, |Q p q| ≤ εQ * Real.exp (-r * bdist p.1 q.1))
    (hα : 0 ≤ α) (hρ : 0 < r - α * 7 ^ d / M) (hp1 : 0 ≤ p1)
    {w : Balaban.Torus d m × Fin N → ℝ} (hw : ∀ p, |w p| ≤ p1) (x : Balaban.Torus d m) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset (Balaban.Torus d m) => x ∈ Y),
        |pairLocal Q Y w| * Real.exp (α * (macCellCount d m M Y : ℝ)) ≤
      1 / 2 * εQ * p1 ^ 2 * Real.exp (α * (16 ^ d + 9 * d * 7 ^ d)) *
        (N * ballConst d (r - α * 7 ^ d / M)) ^ 2 := by
  classical
  set ρ := r - α * 7 ^ d / M with hρdef
  set H : ℝ := 16 ^ d + 9 * d * 7 ^ d with hH
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set z0 : MacIdx d m M := fun _ => ⟨0, lt_of_lt_of_le zero_lt_one (le_max_left _ _)⟩
  set c0 : ℝ := 1 / 2 * εQ * p1 ^ 2 * Real.exp (α * H) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  -- the term of a pair
  set F : (Balaban.Torus d m × Fin N) × (Balaban.Torus d m × Fin N) → ℝ := fun pq =>
    c0 * (Real.exp (-ρ * bdist pq.1.1 x) *
      Real.exp (-ρ * bdist x pq.2.1)) with hF
  have hF0 : ∀ pq, 0 ≤ F pq := fun pq => by positivity
  have hterm : ∀ pq : (Balaban.Torus d m × Fin N) × (Balaban.Torus d m × Fin N),
      x ∈ macPathF d m pq.1.1 pq.2.1 →
      1 / 2 * (|Q pq.1 pq.2| * |w pq.1| * |w pq.2|) *
        Real.exp (α * (macCellCount d m M (macPathF d m pq.1.1 pq.2.1) : ℝ)) ≤ F pq := by
    intro pq hx
    have hdist := dist_split_of_mem_macPath (mem_macPathF.1 hx)
    have hcc := macCellCount_macPathF_le hM z0 pq.1.1 pq.2.1
    have hw2 : |w pq.1| * |w pq.2| ≤ p1 ^ 2 := by
      rw [sq]; exact mul_le_mul (hw _) (hw _) (abs_nonneg _) hp1
    have hexp : Real.exp (α * (macCellCount d m M (macPathF d m pq.1.1 pq.2.1) : ℝ)) ≤
        Real.exp (α * H) * Real.exp (α * 7 ^ d / M * bdist pq.1.1 pq.2.1) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 := mul_le_mul_of_nonneg_left hcc hα
      have e : α * ((16 ^ d + 9 * d * 7 ^ d) + 7 ^ d * (bdist pq.1.1 pq.2.1 / M)) =
          α * H + α * 7 ^ d / M * bdist pq.1.1 pq.2.1 := by
        rw [hH]; field_simp
      linarith
    have hQe := hQ pq.1 pq.2
    have hsplit : Real.exp (-r * bdist pq.1.1 pq.2.1) *
        Real.exp (α * 7 ^ d / M * bdist pq.1.1 pq.2.1) =
        Real.exp (-ρ * bdist pq.1.1 x) *
          Real.exp (-ρ * bdist x pq.2.1) := by
      rw [← Real.exp_add, ← Real.exp_add, hdist, hρdef]
      congr 1; ring
    calc 1 / 2 * (|Q pq.1 pq.2| * |w pq.1| * |w pq.2|) *
          Real.exp (α * (macCellCount d m M (macPathF d m pq.1.1 pq.2.1) : ℝ))
        ≤ 1 / 2 * (εQ * Real.exp (-r * bdist pq.1.1 pq.2.1) * p1 ^ 2) *
          (Real.exp (α * H) *
            Real.exp (α * 7 ^ d / M * bdist pq.1.1 pq.2.1)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hexp (by positivity)
            (by positivity)
          rw [mul_assoc]
          exact mul_le_mul hQe hw2 (by positivity) (by positivity)
      _ = c0 * (Real.exp (-r * bdist pq.1.1 pq.2.1) *
            Real.exp (α * 7 ^ d / M * bdist pq.1.1 pq.2.1)) := by
          rw [hc0]; ring
      _ = F pq := by rw [hsplit]
  -- the bound on each set of blocks through `x`
  have hY : ∀ Y ∈ Finset.univ.filter (fun Y : Finset (Balaban.Torus d m) => x ∈ Y),
      |pairLocal Q Y w| * Real.exp (α * (macCellCount d m M Y : ℝ)) ≤
        ∑ pq ∈ Finset.univ.filter (fun pq : (Balaban.Torus d m × Fin N) ×
          (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1 = Y), F pq := by
    intro Y hY
    have hxY := (Finset.mem_filter.1 hY).2
    unfold pairLocal
    rw [abs_mul, abs_of_neg (by norm_num : -(1 / 2 : ℝ) < 0), neg_neg]
    calc 1 / 2 * |∑ pq ∈ Finset.univ.filter (fun pq : (Balaban.Torus d m × Fin N) ×
            (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1 = Y),
            Q pq.1 pq.2 * w pq.1 * w pq.2| * Real.exp (α * (macCellCount d m M Y : ℝ))
        ≤ ∑ pq ∈ Finset.univ.filter (fun pq : (Balaban.Torus d m × Fin N) ×
            (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1 = Y),
            1 / 2 * (|Q pq.1 pq.2| * |w pq.1| * |w pq.2|) *
              Real.exp (α * (macCellCount d m M Y : ℝ)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)) (by norm_num))
            (Real.exp_pos _).le
          refine Finset.sum_congr rfl fun pq _ => ?_
          rw [abs_mul, abs_mul]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun pq hpq => ?_
          have hpY := (Finset.mem_filter.1 hpq).2
          have := hterm pq (hpY ▸ hxY)
          rwa [hpY] at this
  refine (Finset.sum_le_sum hY).trans ?_
  -- drop the condition `x ∈ Y` and sum over all pairs
  have hdrop : ∑ Y ∈ Finset.univ.filter (fun Y : Finset (Balaban.Torus d m) => x ∈ Y),
      ∑ pq ∈ Finset.univ.filter (fun pq : (Balaban.Torus d m × Fin N) ×
        (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1 = Y), F pq ≤
      ∑ Y : Finset (Balaban.Torus d m),
        ∑ pq ∈ Finset.univ.filter (fun pq : (Balaban.Torus d m × Fin N) ×
          (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1 = Y), F pq :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun Y _ _ => Finset.sum_nonneg fun pq _ => hF0 pq
  refine hdrop.trans ?_
  rw [Finset.sum_fiberwise_of_maps_to (g := fun pq : (Balaban.Torus d m × Fin N) ×
    (Balaban.Torus d m × Fin N) => macPathF d m pq.1.1 pq.2.1) (fun _ _ => Finset.mem_univ _)]
  have hsum1 : ∑ p : Balaban.Torus d m × Fin N, Real.exp (-ρ * bdist p.1 x) ≤
      N * ballConst d ρ := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_)) (ballSum_L1Torus d m hρ x)
    exact congrArg (fun t => Real.exp (-ρ * t)) (dist_comm (α := L1Torus d m) y x)
  have hsum2 : ∑ q : Balaban.Torus d m × Fin N, Real.exp (-ρ * bdist x q.1) ≤
      N * ballConst d ρ := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ballSum_L1Torus d m hρ x) (Nat.cast_nonneg _)
  have e : ∑ pq : (Balaban.Torus d m × Fin N) × (Balaban.Torus d m × Fin N), F pq =
      c0 * ((∑ p : Balaban.Torus d m × Fin N, Real.exp (-ρ * bdist p.1 x)) *
        ∑ q : Balaban.Torus d m × Fin N, Real.exp (-ρ * bdist x q.1)) := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
  rw [e, sq]
  refine mul_le_mul_of_nonneg_left (mul_le_mul hsum1 hsum2
    (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (by
      have := ballConst_decay_nonneg (d := d) hρ
      positivity)) hc00

end Pair

end Balaban.Green
