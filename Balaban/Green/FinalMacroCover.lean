/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.BallSums
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The macro cover of the torus (FINALFAM leaf 1, geometry only)

This is the geometry for the construction proposed in `notes/phase1/FINALFAM.md` §4 (the papers
print no formula; author question 18 is pending).  Nothing analytic is claimed.

Fix a scale `M ≥ 1` and the torus `L1Torus d m` (side `m ≥ 1`, `ℓ¹` torus metric).  In each
coordinate the residues `0, …, m-1` are cut into `K = max 1 (m / M)` consecutive intervals:
`[jM, (j+1)M)` for `j < K-1`, and `[(K-1)M, m)` for the last one.  Hence `K = 1` when `m < 2M`
(the small-torus case: one cell, equal to the whole torus), and otherwise every interval has
between `M` and `2M - 1` points.

* cells `z : Fin d → Fin K`, cores `C_z` (products of intervals; they partition the torus);
* boxes `B_z = {x : dist(x, C_z) < 2M}`; a site lies in at most `7^d` boxes, and
  `x ∈ C_z`, `y ∉ B_z` imply `dist x y ≥ 2M`;
* `φ_z(x) = max 0 (1 - dist(x, C_z)/M)` and `χ_z = φ_z / ∑_w φ_w`:
  `0 ≤ χ_z ≤ 1`, `∑ χ_z = 1`, `χ_z x ≠ 0 → dist(x, C_z) < M` (so `χ_z` vanishes within distance
  `M` of the complement of `B_z`), and `|χ_z x - χ_z y| ≤ (1 + 2·7^d) dist x y / M`.
-/

@[expose] public section

open Finset

namespace Balaban.Green

section OneDim

variable (m M : ℕ) [NeZero m]

/-- Number of cells per coordinate. -/
def macK : ℕ := max 1 (m / M)

omit [NeZero m] in
lemma macK_pos : 0 < macK m M := by unfold macK; omega

/-- The cell (interval) containing a residue. -/
def macCell (v : ZMod m) : Fin (macK m M) :=
  ⟨min (v.val / M) (macK m M - 1), by have := macK_pos m M; omega⟩

variable {m M}

omit [NeZero m] in
lemma macK_eq_one_of_lt (h : m < 2 * M) : macK m M = 1 := by
  unfold macK
  have : m / M < 2 := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · exact (Nat.div_lt_iff_lt_mul hM).2 (by omega)
  omega

omit [NeZero m] in
lemma macK_eq_div (hM : 0 < M) (h : M ≤ m) : macK m M = m / M := by
  unfold macK
  have : 1 ≤ m / M := (Nat.le_div_iff_mul_le hM).2 (by omega)
  omega

lemma macCell_val_bounds (hM : 0 < M) (h : M ≤ m) {v : ZMod m} {j : Fin (macK m M)}
    (hv : macCell m M v = j) : (j : ℕ) * M ≤ v.val ∧ v.val < (j : ℕ) * M + 2 * M := by
  have hj : (j : ℕ) = min (v.val / M) (macK m M - 1) := by rw [← hv]; rfl
  have hK := macK_eq_div hM h
  have h1 := Nat.div_mul_le_self v.val M
  have h2 := Nat.lt_mul_div_succ v.val hM
  have h3 := Nat.div_mul_le_self m M
  have h4 := Nat.lt_mul_div_succ m hM
  have h5 := ZMod.val_lt v
  rcases le_total (v.val / M) (macK m M - 1) with hc | hc
  · rw [min_eq_left hc] at hj
    rw [hj]; constructor <;> nlinarith
  · rw [min_eq_right hc] at hj
    have hpos : 1 ≤ m / M := (Nat.le_div_iff_mul_le hM).2 (by omega)
    have e : (j : ℕ) + 1 = m / M := by omega
    have : (j : ℕ) * M + 2 * M = (m / M + 1) * M := by rw [← e]; ring
    constructor
    · rw [hj]
      exact Nat.mul_le_mul_right M (by omega) |>.trans h1 |> fun h => by
        have : (v.val / M) * M ≥ (macK m M - 1) * M := Nat.mul_le_mul_right M hc
        nlinarith
    · rw [this]; nlinarith

lemma macCell_card_ge (hM : 0 < M) (h : M ≤ m) (j : Fin (macK m M)) :
    M ≤ (univ.filter fun v : ZMod m => macCell m M v = j).card := by
  have hK := macK_eq_div hM h
  have hjK : (j : ℕ) + 1 ≤ m / M := by have := j.2; omega
  have hjm : ((j : ℕ) + 1) * M ≤ m :=
    (Nat.mul_le_mul_right M hjK).trans (Nat.div_mul_le_self m M)
  have key : ∀ i ∈ range M, (((j : ℕ) * M + i : ℕ) : ZMod m) ∈
      (univ.filter fun v : ZMod m => macCell m M v = j) := by
    intro i hi
    have hi' := mem_range.1 hi
    have hv : (((j : ℕ) * M + i : ℕ) : ZMod m).val = (j : ℕ) * M + i := by
      rw [ZMod.val_natCast]; apply Nat.mod_eq_of_lt; nlinarith
    simp only [mem_filter, mem_univ, true_and]
    apply Fin.ext
    show min ((((j : ℕ) * M + i : ℕ) : ZMod m).val / M) (macK m M - 1) = j
    rw [hv]
    have : ((j : ℕ) * M + i) / M = j :=
      Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
    rw [this]; have := j.2; omega
  calc M = (range M).card := (card_range M).symm
    _ ≤ _ := by
      refine card_le_card_of_injOn (fun i => (((j : ℕ) * M + i : ℕ) : ZMod m)) key ?_
      intro a ha b hb hab
      have ha' := mem_range.1 (by simpa using ha)
      have hb' := mem_range.1 (by simpa using hb)
      have := congrArg ZMod.val hab
      simp only at this
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by nlinarith),
        Nat.mod_eq_of_lt (by nlinarith)] at this
      omega

lemma macCell_nonempty (j : Fin (macK m M)) :
    ∃ v : ZMod m, macCell m M v = j := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have : macK m 0 = 1 := by unfold macK; simp
    refine ⟨0, Fin.ext ?_⟩
    have := j.2; simp [macCell]; omega
  rcases lt_or_ge m M with h | h
  · have hK : macK m M = 1 := macK_eq_one_of_lt (by omega)
    refine ⟨0, Fin.ext ?_⟩
    have := j.2; simp [macCell]; omega
  · have := macCell_card_ge hM h j
    have : 0 < (univ.filter fun v : ZMod m => macCell m M v = j).card := by omega
    obtain ⟨v, hv⟩ := card_pos.1 this
    exact ⟨v, (mem_filter.1 hv).2⟩

/-- Cyclic distance is at most the difference of the representatives in `[0, m)`. -/
lemma natAbs_cycRep_sub_le (a b : ZMod m) :
    (cycRep (a - b)).natAbs ≤ ((a.val : ℤ) - b.val).natAbs := by
  apply natAbs_cycRep_le_of_cast
  push_cast
  simp

lemma macCell_dist_lt (hM : 0 < M) (h : M ≤ m) {a b : ZMod m}
    (hab : macCell m M a = macCell m M b) : (cycRep (a - b)).natAbs < 2 * M := by
  have h1 := macCell_val_bounds hM h (rfl : macCell m M a = _)
  have h2 := macCell_val_bounds hM h (hab.symm : macCell m M b = macCell m M a)
  refine lt_of_le_of_lt (natAbs_cycRep_sub_le a b) ?_
  omega

/-- Number of points within cyclic distance `R` of `t`. -/
lemma card_cyc_ball_le (t : ZMod m) (R : ℕ) :
    (univ.filter fun v : ZMod m => (cycRep (t - v)).natAbs ≤ R).card ≤ 2 * R + 1 := by
  have hsub : (univ.filter fun v : ZMod m => (cycRep (t - v)).natAbs ≤ R) ⊆
      (Finset.Icc (-(R : ℤ)) R).image (fun k : ℤ => t - (k : ZMod m)) := by
    intro v hv
    have hv' := (mem_filter.1 hv).2
    refine mem_image.2 ⟨cycRep (t - v), ?_, ?_⟩
    · rw [mem_Icc]; omega
    · rw [cast_cycRep]; ring
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [Int.card_Icc]; omega

/-- The cells within cyclic distance `< 2M` of the residue `t`. -/
def macNear (M : ℕ) (t : ZMod m) : Finset (Fin (macK m M)) :=
  univ.filter fun j => ∃ u : ZMod m, macCell m M u = j ∧ (cycRep (t - u)).natAbs < 2 * M

lemma macNear_card_le (hM : 0 < M) (t : ZMod m) : (macNear M t).card ≤ 7 := by
  rcases lt_or_ge m M with h | h
  · have hK : macK m M = 1 := macK_eq_one_of_lt (by omega)
    calc (macNear M t).card ≤ (univ : Finset (Fin (macK m M))).card := card_le_univ _
      _ = 1 := by simp [hK]
      _ ≤ 7 := by omega
  · set S := macNear M t with hS
    have hdisj : ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' →
        Disjoint (univ.filter fun v : ZMod m => macCell m M v = j)
          (univ.filter fun v : ZMod m => macCell m M v = j') := by
      intro j _ j' _ hne
      rw [disjoint_filter]
      intro v _ h1 h2; exact hne (h1.symm.trans h2)
    have hsub : S.biUnion (fun j => univ.filter fun v : ZMod m => macCell m M v = j) ⊆
        univ.filter fun v : ZMod m => (cycRep (t - v)).natAbs ≤ 4 * M - 1 := by
      intro v hv
      obtain ⟨j, hj, hvj⟩ := mem_biUnion.1 hv
      have hvj' := (mem_filter.1 hvj).2
      obtain ⟨u, hu, htu⟩ := (mem_filter.1 hj).2
      have h1 := macCell_dist_lt hM h (a := u) (b := v) (hu.trans hvj'.symm)
      have h2 := natAbs_cycRep_add_le (t - u) (u - v)
      rw [sub_add_sub_cancel] at h2
      simp only [mem_filter, mem_univ, true_and]
      omega
    have hc := card_le_card hsub
    rw [card_biUnion hdisj] at hc
    have hb := card_cyc_ball_le t (4 * M - 1)
    have hl : S.card • M ≤ ∑ j ∈ S, (univ.filter fun v : ZMod m => macCell m M v = j).card :=
      card_nsmul_le_sum _ _ _ fun j _ => macCell_card_ge hM h j
    rw [smul_eq_mul] at hl
    have h8 : 2 * (4 * M - 1) + 1 < 8 * M := by omega
    by_contra hcon
    have : 8 * M ≤ S.card * M := by nlinarith
    omega

/-- Cells all of whose points lie in a finite set `N` number at most `1 + |N| / M`. -/
lemma macCells_card_le (hM : 0 < M) (N : Finset (ZMod m)) (S : Finset (Fin (macK m M)))
    (h : M ≤ m → ∀ j ∈ S, ∀ v : ZMod m, macCell m M v = j → v ∈ N) :
    (S.card : ℝ) ≤ 1 + N.card / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rcases lt_or_ge m M with hm | hm
  · have hK : macK m M = 1 := macK_eq_one_of_lt (by omega)
    have : S.card ≤ 1 := by
      calc S.card ≤ (univ : Finset (Fin (macK m M))).card := card_le_univ _
        _ = 1 := by simp [hK]
    have h1 : (S.card : ℝ) ≤ 1 := by exact_mod_cast this
    have : (0 : ℝ) ≤ N.card / M := div_nonneg (Nat.cast_nonneg _) hM'.le
    linarith
  · have hdisj : ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' →
        Disjoint (univ.filter fun v : ZMod m => macCell m M v = j)
          (univ.filter fun v : ZMod m => macCell m M v = j') := by
      intro j _ j' _ hne
      rw [disjoint_filter]
      intro v _ h1 h2; exact hne (h1.symm.trans h2)
    have hsub : S.biUnion (fun j => univ.filter fun v : ZMod m => macCell m M v = j) ⊆ N := by
      intro v hv
      obtain ⟨j, hj, hvj⟩ := mem_biUnion.1 hv
      exact h hm j hj v (mem_filter.1 hvj).2
    have hc := card_le_card hsub
    rw [card_biUnion hdisj] at hc
    have hl : S.card • M ≤ ∑ j ∈ S, (univ.filter fun v : ZMod m => macCell m M v = j).card :=
      card_nsmul_le_sum _ _ _ fun j _ => macCell_card_ge hM hm j
    rw [smul_eq_mul] at hl
    have h2 : (S.card : ℝ) * M ≤ N.card := by exact_mod_cast hl.trans hc
    have : (S.card : ℝ) ≤ N.card / M := by rw [le_div_iff₀ hM']; exact h2
    linarith

/-- The arc from `a` in the direction of `b`, of `|cycRep (b - a)| + 1` points. -/
def macArc (a b : ZMod m) : Finset (ZMod m) :=
  (Finset.Icc (min 0 (cycRep (b - a))) (max 0 (cycRep (b - a)))).image
    (fun e : ℤ => a + (e : ZMod m))

/-- Cells whose interval lies within cyclic distance `< 2M` of a point of the arc. -/
def macNearArc (M : ℕ) (a b : ZMod m) : Finset (Fin (macK m M)) :=
  univ.filter fun j => ∃ u : ZMod m, macCell m M u = j ∧
    ∃ t ∈ macArc a b, (cycRep (t - u)).natAbs < 2 * M

lemma macNearArc_card_le (hM : 0 < M) (a b : ZMod m) :
    ((macNearArc M a b).card : ℝ) ≤ 9 + (cycRep (b - a)).natAbs / (M : ℝ) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set δ := cycRep (b - a) with hδ
  set R : ℤ := 4 * (M : ℤ) - 1 with hR
  set N : Finset (ZMod m) := (Finset.Icc (min 0 δ - R) (max 0 δ + R)).image
    (fun e : ℤ => a + (e : ZMod m)) with hN
  have hNc : N.card ≤ δ.natAbs + 8 * M := by
    refine card_image_le.trans ?_
    rw [Int.card_Icc]; omega
  have h := macCells_card_le hM N (macNearArc M a b) (by
    intro hm j hj v hv
    obtain ⟨u, hu, t, ht, htu⟩ := (mem_filter.1 hj).2
    obtain ⟨e0, he0, rfl⟩ := mem_image.1 ht
    have h1 := macCell_dist_lt hM hm (a := u) (b := v) (hu.trans hv.symm)
    have h2 := natAbs_cycRep_add_le (a + (e0 : ZMod m) - u) (u - v)
    rw [sub_add_sub_cancel] at h2
    refine mem_image.2 ⟨e0 - cycRep (a + (e0 : ZMod m) - v), ?_, ?_⟩
    · rw [mem_Icc] at he0 ⊢; omega
    · push_cast; rw [cast_cycRep]; ring)
  have hNr : (N.card : ℝ) ≤ δ.natAbs + 8 * M := by exact_mod_cast hNc
  have h3 : (N.card : ℝ) / M ≤ δ.natAbs / M + 8 := by
    calc (N.card : ℝ) / M ≤ (δ.natAbs + 8 * M) / M := by gcongr
      _ = δ.natAbs / M + 8 := by field_simp
  linarith

/-- Cells with a point within cyclic distance `< 4M` of a point of the cell `j`. -/
def macNear2 (M : ℕ) (j : Fin (macK m M)) : Finset (Fin (macK m M)) :=
  univ.filter fun j' => ∃ u v : ZMod m, macCell m M u = j' ∧ macCell m M v = j ∧
    (cycRep (u - v)).natAbs < 4 * M

lemma macNear2_card_le (hM : 0 < M) (j : Fin (macK m M)) : (macNear2 M j).card ≤ 16 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨t0, ht0⟩ := macCell_nonempty (m := m) (M := M) j
  set N : Finset (ZMod m) := univ.filter fun v : ZMod m => (cycRep (t0 - v)).natAbs ≤ 8 * M - 1
  have hN : N.card ≤ 2 * (8 * M - 1) + 1 := card_cyc_ball_le t0 _
  have h := macCells_card_le hM N (macNear2 M j) (by
    intro hm j' hj' w hw
    obtain ⟨u, v, hu, hv, huv⟩ := (mem_filter.1 hj').2
    have h1 := macCell_dist_lt hM hm (a := u) (b := w) (hu.trans hw.symm)
    have h2 := macCell_dist_lt hM hm (a := v) (b := t0) (hv.trans ht0.symm)
    have h3 := natAbs_cycRep_add_le (t0 - v) (v - u)
    have h4 := natAbs_cycRep_neg (u - v)
    rw [sub_add_sub_cancel] at h3
    rw [neg_sub] at h4
    have h5 := natAbs_cycRep_add_le (t0 - u) (u - w)
    rw [sub_add_sub_cancel] at h5
    have h6 := natAbs_cycRep_neg (t0 - v)
    rw [neg_sub] at h6
    simp only [N, mem_filter, mem_univ, true_and]
    omega)
  have hNr : (N.card : ℝ) ≤ 2 * (8 * M - 1) + 1 := by
    have : 1 ≤ 8 * M := by omega
    have h' : (N.card : ℝ) ≤ ((2 * (8 * M - 1) + 1 : ℕ) : ℝ) := by exact_mod_cast hN
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub this] at h'
    push_cast at h'; linarith
  have h3 : (N.card : ℝ) / M < 16 := by
    rw [div_lt_iff₀ hM']; linarith
  have : ((macNear2 M j).card : ℝ) < 17 := by linarith
  have : (macNear2 M j).card < 17 := by exact_mod_cast this
  omega

end OneDim

section Cover

open scoped Classical

variable (d m M : ℕ) [NeZero m]

/-- Cell indices: one interval index per coordinate. -/
abbrev MacIdx : Type := Fin d → Fin (macK m M)

/-- The core `C_z`: the sites whose coordinates lie in the intervals `z i`. -/
def macCore (z : MacIdx d m M) : Set (L1Torus d m) :=
  {x | ∀ i, macCell m M (x i) = z i}

/-- The enlarged box `B_z = {x : dist(x, C_z) < 2M}`. -/
def macBox (z : MacIdx d m M) : Set (L1Torus d m) :=
  {x | Metric.infDist x (macCore d m M z) < 2 * M}

/-- The plateau `φ_z(x) = max 0 (1 - dist(x, C_z) / M)`. -/
noncomputable def macPhi (z : MacIdx d m M) (x : L1Torus d m) : ℝ :=
  max 0 (1 - Metric.infDist x (macCore d m M z) / M)

/-- The total mass `∑_z φ_z(x)`. -/
noncomputable def macSum (x : L1Torus d m) : ℝ := ∑ z : MacIdx d m M, macPhi d m M z x

/-- The partition of unity `χ_z = φ_z / ∑_w φ_w`. -/
noncomputable def macChi (z : MacIdx d m M) (x : L1Torus d m) : ℝ :=
  macPhi d m M z x / macSum d m M x

variable {d m}

/-- The cell containing a site. -/
def macZ (M : ℕ) (x : L1Torus d m) : MacIdx d m M := fun i => macCell m M (x i)

variable {M}

lemma macCore_nonempty (z : MacIdx d m M) : (macCore d m M z).Nonempty := by
  choose v hv using fun i => macCell_nonempty (m := m) (M := M) (z i)
  exact ⟨(v : Fin d → ZMod m), hv⟩

omit [NeZero m] in
lemma mem_macCore_macZ (x : L1Torus d m) : x ∈ macCore d m M (macZ M x) := fun _ => rfl

omit [NeZero m] in
lemma eq_macZ_of_mem_macCore {x : L1Torus d m} {z : MacIdx d m M} (h : x ∈ macCore d m M z) :
    z = macZ M x := funext fun i => (h i).symm

omit [NeZero m] in
/-- The cores partition the torus: every site lies in exactly one core. -/
theorem macCore_partition (x : L1Torus d m) : ∃! z : MacIdx d m M, x ∈ macCore d m M z :=
  ⟨macZ M x, mem_macCore_macZ x, fun _ h => eq_macZ_of_mem_macCore h⟩

lemma macCore_subset_box (z : MacIdx d m M) (hM : 0 < M) : macCore d m M z ⊆ macBox d m M z := by
  intro x hx
  show Metric.infDist x _ < _
  rw [Metric.infDist_zero_of_mem hx]; positivity

/-- Separation: a site of the core and a site outside the box are at distance `≥ 2M`. -/
theorem macBox_separation {z : MacIdx d m M} {x y : L1Torus d m} (hx : x ∈ macCore d m M z)
    (hy : y ∉ macBox d m M z) : (2 * M : ℝ) ≤ dist x y := by
  have h := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := macCore d m M z)
  rw [Metric.infDist_zero_of_mem hx, zero_add, dist_comm] at h
  have : (2 * M : ℝ) ≤ Metric.infDist y (macCore d m M z) := not_lt.1 hy
  linarith

omit [NeZero m] in
/-- Small torus: if `m < 2M` there is one cell and the core is the whole torus. -/
theorem macCore_eq_univ_of_lt (h : m < 2 * M) (z : MacIdx d m M) :
    macCore d m M z = Set.univ := by
  have hK := macK_eq_one_of_lt (m := m) h
  ext x
  simp only [Set.mem_univ, iff_true]
  intro i
  apply Fin.ext
  have h1 := (macCell m M (x i)).2
  have h2 := (z i).2
  omega

lemma dist_coord_le (x y : L1Torus d m) (i : Fin d) :
    ((cycRep (x i - y i)).natAbs : ℝ) ≤ dist x y := by
  rw [dist_L1Torus]
  exact Finset.single_le_sum (f := fun i => ((cycRep (x i - y i)).natAbs : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (mem_univ i)

/-- Bounded overlap: a site lies in at most `7^d` boxes. -/
theorem macBox_overlap (hM : 0 < M) (x : L1Torus d m) :
    (univ.filter fun z : MacIdx d m M => x ∈ macBox d m M z).card ≤ 7 ^ d := by
  have hsub : (univ.filter fun z : MacIdx d m M => x ∈ macBox d m M z) ⊆
      Fintype.piFinset (fun i => macNear M (x i)) := by
    intro z hz
    have hz' : Metric.infDist x (macCore d m M z) < 2 * M := (mem_filter.1 hz).2
    obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff (macCore_nonempty z)).1 hz'
    rw [Fintype.mem_piFinset]
    intro i
    refine mem_filter.2 ⟨mem_univ _, y i, hy i, ?_⟩
    have := (dist_coord_le x y i).trans_lt hxy
    exact_mod_cast this
  calc _ ≤ _ := card_le_card hsub
    _ = ∏ i, (macNear M (x i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, 7 := Finset.prod_le_prod fun i _ => macNear_card_le hM _
    _ = 7 ^ d := by simp

lemma macPhi_nonneg (z : MacIdx d m M) (x : L1Torus d m) : 0 ≤ macPhi d m M z x := le_max_left _ _

lemma macPhi_le_one (z : MacIdx d m M) (x : L1Torus d m) : macPhi d m M z x ≤ 1 := by
  refine max_le zero_le_one ?_
  have : 0 ≤ Metric.infDist x (macCore d m M z) / M :=
    div_nonneg Metric.infDist_nonneg (Nat.cast_nonneg _)
  linarith

lemma macPhi_eq_one_of_mem {z : MacIdx d m M} {x : L1Torus d m} (h : x ∈ macCore d m M z) :
    macPhi d m M z x = 1 := by
  simp [macPhi, Metric.infDist_zero_of_mem h]

lemma macPhi_ne_zero_iff (hM : 0 < M) (z : MacIdx d m M) (x : L1Torus d m) :
    macPhi d m M z x ≠ 0 ↔ Metric.infDist x (macCore d m M z) < M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold macPhi
  constructor
  · intro h
    by_contra hc
    apply h
    have : 1 - Metric.infDist x (macCore d m M z) / M ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hM']; linarith [not_lt.1 hc]
    exact max_eq_left this
  · intro h
    have : 0 < 1 - Metric.infDist x (macCore d m M z) / M := by
      rw [sub_pos, div_lt_one hM']; exact h
    exact (lt_max_of_lt_right this).ne'

lemma macPhi_lipschitz (hM : 0 < M) (z : MacIdx d m M) (x y : L1Torus d m) :
    |macPhi d m M z x - macPhi d m M z y| ≤ dist x y / M := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold macPhi
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  have h1 := Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := macCore d m M z)
  have h2 := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := macCore d m M z)
  rw [dist_comm y x] at h2
  have e : (1 - Metric.infDist x (macCore d m M z) / M) -
      (1 - Metric.infDist y (macCore d m M z) / M) =
      (Metric.infDist y (macCore d m M z) - Metric.infDist x (macCore d m M z)) / M := by ring
  rw [e, abs_div, abs_of_pos hM']
  gcongr
  rw [abs_le]
  constructor <;> linarith

lemma macPhi_eq_zero_of_not_box (hM : 0 < M) {z : MacIdx d m M} {x : L1Torus d m}
    (h : x ∉ macBox d m M z) : macPhi d m M z x = 0 := by
  by_contra hne
  apply h
  have := (macPhi_ne_zero_iff hM z x).1 hne
  have hM' : (M : ℝ) < 2 * M := by have : (0 : ℝ) < M := by exact_mod_cast hM
                                   linarith
  exact this.trans hM'

lemma macSum_ge_one (x : L1Torus d m) : 1 ≤ macSum d m M x := by
  have := Finset.single_le_sum (f := fun z : MacIdx d m M => macPhi d m M z x)
    (fun z _ => macPhi_nonneg z x) (mem_univ (macZ M x))
  rw [macPhi_eq_one_of_mem (mem_macCore_macZ x)] at this
  exact this

lemma macPhi_le_macSum (z : MacIdx d m M) (x : L1Torus d m) : macPhi d m M z x ≤ macSum d m M x :=
  Finset.single_le_sum (f := fun z : MacIdx d m M => macPhi d m M z x)
    (fun z _ => macPhi_nonneg z x) (mem_univ z)

lemma macSum_pos (x : L1Torus d m) : 0 < macSum d m M x := lt_of_lt_of_le one_pos (macSum_ge_one x)

theorem macChi_nonneg (z : MacIdx d m M) (x : L1Torus d m) : 0 ≤ macChi d m M z x :=
  div_nonneg (macPhi_nonneg z x) (macSum_pos x).le

theorem macChi_le_one (z : MacIdx d m M) (x : L1Torus d m) : macChi d m M z x ≤ 1 :=
  (div_le_one (macSum_pos x)).2 (macPhi_le_macSum z x)

/-- Partition of unity: `∑_z χ_z = 1`. -/
theorem macChi_sum (x : L1Torus d m) : ∑ z : MacIdx d m M, macChi d m M z x = 1 := by
  unfold macChi
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (macSum_pos x).ne'

/-- Support and interior margin: `χ_z x ≠ 0` implies `dist(x, C_z) < M`; hence `χ_z` vanishes
at every site within distance `M` of the complement of `B_z` (and `x ∈ B_z`). -/
theorem macChi_ne_zero_iff (hM : 0 < M) (z : MacIdx d m M) (x : L1Torus d m) :
    macChi d m M z x ≠ 0 ↔ Metric.infDist x (macCore d m M z) < M := by
  unfold macChi
  rw [div_ne_zero_iff, macPhi_ne_zero_iff hM]
  simp [(macSum_pos x).ne']

theorem macChi_mem_box (hM : 0 < M) {z : MacIdx d m M} {x : L1Torus d m}
    (h : macChi d m M z x ≠ 0) : x ∈ macBox d m M z := by
  by_contra hc
  apply h
  unfold macChi
  rw [macPhi_eq_zero_of_not_box hM hc, zero_div]

/-- Interior margin: if `χ_z x ≠ 0` and `y ∉ B_z` then `dist x y > M`. -/
theorem macChi_margin (hM : 0 < M) {z : MacIdx d m M} {x y : L1Torus d m}
    (h : macChi d m M z x ≠ 0) (hy : y ∉ macBox d m M z) : (M : ℝ) < dist x y := by
  have h1 := (macChi_ne_zero_iff hM z x).1 h
  have h2 : (2 * M : ℝ) ≤ Metric.infDist y (macCore d m M z) := not_lt.1 hy
  have h3 := Metric.infDist_le_infDist_add_dist (x := y) (y := x) (s := macCore d m M z)
  rw [dist_comm] at h3
  linarith

lemma quot_lip {a b s t ε Δ : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hb : 0 ≤ b) (hbt : b ≤ t)
    (h1 : |a - b| ≤ ε) (h2 : |s - t| ≤ Δ) : |a / s - b / t| ≤ ε + Δ := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have e : a / s - b / t = (a - b) / s + (b / t) * ((t - s) / s) := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hs0]
    calc |a - b| / s ≤ |a - b| := div_le_self (abs_nonneg _) hs
      _ ≤ ε := h1
  · rw [abs_mul, abs_of_nonneg (div_nonneg hb ht0.le), abs_div, abs_of_pos hs0]
    have h3 : b / t ≤ 1 := (div_le_one ht0).2 hbt
    have h4 : |t - s| / s ≤ Δ := by
      rw [abs_sub_comm] at h2
      calc |t - s| / s ≤ |t - s| := div_le_self (abs_nonneg _) hs
        _ ≤ Δ := h2
    calc b / t * (|t - s| / s) ≤ 1 * (|t - s| / s) :=
          mul_le_mul_of_nonneg_right h3 (div_nonneg (abs_nonneg _) hs0.le)
      _ ≤ Δ := by linarith

/-- The number of cells charged at `x` or `y` is at most `2·7^d`. -/
lemma macSupport_card (hM : 0 < M) (x y : L1Torus d m) :
    (univ.filter fun z : MacIdx d m M => macPhi d m M z x ≠ 0 ∨ macPhi d m M z y ≠ 0).card
      ≤ 2 * 7 ^ d := by
  rw [filter_or]
  refine (card_union_le _ _).trans ?_
  have hx : (univ.filter fun z : MacIdx d m M => macPhi d m M z x ≠ 0).card ≤ 7 ^ d :=
    (card_le_card fun z hz => mem_filter.2 ⟨mem_univ _, by
      by_contra hc
      exact (mem_filter.1 hz).2 (macPhi_eq_zero_of_not_box hM hc)⟩).trans (macBox_overlap hM x)
  have hy : (univ.filter fun z : MacIdx d m M => macPhi d m M z y ≠ 0).card ≤ 7 ^ d :=
    (card_le_card fun z hz => mem_filter.2 ⟨mem_univ _, by
      by_contra hc
      exact (mem_filter.1 hz).2 (macPhi_eq_zero_of_not_box hM hc)⟩).trans (macBox_overlap hM y)
  omega

lemma macSum_lipschitz (hM : 0 < M) (x y : L1Torus d m) :
    |macSum d m M x - macSum d m M y| ≤ 2 * 7 ^ d * (dist x y / M) := by
  set A := univ.filter fun z : MacIdx d m M => macPhi d m M z x ≠ 0 ∨ macPhi d m M z y ≠ 0
  have hA : ∀ z ∈ (univ : Finset (MacIdx d m M)), z ∉ A →
      macPhi d m M z x - macPhi d m M z y = 0 := by
    intro z _ hz
    simp only [A, mem_filter, mem_univ, true_and, not_or, not_not] at hz
    rw [hz.1, hz.2]; ring
  have e : macSum d m M x - macSum d m M y =
      ∑ z ∈ A, (macPhi d m M z x - macPhi d m M z y) := by
    unfold macSum
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_subset (subset_univ A) hA).symm
  rw [e]
  calc _ ≤ ∑ z ∈ A, |macPhi d m M z x - macPhi d m M z y| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ A, dist x y / M := Finset.sum_le_sum fun z _ => macPhi_lipschitz hM z x y
    _ = A.card * (dist x y / M) := by simp
    _ ≤ (2 * 7 ^ d : ℕ) * (dist x y / M) := by
        have := macSupport_card hM x y
        have h0 : 0 ≤ dist x y / M := div_nonneg dist_nonneg (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) h0
    _ = _ := by push_cast; ring

/-- Lipschitz bound of the partition of unity: `|χ_z x - χ_z y| ≤ (1 + 2·7^d) dist x y / M`. -/
theorem macChi_lipschitz (hM : 0 < M) (z : MacIdx d m M) (x y : L1Torus d m) :
    |macChi d m M z x - macChi d m M z y| ≤ (1 + 2 * 7 ^ d) * (dist x y / M) := by
  have := quot_lip (a := macPhi d m M z x) (b := macPhi d m M z y)
    (macSum_ge_one x) (macSum_ge_one y) (macPhi_nonneg z y) (macPhi_le_macSum z y)
    (macPhi_lipschitz hM z x y) (macSum_lipschitz hM x y)
  unfold macChi
  linarith

end Cover

section Tags

variable (d m M : ℕ) [NeZero m]

open scoped Classical

/-- The deterministic path from `x` to `y`: the union over `k` of the axis-parallel segments on
which coordinates `i < k` equal `y i`, coordinates `i > k` equal `x i`, and coordinate `k` runs
along the shortest arc from `x k` to `y k`. -/
def macPath (x y : L1Torus d m) : Set (L1Torus d m) :=
  {p | ∃ k : Fin d, (∀ i, i < k → p i = y i) ∧ (∀ i, k < i → p i = x i) ∧
    p k ∈ macArc (x k) (y k)}

/-- Path tags: the cells `w` whose box meets the box `B_z`, or meets the path from `x` to `y`. -/
noncomputable def macTags (z : MacIdx d m M) (x y : L1Torus d m) : Finset (MacIdx d m M) :=
  univ.filter fun w => (∃ p, p ∈ macBox d m M w ∧ p ∈ macBox d m M z) ∨
    ∃ p ∈ macPath d m x y, p ∈ macBox d m M w

variable {d m M}

omit [NeZero m] in
lemma macArc_mem_start (a b : ZMod m) : a ∈ macArc a b := by
  refine mem_image.2 ⟨0, ?_, by simp⟩
  rw [mem_Icc]; exact ⟨min_le_left _ _, le_max_left _ _⟩

lemma macArc_mem_end (a b : ZMod m) : b ∈ macArc a b := by
  refine mem_image.2 ⟨cycRep (b - a), ?_, ?_⟩
  · rw [mem_Icc]; exact ⟨min_le_right _ _, le_max_right _ _⟩
  · rw [cast_cycRep]; ring

omit [NeZero m] in
lemma macPath_start (hd : 0 < d) (x y : L1Torus d m) : x ∈ macPath d m x y :=
  ⟨⟨0, hd⟩, fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl, macArc_mem_start _ _⟩

lemma macPath_end (hd : 0 < d) (x y : L1Torus d m) : y ∈ macPath d m x y := by
  refine ⟨⟨d - 1, by omega⟩, fun _ _ => rfl, fun i hi => ?_, macArc_mem_end _ _⟩
  exact absurd hi (by have := i.2; simp [Fin.lt_def]; omega)

/-- Tags of the first kind: at most `16^d` cells have a box meeting `B_z`. -/
lemma macTags_near_card (hM : 0 < M) (z : MacIdx d m M) :
    (univ.filter fun w : MacIdx d m M => ∃ p, p ∈ macBox d m M w ∧ p ∈ macBox d m M z).card
      ≤ 16 ^ d := by
  have hsub : (univ.filter fun w : MacIdx d m M => ∃ p, p ∈ macBox d m M w ∧
      p ∈ macBox d m M z) ⊆ Fintype.piFinset (fun i => macNear2 M (z i)) := by
    intro w hw
    obtain ⟨p, hpw, hpz⟩ := (mem_filter.1 hw).2
    obtain ⟨q1, hq1, hd1⟩ := (Metric.infDist_lt_iff (macCore_nonempty w)).1 hpw
    obtain ⟨q2, hq2, hd2⟩ := (Metric.infDist_lt_iff (macCore_nonempty z)).1 hpz
    rw [Fintype.mem_piFinset]
    intro i
    refine mem_filter.2 ⟨mem_univ _, q1 i, q2 i, hq1 i, hq2 i, ?_⟩
    have a1 := (dist_coord_le p q1 i).trans_lt hd1
    have a2 := (dist_coord_le p q2 i).trans_lt hd2
    have a3 := natAbs_cycRep_add_le (q1 i - p i) (p i - q2 i)
    rw [sub_add_sub_cancel] at a3
    have a4 := natAbs_cycRep_neg (p i - q1 i)
    rw [neg_sub] at a4
    have b1 : (cycRep (p i - q1 i)).natAbs < 2 * M := by exact_mod_cast a1
    have b2 : (cycRep (p i - q2 i)).natAbs < 2 * M := by exact_mod_cast a2
    omega
  calc _ ≤ _ := card_le_card hsub
    _ = ∏ i, (macNear2 M (z i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, 16 := Finset.prod_le_prod fun i _ => macNear2_card_le hM _
    _ = 16 ^ d := by simp

/-- The cells whose box meets the segment `k` of the path from `x` to `y`. -/
lemma macTags_seg_card (hM : 0 < M) (x y : L1Torus d m) (k : Fin d) :
    ((univ.filter fun w : MacIdx d m M => ∃ p : L1Torus d m, (∀ i, i < k → p i = y i) ∧
        (∀ i, k < i → p i = x i) ∧ p k ∈ macArc (x k) (y k) ∧ p ∈ macBox d m M w).card : ℝ)
      ≤ (9 + (cycRep (y k - x k)).natAbs / (M : ℝ)) * 7 ^ d := by
  let g : Fin d → Finset (Fin (macK m M)) := fun i =>
    if i < k then macNear M (y i) else if k < i then macNear M (x i)
      else macNearArc M (x k) (y k)
  have hsub : (univ.filter fun w : MacIdx d m M => ∃ p : L1Torus d m, (∀ i, i < k → p i = y i) ∧
        (∀ i, k < i → p i = x i) ∧ p k ∈ macArc (x k) (y k) ∧ p ∈ macBox d m M w) ⊆
      Fintype.piFinset g := by
    intro w hw
    obtain ⟨p, h1, h2, h3, h4⟩ := (mem_filter.1 hw).2
    obtain ⟨q, hq, hd⟩ := (Metric.infDist_lt_iff (macCore_nonempty w)).1 h4
    rw [Fintype.mem_piFinset]
    intro i
    have a1 : (cycRep (p i - q i)).natAbs < 2 * M := by
      exact_mod_cast (dist_coord_le p q i).trans_lt hd
    simp only [g]
    split_ifs with c1 c2
    · refine mem_filter.2 ⟨mem_univ _, q i, hq i, ?_⟩
      rw [← h1 i c1]; exact a1
    · refine mem_filter.2 ⟨mem_univ _, q i, hq i, ?_⟩
      rw [← h2 i c2]; exact a1
    · have : i = k := le_antisymm (not_lt.1 c2) (not_lt.1 c1)
      subst this
      exact mem_filter.2 ⟨mem_univ _, q i, hq i, p i, h3, a1⟩
  have hc := card_le_card hsub
  rw [Fintype.card_piFinset] at hc
  have hc' : ((univ.filter fun w : MacIdx d m M => ∃ p : L1Torus d m, (∀ i, i < k → p i = y i) ∧
        (∀ i, k < i → p i = x i) ∧ p k ∈ macArc (x k) (y k) ∧ p ∈ macBox d m M w).card : ℝ)
      ≤ ((∏ i, (g i).card : ℕ) : ℝ) := by exact_mod_cast hc
  refine hc'.trans ?_
  rw [Nat.cast_prod, ← Finset.mul_prod_erase univ (fun i => ((g i).card : ℝ)) (mem_univ k)]
  have hk : g k = macNearArc M (x k) (y k) := by simp [g]
  have e1 : ((g k).card : ℝ) ≤ 9 + (cycRep (y k - x k)).natAbs / (M : ℝ) := by
    rw [hk]; exact macNearArc_card_le hM _ _
  have e2 : ∏ i ∈ univ.erase k, ((g i).card : ℝ) ≤ 7 ^ d := by
    calc _ ≤ ∏ _i ∈ univ.erase k, (7 : ℝ) := by
          refine Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i hi => ?_)
          have hik : i ≠ k := (mem_erase.1 hi).1
          have : g i = macNear M (y i) ∨ g i = macNear M (x i) := by
            simp only [g]; split_ifs
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact absurd (le_antisymm (not_lt.1 ‹¬ k < i›) (not_lt.1 ‹¬ i < k›)) hik
          have h7 : (g i).card ≤ 7 := by
            rcases this with h | h <;> rw [h] <;> exact macNear_card_le hM _
          exact_mod_cast h7
      _ = 7 ^ (univ.erase k).card := by simp
      _ ≤ 7 ^ d := by
          apply pow_le_pow_right₀ (by norm_num)
          calc _ ≤ (univ : Finset (Fin d)).card := card_le_card (erase_subset _ _)
            _ = d := by simp
  have e0 : 0 ≤ ∏ i ∈ univ.erase k, ((g i).card : ℝ) :=
    Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  calc _ ≤ (9 + (cycRep (y k - x k)).natAbs / (M : ℝ)) * ∏ i ∈ univ.erase k, ((g i).card : ℝ) :=
        mul_le_mul_of_nonneg_right e1 e0
    _ ≤ _ := mul_le_mul_of_nonneg_left e2 (by positivity)

/-- Path tags have a linear count: `|V_z(x, y)| ≤ H_d + C_p · dist(x, y) / M` with
`H_d = 16^d + 9 d 7^d` and `C_p = 7^d`. -/
theorem macTags_card_le (hM : 0 < M) (z : MacIdx d m M) (x y : L1Torus d m) :
    ((macTags d m M z x y).card : ℝ) ≤
      (16 ^ d + 9 * d * 7 ^ d) + 7 ^ d * (dist x y / M) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set A := univ.filter fun w : MacIdx d m M => ∃ p, p ∈ macBox d m M w ∧ p ∈ macBox d m M z
  set B := univ.filter fun w : MacIdx d m M => ∃ p ∈ macPath d m x y, p ∈ macBox d m M w
  have h1 : macTags d m M z x y ⊆ A ∪ B := by
    intro w hw
    have := (mem_filter.1 hw).2
    rw [mem_union]
    rcases this with h | h
    · exact Or.inl (mem_filter.2 ⟨mem_univ _, h⟩)
    · exact Or.inr (mem_filter.2 ⟨mem_univ _, h⟩)
  have hBsub : B ⊆ univ.biUnion (fun k : Fin d => univ.filter fun w : MacIdx d m M =>
      ∃ p : L1Torus d m, (∀ i, i < k → p i = y i) ∧
        (∀ i, k < i → p i = x i) ∧ p k ∈ macArc (x k) (y k) ∧ p ∈ macBox d m M w) := by
    intro w hw
    obtain ⟨p, ⟨k, hk1, hk2, hk3⟩, hp⟩ := (mem_filter.1 hw).2
    exact mem_biUnion.2 ⟨k, mem_univ _, mem_filter.2 ⟨mem_univ _, p, hk1, hk2, hk3, hp⟩⟩
  have hA : (A.card : ℝ) ≤ 16 ^ d := by exact_mod_cast macTags_near_card hM z
  have hB : (B.card : ℝ) ≤ ∑ k : Fin d, (9 + (cycRep (y k - x k)).natAbs / (M : ℝ)) * 7 ^ d := by
    have h2 := (card_le_card hBsub).trans card_biUnion_le
    have h3 : (B.card : ℝ) ≤ ((∑ k : Fin d, (univ.filter fun w : MacIdx d m M =>
        ∃ p : L1Torus d m, (∀ i, i < k → p i = y i) ∧ (∀ i, k < i → p i = x i) ∧
          p k ∈ macArc (x k) (y k) ∧ p ∈ macBox d m M w).card : ℕ) : ℝ) := by
      exact_mod_cast h2
    rw [Nat.cast_sum] at h3
    exact h3.trans (Finset.sum_le_sum fun k _ => macTags_seg_card hM x y k)
  have hdist : ∑ k : Fin d, ((cycRep (y k - x k)).natAbs : ℝ) = dist x y := by
    rw [dist_L1Torus]
    unfold torusDist
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← natAbs_cycRep_neg (x k - y k), neg_sub]
  have hsum : ∑ k : Fin d, (9 + (cycRep (y k - x k)).natAbs / (M : ℝ)) * 7 ^ d =
      (9 * d * 7 ^ d) + 7 ^ d * (dist x y / M) := by
    have hq : ∑ k : Fin d, ((cycRep (y k - x k)).natAbs : ℝ) / (M : ℝ) = dist x y / M := by
      simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul, hdist]
    rw [← Finset.sum_mul, Finset.sum_add_distrib, hq]
    simp; ring
  have hc : (macTags d m M z x y).card ≤ A.card + B.card :=
    (card_le_card h1).trans (card_union_le _ _)
  have : ((macTags d m M z x y).card : ℝ) ≤ A.card + B.card := by exact_mod_cast hc
  linarith

/-- The path is a shortest path: every point `p` of it satisfies
`dist x p + dist p y = dist x y`. -/
theorem macPath_geodesic {x y p : L1Torus d m} (hp : p ∈ macPath d m x y) :
    dist x p + dist p y = dist x y := by
  obtain ⟨k, h1, h2, h3⟩ := hp
  have hcoord : ∀ i, (cycRep (x i - p i)).natAbs + (cycRep (p i - y i)).natAbs ≤
      (cycRep (x i - y i)).natAbs := by
    intro i
    rcases lt_trichotomy i k with c | c | c
    · rw [h1 i c]; simp [natAbs_cycRep_zero]
    · subst c
      obtain ⟨e, he, hpe⟩ := mem_image.1 h3
      rw [mem_Icc] at he
      have a1 : (cycRep (x i - p i)).natAbs ≤ e.natAbs := by
        have := natAbs_cycRep_le_of_cast (x i - p i) (-e) (by rw [← hpe]; push_cast; ring)
        simpa using this
      have a2 : (cycRep (p i - y i)).natAbs ≤ (e - cycRep (y i - x i)).natAbs := by
        apply natAbs_cycRep_le_of_cast
        push_cast; rw [cast_cycRep, ← hpe]; ring
      have a3 := natAbs_cycRep_neg (y i - x i)
      rw [neg_sub] at a3
      omega
    · rw [h2 i c]; simp [natAbs_cycRep_zero]
  have hle : dist x p + dist p y ≤ dist x y := by
    rw [dist_L1Torus, dist_L1Torus, dist_L1Torus]
    unfold torusDist
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast hcoord i
  exact le_antisymm hle (dist_triangle x p y)

end Tags


end Balaban.Green
