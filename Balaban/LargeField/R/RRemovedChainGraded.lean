/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainForest
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gaussian blocks of a graded family of blocks form a forest (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (a).  For a graded family of finite types of
blocks `blk s` with a coarsening map `up s : blk s → blk (s + 1)` whose fibres have `m` elements,
and a set of blocks (the Gaussian blocks) of scales in `[k₁ + 1, top]`, the Gaussian blocks form a
forest: the parent of a Gaussian block of scale `s` is its coarsening if that is a Gaussian block of
scale `s + 1 ≤ top` (otherwise the block is a root); the leaves of a Gaussian block are its children that
are not Gaussian blocks.  `graded_forest` is the hypothesis list of `forest_trees` for this forest.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

section Graded

variable {m k1 top : ℕ} (blk : ℕ → Type) [∀ s, Fintype (blk s)] [∀ s, DecidableEq (blk s)]
  (up : ∀ s, blk s → blk (s + 1)) (nd : (Σ s, blk s) → Prop) [DecidablePred nd]

open Classical in
/-- **The children of a node of a graded forest**: for a node `(s' + 1, y)`, the sum of a function `g`
of the blocks over its children that are nodes plus the sum over its children that are leaves is the
sum over all `y'` of scale `s'` with `up s' y' = y`. -/
theorem graded_children_sum {W : Type*} [AddCommMonoid W]
    (hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ top)
    [Fintype {b : Σ s, blk s // nd b}]
    [Fintype {q : (Σ s, blk s) × {b : Σ s, blk s // nd b} //
      (⟨q.1.1 + 1, up q.1.1 q.1.2⟩ : Σ s, blk s) = q.2.1 ∧ ¬ nd q.1}]
    (g : (Σ s, blk s) → W) {s' : ℕ} (y : blk (s' + 1)) (hi : nd ⟨s' + 1, y⟩) :
    let pa : {b : Σ s, blk s // nd b} → {b : Σ s, blk s // nd b} := fun b =>
      if h : nd ⟨b.1.1 + 1, up b.1.1 b.1.2⟩ ∧ b.1.1 + 1 ≤ top then
        ⟨⟨b.1.1 + 1, up b.1.1 b.1.2⟩, h.1⟩ else b
    (∑ c ∈ Finset.univ.filter (fun c => pa c ≠ c ∧ pa c = ⟨⟨s' + 1, y⟩, hi⟩), g c.1) +
      (∑ l ∈ Finset.univ.filter (fun l : {q : (Σ s, blk s) × {b : Σ s, blk s // nd b} //
        (⟨q.1.1 + 1, up q.1.1 q.1.2⟩ : Σ s, blk s) = q.2.1 ∧ ¬ nd q.1} =>
          l.1.2 = ⟨⟨s' + 1, y⟩, hi⟩), g l.1.1) =
      ∑ y' ∈ Finset.univ.filter (fun y' : blk s' => up s' y' = y), g ⟨s', y'⟩ := by
  intro pa
  have hr := hrange _ hi
  simp only at hr
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ.filter fun y' : blk s' =>
    up s' y' = y) (p := fun y' => nd ⟨s', y'⟩) (f := fun y' => g ⟨s', y'⟩)]
  congr 1
  · -- the children that are nodes
    refine (Finset.sum_bij (fun y' hy' => (⟨⟨s', y'⟩, (Finset.mem_filter.mp hy').2⟩ :
      {b : Σ s, blk s // nd b})) ?_ ?_ ?_ ?_).symm
    · intro y' hy'
      have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy').1).2
      have hnd := (Finset.mem_filter.mp hy').2
      have hpa : pa ⟨⟨s', y'⟩, hnd⟩ = ⟨⟨s' + 1, y⟩, hi⟩ := by
        have hc : nd ⟨s' + 1, up s' y'⟩ ∧ s' + 1 ≤ top := by
          rw [h1]; exact ⟨hi, hr.2⟩
        simp only [pa, hc, and_self, dite_true]
        apply Subtype.ext
        simp only [h1]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hpa⟩
      rw [hpa]
      intro h
      have := congrArg (fun b : {b : Σ s, blk s // nd b} => b.1.1) h
      simp at this
    · intro y1 h1 y2 h2 h
      have := congrArg (fun b : {b : Σ s, blk s // nd b} => b.1) h
      exact eq_of_heq (Sigma.mk.inj this).2
    · intro c hc
      obtain ⟨-, hne, hpa⟩ := Finset.mem_filter.mp hc
      obtain ⟨⟨s2, y2⟩, hc2⟩ := c
      have hcond : nd ⟨s2 + 1, up s2 y2⟩ ∧ s2 + 1 ≤ top := by
        by_contra hh
        exact hne (by simp only [pa, hh, dite_false])
      have hpa' : (⟨s2 + 1, up s2 y2⟩ : Σ s, blk s) = ⟨s' + 1, y⟩ := by
        have := congrArg Subtype.val hpa
        simpa only [pa, hcond, and_self, dite_true] using this
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hpa'
      have hs2 : s2 = s' := by omega
      subst hs2
      have hy2 : up s2 y2 = y := eq_of_heq h2
      exact ⟨y2, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy2⟩, hc2⟩, rfl⟩
    · intro y' hy'
      rfl
  · -- the children that are leaves
    refine (Finset.sum_bij (fun y' hy' => (⟨(⟨s', y'⟩, ⟨⟨s' + 1, y⟩, hi⟩), by
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hy').1).2
        have hnd := (Finset.mem_filter.mp hy').2
        refine ⟨?_, hnd⟩
        show (⟨s' + 1, up s' y'⟩ : Σ s, blk s) = ⟨s' + 1, y⟩
        rw [h1]⟩ : {q : (Σ s, blk s) × {b : Σ s, blk s // nd b} //
          (⟨q.1.1 + 1, up q.1.1 q.1.2⟩ : Σ s, blk s) = q.2.1 ∧ ¬ nd q.1})) ?_ ?_ ?_ ?_).symm
    · intro y' hy'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · intro y1 h1 y2 h2 h
      have := congrArg (fun l : {q : (Σ s, blk s) × {b : Σ s, blk s // nd b} //
        (⟨q.1.1 + 1, up q.1.1 q.1.2⟩ : Σ s, blk s) = q.2.1 ∧ ¬ nd q.1} => l.1.1) h
      exact eq_of_heq (Sigma.mk.inj this).2
    · intro l hl
      obtain ⟨⟨⟨s2, y2⟩, i2⟩, hl2, hnd2⟩ := l
      have hli := (Finset.mem_filter.mp hl).2
      simp only at hli
      subst hli
      simp only at hl2
      obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hl2
      have hs2 : s2 = s' := by omega
      subst hs2
      have hy2 : up s2 y2 = y := eq_of_heq h2
      exact ⟨y2, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy2⟩, hnd2⟩, rfl⟩
    · intro y' hy'
      rfl

open Classical in
/-- **The Gaussian blocks of a graded family form a forest** (the hypotheses of `forest_trees`).
The nodes are the blocks `b` of `nd` (scales in `[k₁ + 1, top]`, `hrange`); the parent of a node is its
coarsening if that is a node of scale at most `top`, and the node itself otherwise (a root); the
leaves are the pairs (node, child block of that node that is not a node). -/
theorem graded_forest
    (hcard : ∀ s (y : blk (s + 1)), (Finset.univ.filter fun y' : blk s => up s y' = y).card = m)
    (hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ top)
    [Fintype {b : Σ s, blk s // nd b}]
    [Fintype {q : (Σ s, blk s) × {b : Σ s, blk s // nd b} //
      (⟨q.1.1 + 1, up q.1.1 q.1.2⟩ : Σ s, blk s) = q.2.1 ∧ ¬ nd q.1}] :
    let pa : {b : Σ s, blk s // nd b} → {b : Σ s, blk s // nd b} := fun b =>
      if h : nd ⟨b.1.1 + 1, up b.1.1 b.1.2⟩ ∧ b.1.1 + 1 ≤ top then
        ⟨⟨b.1.1 + 1, up b.1.1 b.1.2⟩, h.1⟩ else b
    (∀ i, pa i ≠ i → i.1.1 + 1 = (pa i).1.1) ∧
    (∀ i : {b : Σ s, blk s // nd b}, k1 + 1 ≤ i.1.1) ∧
    (∀ i, (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l : {q : (Σ s, blk s) × {b : Σ s, blk s // nd b} //
        (⟨q.1.1 + 1, up q.1.1 q.1.2⟩ : Σ s, blk s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = i).card = m) := by
  intro pa
  refine ⟨?_, fun i => (hrange i.1 i.2).1, ?_⟩
  · intro i hi
    by_cases h : nd ⟨i.1.1 + 1, up i.1.1 i.1.2⟩ ∧ i.1.1 + 1 ≤ top
    · simp only [pa, h, and_self, dite_true]
    · exact absurd (by simp only [pa, h, dite_false]) hi
  · intro i
    obtain ⟨⟨s, y⟩, hi⟩ := i
    have hr := hrange _ hi
    simp only at hr
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have h := graded_children_sum blk up nd hrange (fun _ => (1 : ℕ)) y hi
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    rw [h]
    exact hcard s' y

end Graded

end Balaban.LargeField
