/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block tree of a finite rooted tree (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (a).  A finite rooted tree of Gaussian blocks
(nodes `ι` with scales `sc`, parent map `pa`, root `r`, and the leaves `Lf` attached to nodes by
`lp`, every node having `m` children among nodes and leaves) is numbered by `0, …, n` so that parents
come first; this is a `BlockTree m k1 k` (`exists_blockTree_of_tree`), and `windowIntegrand` of it
is the product over the nodes of the Gaussian factors (`windowIntegrand_eq_prod`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section Tree

variable {m k1 k : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι) (r : ι)

/-- In a finite rooted tree, the scale of a node is at most that of the root, strictly so for
the other nodes. -/
theorem tree_sc_lt (hpa : ∀ i, i ≠ r → sc (pa i) = sc i + 1) :
    ∀ i, i ≠ r → sc i < sc r := by
  have hmax : ∀ i, sc i ≤ sc r := by
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image (Finset.univ : Finset ι) sc ⟨r, Finset.mem_univ r⟩
    have h0 : sc i0 ≤ sc r := by
      by_contra hlt
      have hne : i0 ≠ r := fun h => hlt (h ▸ le_rfl)
      have := hi0 (pa i0) (Finset.mem_univ _)
      rw [hpa i0 hne] at this
      omega
    exact fun i => (hi0 i (Finset.mem_univ i)).trans h0
  intro i hi
  have h1 := hmax (pa i)
  rw [hpa i hi] at h1
  omega

/-- **(a) The block tree of a finite rooted tree**: a finite rooted tree whose nodes have scales
`sc` (the parent has scale one higher, all scales are at least `k₁ + 1`), root `r` of scale `k`, and
`m` children (nodes and leaves) at every node, is a `BlockTree m k₁ k`: its nodes are numbered
`0, …, n` (root `0`, parents first), and the numbering respects scales, parents and leaf parents. -/
theorem exists_blockTree_of_tree
    (hr : sc r = k) (hpa : ∀ i, i ≠ r → sc (pa i) = sc i + 1) (hge : ∀ i, k1 + 1 ≤ sc i)
    (hfull : ∀ i, (Finset.univ.filter fun c => c ≠ r ∧ pa c = i).card +
        (Finset.univ.filter fun l => lp l = i).card = m) :
    ∃ (B : BlockTree m k1 k) (e : ι ≃ Fin (B.n + 1)) (el : Lf ≃ Fin B.nLeaf),
      (e r : ℕ) = 0 ∧ (∀ i, B.scale (e i) = sc i) ∧ (∀ i, i ≠ r → B.par (e i) = e (pa i)) ∧
      ∀ l, B.leafPar (el l) = e (lp l) := by
  classical
  have hlt := tree_sc_lt sc pa r hpa
  let eqv := Fintype.equivFin ι
  let key : ι → ℕ ×ₗ ℕ := fun i => toLex (sc r - sc i, (eqv i : ℕ))
  have hkey : Function.Injective key := by
    intro i j h
    have := congrArg (fun p => (ofLex p).2) h
    exact eqv.injective (Fin.ext this)
  let _ : LinearOrder ι := LinearOrder.lift' key hkey
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨r⟩
  let n : ℕ := Fintype.card ι - 1
  have hn : Fintype.card ι = n + 1 := by omega
  let E : Fin (n + 1) ≃o ι := Fintype.orderIsoFinOfCardEq ι hn
  have hlt_iff : ∀ i j : ι, i < j ↔ key i < key j := fun i j => Iff.rfl
  have hr_min : ∀ i, i ≠ r → r < i := by
    intro i hi
    rw [hlt_iff, Prod.Lex.lt_iff]
    left
    have := hlt i hi
    show sc r - sc r < sc r - sc i
    omega
  have hE0 : E ⟨0, Nat.succ_pos n⟩ = r := by
    by_contra hne
    have h1 := hr_min _ hne
    have h2 : E ⟨0, Nat.succ_pos n⟩ ≤ r := by
      have : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) ≤ E.symm r := Fin.zero_le _
      simpa using E.monotone this
    exact absurd h1 (not_lt.mpr h2)
  have hpar_lt : ∀ i, i ≠ r → pa i < i := by
    intro i hi
    rw [hlt_iff, Prod.Lex.lt_iff]
    left
    have := hlt i hi
    have := hpa i hi
    show sc r - sc (pa i) < sc r - sc i
    have := hlt (pa i)
    omega
  let el : Lf ≃ Fin (Fintype.card Lf) := Fintype.equivFin Lf
  let sc' : ℕ → ℕ := fun i => if h : i < n + 1 then sc (E ⟨i, h⟩) else 0
  let par' : ℕ → ℕ := fun i => if h : i < n + 1 then ((E.symm (pa (E ⟨i, h⟩)) : Fin (n + 1)) : ℕ) else 0
  let lp' : Fin (Fintype.card Lf) → ℕ := fun x => ((E.symm (lp (el.symm x)) : Fin (n + 1)) : ℕ)
  have hsc' : ∀ (i : Fin (n + 1)), sc' i = sc (E i) := by
    intro i; have h := Nat.not_lt.mpr (Nat.lt_succ_iff.mp i.2); simp [sc', h]
  have hpar' : ∀ (i : Fin (n + 1)), par' i = (E.symm (pa (E i)) : ℕ) := by
    intro i; have h := Nat.not_lt.mpr (Nat.lt_succ_iff.mp i.2); simp [par', h]
  refine ⟨⟨n, sc', par', Fintype.card Lf, lp', ?_, ?_, ?_, ?_, ?_, ?_⟩,
    E.symm.toEquiv, el, ?_, ?_, ?_, ?_⟩
  · have := hsc' ⟨0, Nat.succ_pos n⟩
    simp only at this ⊢
    rw [this, hE0, hr]
  · intro i hi hi0
    have hi' : i < n + 1 := Nat.lt_succ_of_le hi
    have h1 := hpar' ⟨i, hi'⟩
    simp only at h1
    rw [h1]
    have hne : E ⟨i, hi'⟩ ≠ r := by
      intro h
      rw [← hE0] at h
      have := E.injective h
      exact hi0 (by simpa using congrArg Fin.val this)
    have := hpar_lt _ hne
    have h2 : E.symm (pa (E ⟨i, hi'⟩)) < ⟨i, hi'⟩ := by
      rw [← E.symm.lt_iff_lt] at this
      simpa using this
    exact h2
  · intro i hi hi0
    have hi' : i < n + 1 := Nat.lt_succ_of_le hi
    have hne : E ⟨i, hi'⟩ ≠ r := by
      intro h
      rw [← hE0] at h
      have := E.injective h
      exact hi0 (by simpa using congrArg Fin.val this)
    have h1 := hpar' ⟨i, hi'⟩
    simp only at h1
    rw [h1]
    have h2 := hsc' (E.symm (pa (E ⟨i, hi'⟩)))
    rw [h2]
    simp only [OrderIso.apply_symm_apply]
    rw [hpa _ hne]
    have := hsc' ⟨i, hi'⟩
    simp only at this
    rw [this]
  · intro i hi
    by_cases h : i < n + 1
    · have := hsc' ⟨i, h⟩
      simp only at this
      rw [this]; exact hge _
    · simp only [sc', h, dite_false]; omega
  · intro x
    exact Nat.lt_succ_iff.mp (E.symm (lp (el.symm x))).2
  · intro i hi
    have hi' : i < n + 1 := Nat.lt_succ_of_le hi
    have h1 := hfull (E ⟨i, hi'⟩)
    rw [← h1]
    congr 1
    · refine Finset.card_bij (fun c hc => E ⟨c, Finset.mem_range.mp (Finset.mem_filter.mp hc).1⟩) ?_ ?_ ?_
      · intro c hc
        have hcf := Finset.mem_filter.mp hc
        have hc2 := hcf.2.1
        have hc3 := hcf.2.2
        have hcn := Finset.mem_range.mp hcf.1
        have h4 := hpar' ⟨c, hcn⟩
        simp only at h4
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro h
          rw [← hE0] at h
          have := E.injective h
          exact hc2 (by simpa using congrArg Fin.val this)
        · have h5 : E.symm (pa (E ⟨c, hcn⟩)) = ⟨i, hi'⟩ := Fin.ext (h4 ▸ hc3)
          rw [← h5]; simp
      · intro c c' hc hc' h
        have := E.injective h
        simpa using congrArg Fin.val this
      · intro j hj
        obtain ⟨-, hj1, hj2⟩ := Finset.mem_filter.mp hj
        refine ⟨(E.symm j : ℕ), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (E.symm j).2, ?_, ?_⟩
          · intro h
            apply hj1
            have : E.symm j = ⟨0, Nat.succ_pos n⟩ := Fin.ext h
            rw [← hE0, ← this]; simp
          · have h4 := hpar' (E.symm j)
            rw [h4]
            simp only [OrderIso.apply_symm_apply, hj2]
            simp
        · simp
    · refine Finset.card_bij (fun x _ => el.symm x) ?_ ?_ ?_
      · intro x hx
        have := (Finset.mem_filter.mp hx).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have h5 : E.symm (lp (el.symm x)) = ⟨i, hi'⟩ := Fin.ext this
        rw [← h5]; simp
      · intro x x' _ _ h
        exact el.symm.injective h
      · intro l hl
        refine ⟨el l, ?_, by simp⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have := (Finset.mem_filter.mp hl).2
        show ((E.symm (lp (el.symm (el l))) : Fin (n + 1)) : ℕ) = i
        simp only [Equiv.symm_apply_apply, this]
        simp
  · show ((E.symm r : Fin (n + 1)) : ℕ) = 0
    rw [← hE0]; simp
  · intro i
    have := hsc' (E.symm i)
    simp only [OrderIso.apply_symm_apply] at this
    exact this
  · intro i hi
    have h4 := hpar' (E.symm i)
    simp only [OrderIso.apply_symm_apply] at h4
    exact h4
  · intro l
    simp [lp']

end Tree

end Balaban.LargeField
