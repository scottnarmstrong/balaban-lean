/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedWindowAncCore

/-!
# The regrouping of the removed-outcome window integral: disjoint ancestor variables (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, step (1).  The ancestors `P ≠ P'` of a component
`Z` at the same scale `s` read disjoint coordinates of the internal variables of `Z`: the variable
of `Z` that is the variable `(j, κ, y)` of `P` (inclusion `inclVar_mem`) is never the variable of
`P'`, because the variable sets of two components of the same scale share no block
(`locOp_factor`).  Also the inclusion is injective for a fixed ancestor.

* `incl_ne_of_ne`: different ancestors, different coordinates;
* `incl_injective`: the inclusion of the variables of one ancestor is injective.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Disj

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

/-- **Ancestors at the same scale read disjoint coordinates** (Lemma III.8.7 (4), step (1)): for
`P ≠ P'` at scale `s` that are both ancestors of `Z`, no variable of `P` and variable of `P'`
become the same coordinate of the internal variables of `Z`. -/
theorem incl_ne_of_ne {s m : ℕ} (hm : m ≤ K) {Z : H.Comp m} {P P' : H.Comp s}
    (h : H.Desc s m P Z) (h' : H.Desc s m P' Z) (hne : P ≠ P')
    (p : InternalVars (H.localHistory M K s P) s) (p' : InternalVars (H.localHistory M K s P') s) :
    (⟨⟨Fin.castLE h.le p.1.1, p.1.2.1, p.1.2.2⟩, inclVar_mem hm h p⟩ :
        InternalVars (H.localHistory M K m Z) m) ≠
      ⟨⟨Fin.castLE h'.le p'.1.1, p'.1.2.1, p'.1.2.2⟩, inclVar_mem hm h' p'⟩ := by
  intro heq
  have h1 := congrArg (fun q : InternalVars (H.localHistory M K m Z) m => q.1) heq
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨hj, hh⟩ := h1
  rcases p with ⟨⟨⟨j, hjs⟩, κ, b⟩, hb⟩
  rcases p' with ⟨⟨⟨j', hjs'⟩, κ', b'⟩, hb'⟩
  have hjj : j = j' := by
    have := congrArg Fin.val hj
    simpa using this
  subst hjj
  have hh' : (κ, b) = (κ', b') := eq_of_heq hh
  simp only [Prod.mk.injEq] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  have hsm := h.le
  exact (locOp_factor (H := H) (one_le_of_comp P) (by omega) hne).2 j (by omega) b κ κ ⟨hb, hb'⟩

/-- The inclusion of the variables of one ancestor into those of the descendant is injective. -/
theorem incl_injective {s m : ℕ} (hm : m ≤ K) {Z : H.Comp m} {P : H.Comp s}
    (h : H.Desc s m P Z) :
    Function.Injective fun p : InternalVars (H.localHistory M K s P) s =>
      (⟨⟨Fin.castLE h.le p.1.1, p.1.2.1, p.1.2.2⟩, inclVar_mem hm h p⟩ :
        InternalVars (H.localHistory M K m Z) m) := by
  intro p p' heq
  have h1 := congrArg (fun q : InternalVars (H.localHistory M K m Z) m => q.1) heq
  simp only [Sigma.mk.injEq] at h1
  obtain ⟨hj, hh⟩ := h1
  rcases p with ⟨⟨⟨j, hjs⟩, κ, b⟩, hb⟩
  rcases p' with ⟨⟨⟨j', hjs'⟩, κ', b'⟩, hb'⟩
  have hjj : j = j' := by
    have := congrArg Fin.val hj
    simpa using this
  subst hjj
  have hh' : (κ, b) = (κ', b') := eq_of_heq hh
  simp only [Prod.mk.injEq] at hh'
  obtain ⟨rfl, rfl⟩ := hh'
  rfl

end Disj

end Balaban.LargeField
