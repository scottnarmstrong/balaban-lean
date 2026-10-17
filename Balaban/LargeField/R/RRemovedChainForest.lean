/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainProd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Forests of Gaussian blocks: one block tree per root (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (a), (b) (generic part).  A finite forest
(nodes `ι`, scales `sc`, parent `pa` with the roots the fixed points of `pa`, leaves `Lf` attached by
`lp`, every node having `m` children) is the disjoint union of the trees of its roots `r`; the nodes
of the tree of `r` are those `i` with `pa^[card ι] i = r`.  Each tree is a `BlockTree`
(`exists_blockTree_of_tree`); `forest_trees` collects them, and `prod_forest_eq_windowIntegrand` is the
identity of the product over all nodes of the Gaussian factors with the product over the roots of the
`windowIntegrand`s of the trees.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

section Forest

variable {m k1 : ℕ} {ι Lf : Type} [Fintype ι] [DecidableEq ι] [Fintype Lf]
  (sc : ι → ℕ) (pa : ι → ι) (lp : Lf → ι)

/-- The root of the tree of a node. -/
theorem iter_fixed {r : ι} (h : pa r = r) (t : ℕ) : pa^[t] r = r :=
  Function.iterate_fixed h t

/-- After `card ι` steps every node has reached a root. -/
theorem pa_iter_card_fixed (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1) (i : ι) :
    pa (pa^[Fintype.card ι] i) = pa^[Fintype.card ι] i := by
  by_contra hne
  have hnf : ∀ t, t ≤ Fintype.card ι → pa (pa^[t] i) ≠ pa^[t] i := by
    intro t ht hfix
    apply hne
    have h1 : pa^[Fintype.card ι] i = pa^[Fintype.card ι - t] (pa^[t] i) := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h1, iter_fixed pa hfix]
    exact hfix
  have hsc : ∀ t, t ≤ Fintype.card ι + 1 → sc (pa^[t] i) = sc i + t := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', hpa _ (hnf t (by omega)), ih (by omega)]
      ring
  have hinj : Function.Injective (fun t : Fin (Fintype.card ι + 1) => pa^[t.1] i) := by
    intro a b hab
    have h1 := hsc a.1 (by omega)
    have h2 := hsc b.1 (by omega)
    have : sc i + a.1 = sc i + b.1 := by
      rw [← h1, ← h2]
      exact congrArg sc hab
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem pa_iter_card_pa (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1) (i : ι) :
    pa^[Fintype.card ι] (pa i) = pa^[Fintype.card ι] i := by
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact pa_iter_card_fixed sc pa hpa i

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **(a), (b) for the tree of one root.**  In a finite forest with `m` children at every node, the
nodes below the root `r` form a block tree `B` (numbering `e` of the nodes, `el` of the leaves of these
nodes): `e` respects scales and parents, and `windowIntegrand` of `B` at the values `Ψ`, `Ψl` is the
product over the nodes below `r` of the Gaussian factors
`z_{s_i}^{dim V} g_{c_{s_i - 1}}(z_{s_i} Ψ_i - m⁻¹ (∑_{children nodes} Ψ + ∑_{children leaves} Ψl))`. -/
theorem forest_tree_of_root (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1)
    (hge : ∀ i, k1 + 1 ≤ sc i)
    (hfull : ∀ i, (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l => lp l = i).card = m)
    (r : ι) (hr : pa r = r) :
    ∃ (B : BlockTree m k1 (sc r))
      (e : {i // pa^[Fintype.card ι] i = r} ≃ Fin (B.n + 1))
      (el : {l : Lf // pa^[Fintype.card ι] (lp l) = r} ≃ Fin B.nLeaf),
      (e ⟨r, iter_fixed pa hr _⟩ : ℕ) = 0 ∧ (∀ i, B.scale (e i) = sc i.1) ∧
      (∀ i, i.1 ≠ r → B.par (e i) = e ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩) ∧
      (∀ l, B.leafPar (el l) = e ⟨lp l.1, l.2⟩) ∧
      ∀ (c z : ℕ → ℝ) (Ψ : ι → V) (Ψl : Lf → V),
        B.windowIntegrand c z (fun x => Ψl (el.symm x).1)
            (fun i => if h : i < B.n + 1 then Ψ (e.symm ⟨i, h⟩).1 else 0) =
          ∏ i : {i // pa^[Fintype.card ι] i = r}, z (sc i.1) ^ Module.finrank ℝ V *
            gaussDens (c (sc i.1 - 1)) (z (sc i.1) • Ψ i.1 - (m : ℝ)⁻¹ •
              ((∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i.1), Ψ j) +
                ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i.1), Ψl l)) := by
  classical
  have hrt := pa_iter_card_pa sc pa hpa
  have hrr : pa^[Fintype.card ι] r = r := iter_fixed pa hr _
  let sc' : {i // pa^[Fintype.card ι] i = r} → ℕ := fun i => sc i.1
  let pa' : {i // pa^[Fintype.card ι] i = r} → {i // pa^[Fintype.card ι] i = r} :=
    fun i => ⟨pa i.1, (hrt i.1).trans i.2⟩
  let lp' : {l : Lf // pa^[Fintype.card ι] (lp l) = r} → {i // pa^[Fintype.card ι] i = r} :=
    fun l => ⟨lp l.1, l.2⟩
  let r' : {i // pa^[Fintype.card ι] i = r} := ⟨r, hrr⟩
  have hnotfix : ∀ i : {i // pa^[Fintype.card ι] i = r}, i ≠ r' → pa i.1 ≠ i.1 := by
    intro i hi hfix
    apply hi
    apply Subtype.ext
    have := i.2
    rw [iter_fixed pa hfix] at this
    exact this
  have h1 : ∀ i, i ≠ r' → sc' (pa' i) = sc' i + 1 := fun i hi => hpa _ (hnotfix i hi)
  have h2 : ∀ i, k1 + 1 ≤ sc' i := fun i => hge _
  have h3 : ∀ i : {i // pa^[Fintype.card ι] i = r},
      (Finset.univ.filter fun c : {i // pa^[Fintype.card ι] i = r} => c ≠ r' ∧ pa' c = i).card +
        (Finset.univ.filter fun l : {l : Lf // pa^[Fintype.card ι] (lp l) = r} => lp' l = i).card
        = m := by
    intro i
    rw [← hfull i.1]
    congr 1
    · refine Finset.card_bij (fun c _ => c.1) ?_ ?_ ?_
      · intro c hc
        have hc' := (Finset.mem_filter.mp hc).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotfix c hc'.1, congrArg Subtype.val hc'.2⟩
      · intro c c' _ _ h
        exact Subtype.ext h
      · intro c hc
        have hc' := (Finset.mem_filter.mp hc).2
        have hmem : pa^[Fintype.card ι] c = r := by rw [← hrt c, hc'.2]; exact i.2
        refine ⟨⟨c, hmem⟩, ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, Subtype.ext hc'.2⟩
        intro h
        apply hc'.1
        have := congrArg Subtype.val h
        simp only [r'] at this
        rw [this]; exact hr
    · refine Finset.card_bij (fun l _ => l.1) ?_ ?_ ?_
      · intro l hl
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Subtype.val (Finset.mem_filter.mp hl).2⟩
      · intro l l' _ _ h
        exact Subtype.ext h
      · intro l hl
        have hl' := (Finset.mem_filter.mp hl).2
        have hmem : pa^[Fintype.card ι] (lp l) = r := by rw [hl']; exact i.2
        exact ⟨⟨l, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hl'⟩, rfl⟩
  obtain ⟨B, e, el, he0, hsc, hpar, hleaf⟩ := exists_blockTree_of_tree sc' pa' lp' r' rfl h1 h2 h3
  refine ⟨B, e, el, he0, hsc, fun i hi => hpar i (fun h => hi (congrArg Subtype.val h)), hleaf,
    fun c z Ψ Ψl => ?_⟩
  rw [windowIntegrand_eq_prod (sc := sc') (pa := pa') (lp := lp') (r := r') B e el he0 hsc hpar hleaf c z
    (fun i => Ψ i.1) (fun l => Ψl l.1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e1 : ∑ j ∈ Finset.univ.filter (fun j : {i // pa^[Fintype.card ι] i = r} => j ≠ r' ∧ pa' j = i),
      Ψ j.1 = ∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i.1), Ψ j := by
    refine Finset.sum_bij (fun j _ => j.1) ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotfix j hj'.1, congrArg Subtype.val hj'.2⟩
    · intro j j' _ _ h
      exact Subtype.ext h
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hmem : pa^[Fintype.card ι] j = r := by rw [← hrt j, hj'.2]; exact i.2
      refine ⟨⟨j, hmem⟩, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, Subtype.ext hj'.2⟩
      intro h
      apply hj'.1
      have := congrArg Subtype.val h
      simp only [r'] at this
      rw [this]; exact hr
    · intro j _
      rfl
  have e2 : ∑ l ∈ Finset.univ.filter (fun l : {l : Lf // pa^[Fintype.card ι] (lp l) = r} => lp' l = i),
      Ψl l.1 = ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i.1), Ψl l := by
    refine Finset.sum_bij (fun l _ => l.1) ?_ ?_ ?_ ?_
    · intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Subtype.val (Finset.mem_filter.mp hl).2⟩
    · intro l l' _ _ h
      exact Subtype.ext h
    · intro l hl
      have hl' := (Finset.mem_filter.mp hl).2
      have hmem : pa^[Fintype.card ι] (lp l) = r := by rw [hl']; exact i.2
      exact ⟨⟨l, hmem⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hl'⟩, rfl⟩
    · intro l _
      rfl
  rw [e1, e2]

/-- The nodes of a forest are the disjoint union of the trees of the roots. -/
theorem prod_forest_eq {R : Type*} [CommMonoid R] (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1)
    (f : ι → R) :
    ∏ i, f i = ∏ r : {r : ι // pa r = r}, ∏ i : {i : ι // pa^[Fintype.card ι] i = r.1}, f i.1 := by
  classical
  have h := Fintype.prod_sigma (fun p : (r : {r : ι // pa r = r}) ×
    {i : ι // pa^[Fintype.card ι] i = r.1} => f p.2.1)
  simp only at h
  rw [← h]
  refine (Fintype.prod_equiv (Equiv.mk (fun i : ι => (⟨⟨pa^[Fintype.card ι] i,
      pa_iter_card_fixed sc pa hpa i⟩, ⟨i, rfl⟩⟩ : (r : {r : ι // pa r = r}) ×
        {i : ι // pa^[Fintype.card ι] i = r.1}))
    (fun p => p.2.1) (fun i => rfl) (fun p => by
      obtain ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ := p
      simp only at hi ⊢
      subst hi
      rfl)) _ _ (fun i => rfl))

/-- **(a) and (b) for a forest.**  There is a block tree `B r` for every root `r`, with numberings of
the nodes below `r` and of their leaves respecting scales, parents and leaf parents, such that the
product over all nodes of the Gaussian factors is the product over the roots of the `windowIntegrand`s. -/
theorem forest_trees (hpa : ∀ i, pa i ≠ i → sc (pa i) = sc i + 1) (hge : ∀ i, k1 + 1 ≤ sc i)
    (hfull : ∀ i, (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l => lp l = i).card = m) :
    ∃ (B : ∀ r : {r : ι // pa r = r}, BlockTree m k1 (sc r.1))
      (e : ∀ r : {r : ι // pa r = r}, {i // pa^[Fintype.card ι] i = r.1} ≃ Fin ((B r).n + 1))
      (el : ∀ r : {r : ι // pa r = r},
        {l : Lf // pa^[Fintype.card ι] (lp l) = r.1} ≃ Fin (B r).nLeaf),
      (∀ r, (e r ⟨r.1, iter_fixed pa r.2 _⟩ : ℕ) = 0) ∧
      (∀ r i, (B r).scale (e r i) = sc i.1) ∧
      (∀ r i, i.1 ≠ r.1 →
        (B r).par (e r i) = e r ⟨pa i.1, (pa_iter_card_pa sc pa hpa i.1).trans i.2⟩) ∧
      (∀ r l, (B r).leafPar (el r l) = e r ⟨lp l.1, l.2⟩) ∧
      ∀ (c z : ℕ → ℝ) (Ψ : ι → V) (Ψl : Lf → V),
        ∏ i : ι, z (sc i) ^ Module.finrank ℝ V *
            gaussDens (c (sc i - 1)) (z (sc i) • Ψ i - (m : ℝ)⁻¹ •
              ((∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i), Ψ j) +
                ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i), Ψl l)) =
          ∏ r : {r : ι // pa r = r}, (B r).windowIntegrand c z (fun x => Ψl ((el r).symm x).1)
            (fun i => if h : i < (B r).n + 1 then Ψ ((e r).symm ⟨i, h⟩).1 else 0) := by
  classical
  choose B e el he0 hsc hpar hleaf hid using
    fun r : {r : ι // pa r = r} => forest_tree_of_root (V := V) sc pa lp hpa hge hfull r.1 r.2
  refine ⟨B, e, el, he0, hsc, hpar, hleaf, fun c z Ψ Ψl => ?_⟩
  rw [prod_forest_eq sc pa hpa (fun i => z (sc i) ^ Module.finrank ℝ V *
    gaussDens (c (sc i - 1)) (z (sc i) • Ψ i - (m : ℝ)⁻¹ •
      ((∑ j ∈ Finset.univ.filter (fun j : ι => pa j ≠ j ∧ pa j = i), Ψ j) +
        ∑ l ∈ Finset.univ.filter (fun l : Lf => lp l = i), Ψl l)))]
  exact Finset.prod_congr rfl fun r _ => (hid r c z Ψ Ψl).symm

end Forest

end Balaban.LargeField
