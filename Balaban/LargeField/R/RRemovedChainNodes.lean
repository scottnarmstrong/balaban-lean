/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainLevel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The forest of the Gaussian blocks of a quiet window (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (a), (b).  The Gaussian blocks of the
ancestors of `Z` of scales `k₁ + 1, …, m' + 1` (the nodes) form a forest (`graded_forest`): the
parent of a node is its coarsening if that is a node.  `prod_nodes_eq` writes a product over the nodes
as the iterated product over the scales and the Gaussian blocks of the right-hand side of
`gaussProd_unroll_eq`, `card_fibre_up` is the fibre count `L^d` of the coarsening, and
`gauss_forest_trees` is `forest_trees` for this forest: the product of the Gaussian factors of
`gaussProd_unroll_eq` is the product over the roots of the `windowIntegrand`s of block trees, with
node values `ψ` and leaf values read from a field `fld`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Nodes

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- Every block of scale `s + 1` has `L^d` children of scale `s`. -/
theorem card_fibre_up {s : ℕ} (hs : s + 1 ≤ K) (y : BlockAt S n M K (s + 1)) :
    (Finset.univ.filter fun y' : BlockAt S n M K s =>
      blockMap S.L (M * n K * S.L ^ (K - (s + 1))) y' = y).card = S.L ^ S.d := by
  have hℓ : M * n K * S.L ^ (K - s) = S.L * (M * n K * S.L ^ (K - (s + 1))) := by
    rw [show K - s = (K - (s + 1)) + 1 by omega, pow_succ]
    ring
  exact card_blockFibre hℓ y

open Classical in
/-- A product over the nodes is the iterated product over the scales and the blocks of that scale
that are nodes. -/
theorem prod_nodes_eq {β : Type*} [CommMonoid β] {k1 m' : ℕ}
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    (hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ m' + 1)
    (f : {b : Σ s, BlockAt S n M K s // nd b} → β) :
    ∏ b : {b : Σ s, BlockAt S n M K s // nd b}, f b =
      ∏ j ∈ Finset.Ico k1 (m' + 1), ∏ y : {y : BlockAt S n M K (j + 1) // nd ⟨j + 1, y⟩},
        f ⟨⟨j + 1, y.1⟩, y.2⟩ := by
  classical
  rw [Finset.prod_sigma']
  symm
  refine Finset.prod_bij (fun p hp => (⟨⟨p.1 + 1, p.2.1⟩, p.2.2⟩ :
    {b : Σ s, BlockAt S n M K s // nd b})) ?_ ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_univ _
  · rintro ⟨j, y⟩ _ ⟨j', y'⟩ _ h
    have h1 := congrArg Subtype.val h
    simp only [Sigma.mk.inj_iff] at h1
    obtain ⟨h2, h3⟩ := h1
    have hj : j = j' := by omega
    subst hj
    rw [Subtype.ext (eq_of_heq h3)]
  · rintro ⟨⟨s, y⟩, hb⟩ _
    obtain ⟨j, rfl⟩ : ∃ j, s = j + 1 := ⟨s - 1, by have : k1 + 1 ≤ s := (hrange _ hb).1; omega⟩
    have h : k1 + 1 ≤ j + 1 ∧ j + 1 ≤ m' + 1 := hrange _ hb
    refine ⟨⟨j, ⟨y, hb⟩⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Ico.mpr
      ⟨show k1 ≤ j by omega, show j < m' + 1 by omega⟩, Finset.mem_univ _⟩, rfl⟩
  · intro p hp
    rfl

open Classical in
/-- **(a), (b) for the Gaussian blocks of the window.**  Let `nd` be the set of nodes: the Gaussian
blocks `y` of the ancestors `c` of `Z` of scales `j + 1`, `k₁ ≤ j ≤ m'` (`hnd`), and `pa` the parent map
(the coarsening of a node if it is a node, the node itself otherwise).  For any fields `fld` (read at
the scales `≤ m'`) and `ft` (the top scale `m' + 1`), the product of the Gaussian factors of
`gaussProd_unroll_eq` (top step, then the steps `j`, `k₁ ≤ j < m'`) is the product over the roots `r`
of the `windowIntegrand`s of block trees `B r`: the node values are `ψ`, equal to `fld` at the scales
`≤ m'` and to `ft` at the scale `m' + 1`, and the leaf values are `fld` at the children of nodes that are
not nodes.  The numberings `e r` of the nodes below `r` and `el r` of their leaves respect scales,
parents and leaf parents. -/
theorem gauss_forest_trees {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (c z : ℕ → ℝ) (ψ : (Σ s, BlockAt S n M K s) → EuclideanSpace ℝ (Fin N))
    (fld : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ : ∀ s y, s ≤ m' → ψ ⟨s, y⟩ = fld s y) (hψt : ∀ y, ψ ⟨m' + 1, y⟩ = ft y) :
    ∃ (B : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
        BlockTree (S.L ^ S.d) k1 r.1.1.1)
      (e : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
        {i : {b : Σ s, BlockAt S n M K s // nd b} //
          pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] i = r.1} ≃ Fin ((B r).n + 1))
      (el : ∀ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
        {l : {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
            (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
              Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} //
          pa^[Fintype.card {b : Σ s, BlockAt S n M K s // nd b}] l.1.2 = r.1} ≃ Fin (B r).nLeaf),
      (∀ r i, i.1 = r.1 → (e r i : ℕ) = 0) ∧ (∀ r i, (B r).scale (e r i) = i.1.1.1) ∧
      (∀ r i i', i.1 ≠ r.1 → i'.1 = pa i.1 → (B r).par (e r i) = e r i') ∧
      (∀ r l i, i.1 = l.1.1.2 → (B r).leafPar (el r l) = e r i) ∧
      (((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
          ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
            y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
        z (m' + 1) ^ N * gaussDens (c m')
          (z (m' + 1) • ft y - ((S.L : ℝ) ^ S.d)⁻¹ •
            ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
              blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld m' y')) *
      ∏ j ∈ Finset.Ico k1 m',
        ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
            ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
          z (j + 1) ^ N * gaussDens (c j)
            (z (j + 1) • fld (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld j y')) =
        ∏ r : {r : {b : Σ s, BlockAt S n M K s // nd b} // pa r = r},
          (B r).windowIntegrand c z (fun x => fld ((el r).symm x).1.1.1.1 ((el r).symm x).1.1.1.2)
            (fun i => if h : i < (B r).n + 1 then ψ ((e r).symm ⟨i, h⟩).1.1 else 0)) := by
  classical
  have hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ m' + 1 := by
    rintro ⟨s, y⟩ h
    cases s with
    | zero => exact absurd h (hnd0 y)
    | succ j =>
      obtain ⟨h1, h2, -⟩ := (hnd j y).mp h
      exact ⟨by show k1 + 1 ≤ j + 1; omega, by show j + 1 ≤ m' + 1; omega⟩
  have hfl : Finite {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} :=
    finite_graded_leaves (fun s => BlockAt S n M K s)
      (fun s => blockMap S.L (M * n K * S.L ^ (K - (s + 1)))) nd (top := m' + 1)
      (fun b hb => (hrange b hb).2)
  have : Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} := Fintype.ofFinite _
  have hcard : ∀ s (y : BlockAt S n M K (s + 1)), nd ⟨s + 1, y⟩ →
      (Finset.univ.filter fun y' : BlockAt S n M K s =>
        blockMap S.L (M * n K * S.L ^ (K - (s + 1))) y' = y).card = S.L ^ S.d := by
    intro s y hy
    have h2 : s + 1 ≤ m' + 1 := (hrange _ hy).2
    exact card_fibre_up (by omega) y
  have hg := graded_forest (m := S.L ^ S.d) (k1 := k1) (top := m' + 1)
    (fun s => BlockAt S n M K s) (fun s => blockMap S.L (M * n K * S.L ^ (K - (s + 1)))) nd
    hcard hrange
  obtain ⟨g1, g2, g3⟩ := hg
  have hpaeq : pa = fun b => if h : nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1)))
      b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 then ⟨⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1)))
      b.1.2⟩, h.1⟩ else b := by
    funext b
    split_ifs with h
    · exact Subtype.ext ((hpa b).1 h)
    · exact (hpa b).2 h
  have g1' : ∀ i : {b : Σ s, BlockAt S n M K s // nd b}, pa i ≠ i → i.1.1 + 1 = (pa i).1.1 := by
    subst hpaeq
    exact g1
  have g3' : ∀ i : {b : Σ s, BlockAt S n M K s // nd b},
      (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l : {q : (Σ s, BlockAt S n M K s) ×
          {b : Σ s, BlockAt S n M K s // nd b} //
        (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
          Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = i).card = S.L ^ S.d := by
    subst hpaeq
    exact g3
  obtain ⟨B, e, el, he0, hsc, hpar, hleaf, hprod⟩ := forest_trees (m := S.L ^ S.d) (k1 := k1)
    (V := EuclideanSpace ℝ (Fin N)) (fun i => i.1.1) pa
    (Lf := {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}) (fun l => l.1.2)
    (fun i hi => (g1' i hi).symm) g2 g3'
  refine ⟨B, e, el, ?_, hsc, ?_, ?_, ?_⟩
  · intro r i hi
    have h : i = ⟨r.1, iter_fixed _ r.2 _⟩ := Subtype.ext hi
    rw [h]
    exact he0 r
  · intro r i i' hi hi'
    refine (hpar r i hi).trans (congrArg (fun a => ((e r a : Fin ((B r).n + 1)) : ℕ)) ?_)
    exact Subtype.ext hi'.symm
  · intro r l i hi
    refine (hleaf r l).trans (congrArg (fun a => ((e r a : Fin ((B r).n + 1)) : ℕ)) ?_)
    exact Subtype.ext hi.symm
  refine Eq.trans ?_ (hprod c z (fun i => ψ i.1) (fun l => fld l.1.1.1 l.1.1.2))
  have hsum : ∀ j, j ≤ m' → ∀ (y : BlockAt S n M K (j + 1)) (h : nd ⟨j + 1, y⟩),
      (∑ j' ∈ Finset.univ.filter (fun j' : {b : Σ s, BlockAt S n M K s // nd b} =>
          pa j' ≠ j' ∧ pa j' = ⟨⟨j + 1, y⟩, h⟩), ψ j'.1) +
        ∑ l ∈ Finset.univ.filter (fun l : {q : (Σ s, BlockAt S n M K s) ×
            {b : Σ s, BlockAt S n M K s // nd b} //
          (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
            Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = ⟨⟨j + 1, y⟩, h⟩),
          fld l.1.1.1 l.1.1.2 =
        ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
          blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld j y' := by
    intro j hj y h
    have h1 : ∑ j' ∈ Finset.univ.filter (fun j' : {b : Σ s, BlockAt S n M K s // nd b} =>
          pa j' ≠ j' ∧ pa j' = ⟨⟨j + 1, y⟩, h⟩), ψ j'.1 =
        ∑ j' ∈ Finset.univ.filter (fun j' : {b : Σ s, BlockAt S n M K s // nd b} =>
          pa j' ≠ j' ∧ pa j' = ⟨⟨j + 1, y⟩, h⟩), fld j'.1.1 j'.1.2 := by
      refine Finset.sum_congr rfl fun j' hj' => ?_
      obtain ⟨hne, hpj⟩ := (Finset.mem_filter.mp hj').2
      have h2 := g1' j' hne
      rw [hpj] at h2
      have h3 : j'.1.1 + 1 = j + 1 := h2
      have h4 : j'.1.1 ≤ m' := by omega
      exact hψ j'.1.1 j'.1.2 h4
    rw [h1]
    subst hpaeq
    exact graded_children_sum (k1 := k1) (top := m' + 1)
      (fun s => BlockAt S n M K s) (fun s => blockMap S.L (M * n K * S.L ^ (K - (s + 1)))) nd
      hrange (fun b => fld b.1 b.2) y h
  rw [prod_nodes_eq nd hrange, Finset.prod_Ico_succ_top hk1, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hjm : j < m' := (Finset.mem_Ico.mp hj).2
    have hiff : ∀ y : BlockAt S n M K (j + 1), y ∈ (Finset.univ.filter fun y : BlockAt S n M K (j + 1) =>
        ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j) ↔
        nd ⟨j + 1, y⟩ := by
      intro y
      rw [hnd]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨(Finset.mem_Ico.mp hj).1, hjm.le, h⟩
      · intro h; exact h.2.2
    rw [Finset.prod_subtype _ hiff]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [hsum j hjm.le y.1 y.2]
    show _ = z (j + 1) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
      gaussDens (c j) (z (j + 1) • ψ ⟨j + 1, y.1⟩ - (((S.L ^ S.d : ℕ)) : ℝ)⁻¹ • _)
    rw [finrank_euclideanSpace_fin, Nat.cast_pow, hψ (j + 1) y.1 (by omega)]
  · have hiff : ∀ y : BlockAt S n M K (m' + 1), y ∈ (Finset.univ.filter fun y : BlockAt S n M K (m' + 1) =>
        ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m') ↔
        nd ⟨m' + 1, y⟩ := by
      intro y
      rw [hnd]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨hk1, le_rfl, h⟩
      · intro h; exact h.2.2
    rw [Finset.prod_subtype _ hiff]
    refine Finset.prod_congr rfl fun y _ => ?_
    rw [hsum m' le_rfl y.1 y.2]
    show _ = z (m' + 1) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) *
      gaussDens (c m') (z (m' + 1) • ψ ⟨m' + 1, y.1⟩ - (((S.L ^ S.d : ℕ)) : ℝ)⁻¹ • _)
    rw [finrank_euclideanSpace_fin, Nat.cast_pow, hψt y.1]

end Nodes

end Balaban.LargeField
