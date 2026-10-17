/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainNodes
public import Balaban.LargeField.R.RRemovedChainForestMain

/-!
# The unrolled Gaussian product as a product over the nodes, and its integral (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (a), (b), (d).  `gauss_prod_eq_nodes`: the product of
the Gaussian factors of `gaussProd_unroll_eq` is the product over the nodes of the Gaussian factors of the
forest.  `lintegral_gauss_unrolled`: integrating the free nodes (the nodes outside `Fx`, the others being
fixed roots with prescribed values) in the unrolled Gaussian product gives at most the product of the
suprema `(c_{s-1} z_s² / 2π)^{N/2}` of the densities of the fixed roots, for any values of the leaves.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section GaussInt

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **The unrolled Gaussian product is the product over the nodes** (the node values `ψ`, the leaf values
read from `fld`; `ψ` equals `fld` at the scales `≤ m'` and `ft` at the scale `m' + 1`). -/
theorem gauss_prod_eq_nodes {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (Z : H.Comp (m' + 1))
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    [Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
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
    ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
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
      ∏ i : {b : Σ s, BlockAt S n M K s // nd b}, z i.1.1 ^ Module.finrank ℝ
          (EuclideanSpace ℝ (Fin N)) *
        gaussDens (c (i.1.1 - 1)) (z i.1.1 • ψ i.1 - ((S.L ^ S.d : ℕ) : ℝ)⁻¹ •
          ((∑ j ∈ Finset.univ.filter (fun j : {b : Σ s, BlockAt S n M K s // nd b} =>
              pa j ≠ j ∧ pa j = i), ψ j.1) +
            ∑ l ∈ Finset.univ.filter (fun l : {q : (Σ s, BlockAt S n M K s) ×
                {b : Σ s, BlockAt S n M K s // nd b} //
              (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
                Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = i),
              fld l.1.1.1 l.1.1.2)) := by
  classical
  have hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ m' + 1 := by
    rintro ⟨s, y⟩ h
    cases s with
    | zero => exact absurd h (hnd0 y)
    | succ j =>
      obtain ⟨h1, h2, -⟩ := (hnd j y).mp h
      exact ⟨by show k1 + 1 ≤ j + 1; omega, by show j + 1 ≤ m' + 1; omega⟩
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

open Classical in
/-- **The hypotheses of the forest integral for the Gaussian nodes**: the parent map, the scales, the
number of children and the range of the scales. -/
theorem gauss_forest_data {k1 m' : ℕ} (Z : H.Comp (m' + 1))
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    (hnd0 : ∀ y : BlockAt S n M K 0, ¬ nd ⟨0, y⟩) (hm : m' + 1 ≤ K)
    [Fintype {b : Σ s, BlockAt S n M K s // nd b}]
    [Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b)) :
    (∀ i : {b : Σ s, BlockAt S n M K s // nd b}, pa i ≠ i → (pa i).1.1 = i.1.1 + 1) ∧
    (∀ i : {b : Σ s, BlockAt S n M K s // nd b}, k1 + 1 ≤ i.1.1) ∧
    (∀ i : {b : Σ s, BlockAt S n M K s // nd b}, i.1.1 ≤ m' + 1) ∧
    (∀ i : {b : Σ s, BlockAt S n M K s // nd b},
      (Finset.univ.filter fun c => pa c ≠ c ∧ pa c = i).card +
      (Finset.univ.filter fun l : {q : (Σ s, BlockAt S n M K s) ×
          {b : Σ s, BlockAt S n M K s // nd b} //
        (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
          Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1} => l.1.2 = i).card = S.L ^ S.d) := by
  have hrange : ∀ b, nd b → k1 + 1 ≤ b.1 ∧ b.1 ≤ m' + 1 := by
    rintro ⟨s, y⟩ h
    cases s with
    | zero => exact absurd h (hnd0 y)
    | succ j =>
      obtain ⟨h1, h2, -⟩ := (hnd j y).mp h
      exact ⟨by show k1 + 1 ≤ j + 1; omega, by show j + 1 ≤ m' + 1; omega⟩
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
  subst hpaeq
  exact ⟨fun i hi => (g1 i hi).symm, g2, fun i => (hrange i.1 i.2).2, g3⟩


end GaussInt

end Balaban.LargeField
