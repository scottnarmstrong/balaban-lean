/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainRead
public import Balaban.LargeField.R.RRemovedWindowAncCore
public import Balaban.LargeField.R.RRemovedChainGraded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian blocks of the ancestors at one scale (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (a), (b).  The Gaussian blocks of the step
`j → j + 1` of different ancestors `c ≠ c'` of `Z` of the same scale are different
(`gaussBlocks_disjoint`), so a product over the ancestors and their Gaussian blocks is the product over
the set of Gaussian blocks of all ancestors of that scale (`prod_gauss_level`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Level

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

/-- The Gaussian blocks of the step `j → j + 1` of two different components of scale `j + 1` are
disjoint. -/
theorem gaussBlocks_disjoint {j : ℕ} (hK : j + 1 ≤ K) {c c' : H.Comp (j + 1)} (hne : c ≠ c')
    {y : BlockAt S n M K (j + 1)} (hy : y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j)
    (hy' : y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j) : False := by
  have h1 := ((gaussBlocks_iff hK c y).mp hy).1
  have h2 := ((gaussBlocks_iff hK c' y).mp hy').1
  exact hne (Subtype.ext (comp_eq_of_mem c.2 c'.2 h1 h2))

/-- The sum, as a product, over the ancestors at scale `k₁` of `Z` is the iterated product over the
ancestors at scale `k₁ + 1` and their old parts. -/
theorem prod_anc_eq_prod_parts {β : Type*} [CommMonoid β] {k1 m : ℕ} (h : k1 < m) (Z : H.Comp m)
    (f : H.Comp k1 → β) :
    ∏ C ∈ H.ancFin k1 m Z, f C = ∏ P ∈ H.ancFin (k1 + 1) m Z, ∏ C ∈ H.parts k1 P, f C := by
  classical
  rw [ancFin_eq_biUnion_parts h Z, Finset.prod_biUnion (fun P _ P' _ hne => parts_disjoint hne)]

open Classical in
/-- **The product over the Gaussian blocks of the ancestors of one scale.**  For `j + 1 < m`, the
iterated product over the ancestors `P` of `Z` of scale `j + 2`, their old parts `c` and the Gaussian
blocks `y` of `c`, of a function `Φ` of the block, is the product over the Gaussian blocks of all the
ancestors of scale `j + 1`. -/
theorem prod_gauss_level {β : Type*} [CommMonoid β] {j m : ℕ} (hj : j + 1 < m) (hK : j + 1 ≤ K)
    (Z : H.Comp m) (Φ : BlockAt S n M K (j + 1) → β) :
    ∏ P : ↥(H.ancFin (j + 1 + 1) m Z), ∏ c : ↥(H.parts (j + 1) P.1),
        ∏ y : ↥(gaussBlocks (H.localHistory M K (j + 1) c.1) j), Φ y.1 =
      ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
        ∃ c ∈ H.ancFin (j + 1) m Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j), Φ y := by
  have h1 : ∏ P : ↥(H.ancFin (j + 1 + 1) m Z), ∏ c : ↥(H.parts (j + 1) P.1),
        ∏ y : ↥(gaussBlocks (H.localHistory M K (j + 1) c.1) j), Φ y.1 =
      ∏ P ∈ H.ancFin (j + 1 + 1) m Z, ∏ c ∈ H.parts (j + 1) P,
        ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
          y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j), Φ y := by
    rw [← Finset.prod_coe_sort (H.ancFin (j + 1 + 1) m Z)]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [← Finset.prod_coe_sort (H.parts (j + 1) P.1)]
    refine Finset.prod_congr rfl fun c _ => ?_
    exact (Finset.prod_subtype (Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
      y ∈ gaussBlocks (H.localHistory M K (j + 1) c.1) j)) (by simp) Φ).symm
  rw [h1]
  have h2 := prod_anc_eq_prod_parts (f := fun c => ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
    y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j), Φ y) hj Z
  rw [← h2]
  rw [← Finset.prod_biUnion]
  · congr 1
    ext y
    simp [Finset.mem_biUnion]
  · intro c _ c' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    exact gaussBlocks_disjoint hK hne (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hy').2

open Classical in
/-- The product over the Gaussian blocks of the top component as the product over the Gaussian blocks
of its ancestors of the same scale (which is `Z` itself). -/
theorem prod_gauss_top {β : Type*} [CommMonoid β] {m' : ℕ} (Z : H.Comp (m' + 1))
    (Φ : BlockAt S n M K (m' + 1) → β) :
    ∏ y : ↥(gaussBlocks (H.localHistory M K (m' + 1) Z) m'), Φ y.1 =
      ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
        ∃ c ∈ H.ancFin (m' + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (m' + 1) c) m'), Φ y := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
    y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m')) (by simp) Φ]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext y
  simp [ancFin_self]

end Level

end Balaban.LargeField
