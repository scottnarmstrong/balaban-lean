/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafMap
public import Balaban.LargeField.R.RRemovedHidLeafSite
public import Balaban.LargeField.R.DeltaPsiEdge

/-!
# The parent chain of the blocks of a site (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `chain_inv`: along the parent map `pa` of the forest of the nodes, the iterates of
a node whose block is the `i₀`-block of a site `x` are the `i`-blocks of `x`, `i ≥ i₀` (the parent of a block is
its coarsening, `jBlock_succ_eq_blockMap`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Chain

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {m' : ℕ}

theorem chain_inv (hmK : m' + 1 ≤ K) (nd : (Σ s, BlockAt S n M K s) → Prop)
    (pa : {b : Σ s, BlockAt S n M K s // nd b} → {b : Σ s, BlockAt S n M K s // nd b})
    (hpa : ∀ b : {b : Σ s, BlockAt S n M K s // nd b},
      (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧ b.1.1 + 1 ≤ m' + 1 →
        (pa b).1 = ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩) ∧
      (¬ (nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1) → pa b = b))
    (x : Torus S.d (M * n K * S.L ^ K)) (b0 : {b : Σ s, BlockAt S n M K s // nd b}) (i0 : ℕ)
    (h0 : b0.1 = ⟨i0, jBlock S.d S.L (M * n K) K i0 x⟩) (t : ℕ) :
    ∃ i, i0 ≤ i ∧ (pa^[t] b0).1 = ⟨i, jBlock S.d S.L (M * n K) K i x⟩ := by
  induction t with
  | zero => exact ⟨i0, le_rfl, h0⟩
  | succ t ih =>
    obtain ⟨i, hi, hb⟩ := ih
    rw [Function.iterate_succ_apply']
    set b := pa^[t] b0 with hbdef
    obtain ⟨hp1, hp2⟩ := hpa b
    by_cases hprem : nd ⟨b.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (b.1.1 + 1))) b.1.2⟩ ∧
        b.1.1 + 1 ≤ m' + 1
    · have h1 := hp1 hprem
      rw [hb] at h1 hprem
      refine ⟨i + 1, by omega, ?_⟩
      rw [h1]
      have hi1 : i + 1 ≤ m' + 1 := hprem.2
      have hj : i + 1 ≤ K := by omega
      have := jBlock_succ_eq_blockMap (d := S.d) (L := S.L) (N₀ := M * n K) (k := K) hj x
      simp only [this]
    · rw [hp2 hprem]
      exact ⟨i, hi, hb⟩

end Chain

end Balaban.LargeField
