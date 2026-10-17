/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedKernel
public import Balaban.LargeField.History.LocalHistory

/-!
# The output configuration `o'` of the window integral at a block (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4.  The configuration `o' = ψ_k` with `ψ_k↾Z₀` replaced by `w'`
in `mergeOut oz par`: at a block of `V` outside `Z₀` in `Z` it is `oz`, at a block of `Z₀` it is `w'`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section O

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))

theorem merge_apply_out (oz : OutZ N R a k) (par : OutPar N R a k) (w' : OutZero N R a k Z0)
    (y : BlockAt S n M K k) (hV : y ∈ Vblk R a k) (hn : y ∉ Z0) (hz : ZBlk a k y) :
    remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2) ⟨y, hV⟩ =
      oz ⟨y, hV, hz⟩ := by
  classical
  simp [remZeroMerge, remZeroSplit_apply, restrictOutPart, mergeOut, hn, hz]

theorem merge_apply_zero (oz : OutZ N R a k) (par : OutPar N R a k) (w' : OutZero N R a k Z0)
    (y : BlockAt S n M K k) (hV : y ∈ Vblk R a k) (hy : y ∈ Z0) :
    remZeroMerge a k Z0 (w', (remZeroSplit a k Z0 (mergeOut a k oz par)).2) ⟨y, hV⟩ =
      w' ⟨y, hV, hy⟩ := by
  classical
  simp [remZeroMerge, hy]

end O

end Balaban.LargeField
