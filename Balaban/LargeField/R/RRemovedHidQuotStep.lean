/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidQuotAct
public import Balaban.LargeField.R.WindowGenCompose

/-!
# The step objects of a quiet step in the form of the composed objects (W936)

`notes/phase1/LF4R-PLAN.md` §8.5.  For one quiet step `k → k + 1`:

* `mainActionLoc_eq_multiAction`: the main action is `multiAction` (`WindowGenCompose.lean`) of the history
  generating set `histGenLevel` at the region `Xfine`, the multiscale field `psiLevel` and the real
  background `locPhi`;
* `gaussProd_eq_exp`: the Gaussian product is `∏ z^N (c/2π)^{N/2} · exp (-∑_y (c/2) ‖z ψ_{k+1}(y) - (Qψ_k)(y)‖²)`,
  the shape `const · e^{-𝒢}` of `constNat`, `gaussNat`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}
  (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ) (Zc : Finset (Torus S.d (n (k + 1))))
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅)

theorem mainActionLoc_eq_multiAction
    (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    mainActionLoc g Hl k Zc hZc hk cs hrem o x hv =
      multiAction (histGenLevel g Hl k hk hrem) cs.aw (cs.beta (k + 1)) (cs.muAct (k + 1)) hv
        (Xfine g Hl k Zc)
        (psiLevel g Hl k hk (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
          (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o))
        (locPhi g Hl k Zc hZc hk cs o x hv) := rfl

open Classical in
theorem gaussProd_eq_exp (a : LocalHistory S n M K) (k : ℕ) (cs : OpConsts)
    {V : Set (BlockAt S n M K (k + 1))} (o : OutConfig N V) (x : NewCfg N a k) :
    gaussProd N a k cs o x =
      (∏ _y : gaussBlocks a k, cs.z (k + 1) ^ N *
          (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2)) *
        Real.exp (-∑ y : gaussBlocks a k,
          (cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) / 2 *
            ‖cs.z (k + 1) • outField N o y - qCoarseK N x y‖ ^ 2) := by
  unfold gaussProd gaussT
  simp only [← mul_assoc]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  simp only [neg_mul]
  congr!

end Step

end Balaban.LargeField
