/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.QuietSymm
public import Balaban.LargeField.Base.BaseGaussCut

/-!
# The ultralocal Gaussian of the first-step fluctuation variables

LFR Definition II.7.6 (kernel): the fluctuation variables `ψ'_0(y) ∈ ℝ^N` of the sites of
`(Ω ∖ Ω'') ∩ Z'` carry the ultralocal Gaussian `(2π)^{-N/2} e^{-½ ‖ψ'_0‖²}` of P5 (2.47), one factor per
block.  `baseFluctGauss` is the product over these blocks; it is nonnegative, Borel in the new
variables and `O(N)`-invariant.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Gauss

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  (a : LocalHistory S n M K)

/-- The `0`-blocks carrying the fluctuation variable `ψ'_0`: those of `(Ω ∖ Ω'') ∩ Z'`. -/
def baseFluctBlocks : Set (BlockAt S n M K 0) :=
  {y | BlockSub (S := S) (n := n) (M := M) (K := K) 0 y (varSet a 0 .fluct)}

theorem siteDensity_rot (N : ℕ) (ρ : OrthN N) (v : EuclideanSpace ℝ (Fin N)) :
    siteDensity N (ρ v) = siteDensity N v := by
  unfold siteDensity
  rw [LinearIsometryEquiv.norm_map]

open Classical in
/-- **The ultralocal Gaussian of the fluctuation variables** `∏_{y} (2π)^{-N/2} e^{-½ ‖ψ'_0(y)‖²}`. -/
noncomputable def baseFluctGauss (N : ℕ) (x : NewCfg N a 0) : ℝ :=
  ∏ y : baseFluctBlocks a, siteDensity N (subFluctVarField N x 0 y.1)

theorem baseFluctGauss_nonneg (x : NewCfg N a 0) : 0 ≤ baseFluctGauss a N x :=
  Finset.prod_nonneg fun _ _ => siteDensity_nonneg N _

theorem measurable_baseFluctGauss : Measurable (baseFluctGauss a N) := by
  classical
  unfold baseFluctGauss
  refine Finset.measurable_fun_prod _ fun y _ => ?_
  exact (measurable_siteDensity N).comp (measurable_subFluctVarField 0 y.1)

theorem baseFluctGauss_rot (ρ : OrthN N) (x : NewCfg N a 0) :
    baseFluctGauss a N (rotSub ρ x) = baseFluctGauss a N x := by
  unfold baseFluctGauss
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [subFluctVarField_rot, siteDensity_rot]

end Gauss

end Balaban.LargeField
