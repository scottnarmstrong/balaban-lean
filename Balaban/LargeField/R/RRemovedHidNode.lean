/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainRead
public import Balaban.LargeField.R.RRemovedWindowAncCore

/-!
# The node variables of the window are internal variables of the top component (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (2).  An output block `y` of an ancestor `c` of
scale `j + 1 ≤ m'` of `Z` (scale `m' + 1`) is the large-field variable `ψ_{j+1}(y)` of the successor of `c`
and hence an internal variable of `Z` (`node_var`); read from a configuration of the variables of `Z`, the
field `ψ_{j+1}(y)` is the value of that variable (`subVarField_node`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory

section Node

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **A node is an internal variable of the top component**: an output block `y` of an ancestor `c` of
scale `j + 1 ≤ m'` of `Z` (scale `m' + 1`, quiet window) is the large-field variable `ψ_{j+1}(y)` of `Z`. -/
theorem node_var {k1 m' j : ℕ} (hk1 : k1 ≤ j) (hjm : j + 1 ≤ m') (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {y : BlockAt S n M K (j + 1)}
    (hzb : ZBlk (H.localHistory M K (j + 1) c) (j + 1) y) :
    ∃ hb : BlockSub (S := S) (n := n) (M := M) (K := K) (j + 1) y
      (varSet (H.localHistory M K (m' + 1) Z) (j + 1) .large),
      mkVar (H.localHistory M K (m' + 1) Z) (m' + 1) (j + 1) .large y (by omega) hb ∈
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A := by
  classical
  have hlt : j + 1 < m' + 1 := by omega
  rw [ancFin_eq_biUnion_parts (by omega : j + 1 < m' + 1) Z] at hc
  obtain ⟨P, hP, hcP⟩ := Finset.mem_biUnion.mp hc
  have hdP := mem_ancFin.mp hP
  have hK : j + 1 + 1 ≤ K := hdP.le.trans hm
  have hb := outBlock_large hK P hcP y hzb
  have hA : mkVar (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1) (j + 1) .large y (by omega) hb ∈
      (locOp geo cs SD KD hH lab (j + 1 + 1) hK P).A :=
    newVars_sub_locOp_A geo cs SD KD hK (fun hk => hq _ (by omega) P hdP hk) rfl
  have hbZ := inclVar_mem hm hdP (mkVar (H.localHistory M K (j + 1 + 1) P) (j + 1 + 1) (j + 1)
    .large y (by omega) hb)
  exact ⟨hbZ, locOp_A_incl geo cs SD KD hm hdP (fun t ht Y' h' => hq t (by omega) Y' h') _ hA⟩

end Node

end Balaban.LargeField
