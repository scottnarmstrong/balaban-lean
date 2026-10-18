/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LateScaleWitness
public import Balaban.LargeField.History.LateParentR3

/-!
# An instance of the direction bound of `LateParentR3` (ruling R2)

In the context `ctxLate` of `LateScaleWitness` (positive cube mass `sfBgMassAt L 1 (1/9)`,
`χ_1(Y) = 1` at the constant unit field, with the extended direction stencil), the hypotheses of
`parentPsi_dir_of_chiY_ne_zero` hold together at a data site.  The conclusion is degenerate (the
datum equals `h`); the point is that the hypotheses are jointly satisfiable.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7.Wit
  Balaban.SmallField.Def6v2

/-- **The direction bound at every data site has a landed instance**: in `ctxLate`, with `Y` the
whole torus and the constant unit field, there is a data site of `𝔹_1(W₂(Y))`, and at every data
site `‖Ψ(s) - h‖ < δ_1 / √ν_1`. -/
theorem lateDirAllSites_instance :
    ∃ s, s ∈ dataSites (ctxLate.genW (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1)))) ∧
      ∀ s ∈ dataSites (ctxLate.genW (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1)))),
        rn (fun i => parentPsi ctxLate (fun _ => whv) s i - whv i) <
          ctxLate.cs.delta 1 / Real.sqrt lateNu := by
  have hne : ctxLate.chiY Set.univ (fun _ => whv) whv ≠ 0 := by
    rw [chiY_ctxLate]; exact one_ne_zero
  obtain ⟨s, hs⟩ := exists_tested_site ctxLate _ (Set.mem_univ _)
  exact ⟨s, hs.1, fun t ht => parentPsi_dir_of_chiY_ne_zero ctxLate (by decide) _ _ whv hne
    lateNu_pos ctxLate_mu ht⟩

end Balaban.LargeField.Def7
