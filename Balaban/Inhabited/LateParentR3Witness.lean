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
`parentPsi_dir_of_chiY_ne_zero` hold together at a data site, and those of the late parent-domain
theorem `inPsiTilde_genW_of_late_chiY_local` hold on the history without large-field cubes.  The
conclusions are degenerate (the datum equals `h`); the point is that the hypotheses are jointly
satisfiable at a positive cube mass.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7.Wit
  RegionHistory Balaban.SmallField.Def6v2 Balaban.SmallField

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

/-- **A genuine instance of `LateParentR3`** (`inPsiTilde_genW_of_late_chiY_local`) at the constant
unit field in `ctxLate` (positive cube mass), on the region history without large-field cubes
(`Y` the whole torus, no retained component, so the activity hypothesis is vacuous): the datum lies
in the real domain of the complete background with the radius `max (3 d L δ_0, 4 (d+1) δ_1)`. -/
theorem lateParentDomain_instance :
    InPsiTilde (ctxLate.genW ((emptyHist.step (0 + 1)).Z)ᶜ) (sfBgMassAt wS.L (0 + 1) lateNu)
      (max (3 * wS.d * wS.L * ctxLate.cs.delta 0) (4 * (wS.d + 1) * ctxLate.cs.delta (0 + 1)))
      (parentPsi ctxLate (fun _ => whv)) (fun i => whv i) := by
  refine inPsiTilde_genW_of_late_chiY_local emptyHist ctxLate (fun _ => whv) whv (by decide)
    lateNu_pos whv_norm csY_delta_one_pos csY_delta_one_le ctxLate_mu
    (by rw [chiY_ctxLate]; exact one_ne_zero) hbLate ?_
  intro C hC ⟨t, ht, hq⟩
  exfalso
  have h := comp_subset C.2 hq
  rw [mem_finOf] at h
  exact (emptyFlow_Zpre 1 ▸ h : _)

end Balaban.LargeField.Def7
