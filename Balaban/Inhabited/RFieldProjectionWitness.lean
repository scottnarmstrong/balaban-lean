/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RFieldProjection
public import Balaban.LargeField.Def7v2InhabitedFam

/-!
# Consistency of `RFieldProjection` on the landed witnesses

`IsRepPre2` is inhabited (`Wit.nonempty_isRepPre2`, `Wit.wIsRepPre2`), and so is `IsRep2`
(`Wit.wIsRep2`); the two witnesses are over families with the same small-field data.  The
assembly `isRep2_of_isRepPre2_of_fields` applied to the pre witness with the seven changed fields
taken from the post witness returns a post record (`wAssembled`).  This is a consistency check
that the seven hypotheses are jointly satisfiable, not a construction of `R`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2.Wit

open MeasureTheory Balaban RegionHistory Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.Background Balaban.LargeField.Def7
  Balaban.LargeField.Def7.Wit Filter Topology

theorem wFam2_sf_eq (ν : ℝ) (k0 : ℕ) : (wFam2 ν k0 (1 + 1)).sf = (wFam2 ν k0 1).sf := rfl

/-- The assembly applied to the landed pre and post witnesses. -/
theorem wAssembled (ν : ℝ) (hν0 : 0 < ν) (hν : wβ * ν * 27 ≤ 1) (rH : ℝ) :
    IsRep2 wS wR (kZero wS.d wS.L wβ ν) 1 27 2 wGeoF (wCs ν (kZero wS.d wS.L wβ ν))
      (budgetConsts wβ) wP6 wC7 wβ ν whv rH 1 wM6 le_rfl
      (wFam2 ν (kZero wS.d wS.L wβ ν) (1 + 1)) (wRho2 ν (kZero wS.d wS.L wβ ν) (1 + 1))
      (wSt ν) wVc :=
  isRep2_of_isRepPre2_of_fields (wIsRepPre2 ν hν0 hν rH) (wFam2_sf_eq ν _)
    (wIsRep2 ν hν0 hν rH).complete (wIsRep2 ν hν0 hν rH).form (wIsRep2 ν hν0 hν rH).sfData
    (wIsRep2 ν hν0 hν rH).pin (wIsRep2 ν hν0 hν rH).opBound (wIsRep2 ν hν0 hν rH).budget
    (wIsRep2 ν hν0 hν rH).bdry

end Balaban.LargeField.Def7v2.Wit
