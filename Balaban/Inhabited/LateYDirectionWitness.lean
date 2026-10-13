/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ChiYWitness
public import Balaban.LargeField.History.LateYDirection

/-!
# The tested/outer partition on the landed instance `ctxY` (`LateYDirectionWitness`)

On `ctxY` (scale `k = 1`, `Y` the whole torus) the set of tested sites is non-empty and the set of
outer sites is empty, so the instance does not exercise the outer part of the partition.
It is not a late scale either: the cube mass of `ctxY` at `k = 1` is `0` (below the switch), so
the mass identification `cs.mu k = sfBgMassAt L k ν` of `parentPsi_direction_of_chiY_ne_zero` is
impossible for every `ν > 0` there (`ctxY_mass_identification_fails`).  A witness for the
direction bound needs a late scale (`k > k₀`) with non-empty `Y`; none is landed.  A witness with
`outerSites ≠ ∅` needs in addition `Y ≠ ∅` whose neighbourhood `nbhd 1 Y` is not the whole torus,
and a retained shell with a data site over a cube outside `nbhd 1 Y`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7.Wit
  Balaban.SmallField.Def6v2

theorem testedSites_ctxY_nonempty :
    ∃ s, s ∈ testedSites ctxY (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1))) :=
  exists_tested_site ctxY _ (Set.mem_univ _)

theorem outerSites_ctxY_empty :
    outerSites ctxY (Set.univ : Set (Torus wS.d (sides wS.L 1 nMulti 1))) = ∅ :=
  outerSites_univ ctxY

/-- The cube mass of `ctxY` at `k = 1` is `0`; it is never `sfBgMassAt L 1 ν` with `ν > 0`. -/
theorem ctxY_mass_identification_fails {ν : ℝ} (hν : 0 < ν) :
    ctxY.cs.mu 1 ≠ sfBgMassAt wS.L 1 ν := by
  rw [ctxY_mu_one]
  unfold sfBgMassAt physMass
  have : (0 : ℝ) < wS.L := by
    have : wS.L = 3 := rfl
    rw [this]; norm_num
  positivity

end Balaban.LargeField.Def7
