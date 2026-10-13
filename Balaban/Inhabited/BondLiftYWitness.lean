/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.ParentDomain
public import Balaban.LargeField.History.BondLiftY

public import Balaban.LargeField.History.BondLiftY
public import Balaban.Inhabited.SFCtxMulti

/-!
# Non-vacuity of the classification of `BondLiftY` on `ctxMulti`

The interface pair over a cube of `Y` on the landed multi-cube context (`d = L = 3`, `N = 2`,
`k = 1`).  The hypothesis `chiY ≠ 0` is not part of this statement.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7
  Balaban.LargeField.Def7.Wit

/-- The classification pair on the landed multi-cube context `ctxMulti` (`d = L = 3`, `N = 2`, `k = 1`).  The hypothesis `chiY ≠ 0` is not part of this statement. -/
theorem multi_pair_over_Y_instance :
    ∃ (Y : Set (Torus wS.d (sides wS.L 1 nMulti 1))) (y₁ : Torus wS.d (sides wS.L 1 nMulti 1))
      (s s' : BgT ctxMulti.geo 1),
      y₁ ∈ Y ∧
      blockMap (wS.L ^ 1 * (ctxMulti.geo.c * ctxMulti.geo.M1)) (sides wS.L 1 nMulti 1) s = y₁ ∧
      s ≠ s' ∧ IsInterfacePair (ctxMulti.genW Y) s s' ∧
      (ctxMulti.genW Y).layerIndex s = 1 ∧ (ctxMulti.genW Y).layerIndex s' = 1 ∧
      s ∉ collar (ctxMulti.genW Y) ∧ s' ∉ collar (ctxMulti.genW Y) :=
  exists_pair_over_Y (j := 0) ctxMulti (by norm_num [wS, setting, typing, typing0])


end Balaban.LargeField
