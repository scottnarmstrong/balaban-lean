/-
Ported from `scottnarmstrong/BKARForestFormula` at commit `a07f44a` on 2026-10-11
(Lean v4.33.0 / Mathlib v4.33.0 to v4.35.0-rc2 and the module system).
Original author: Scott Armstrong. Original license: Apache License 2.0
(see the LICENSE file of that repository).
-/
module

public import Balaban.External.BKAR.CubePartition.Support
public import Balaban.External.BKAR.CubePartition.Prefixed
public import Balaban.External.BKAR.CubePartition.CubeIntegral
public import Balaban.External.BKAR.CubePartition.MeasurePartition
public import Balaban.External.BKAR.CubePartition.MeasureSmoothness
public import Balaban.External.BKAR.CubePartition.SimplexSector
public import Balaban.External.BKAR.CubePartition.SimplexSector.Finite

/-! # Cube partition layer (facade)

Re-exports the conversion from the recursion's nested ordered-simplex
integrals to genuine set integrals over the unit cube `[0,1]^{E(F)}`: the
ordered sectors and their almost-everywhere disjoint partition of the cube,
the simplex-sector conversion, and the regrouping of contributions by
support.
-/
