/-
Ported from `scottnarmstrong/BKARForestFormula` at commit `a07f44a` on 2026-10-11
(Lean v4.33.0 / Mathlib v4.33.0 to v4.35.0-rc2 and the module system).
Original author: Scott Armstrong. Original license: Apache License 2.0
(see the LICENSE file of that repository).
-/
module

public import Balaban.External.BKAR.CubePartition.SimplexSector.Pair

/-! # Simplex-sector conversion (facade)

Re-exports the simplex-sector conversion: the identification of the
recursion's nested ordered-simplex integrals with set integrals over the
closed ordered cube sectors, built up through the singleton case, the
ordered coordinate equivalences, and the two-edge case.
-/
