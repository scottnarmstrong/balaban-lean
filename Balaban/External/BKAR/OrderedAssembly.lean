/-
Ported from `scottnarmstrong/BKARForestFormula` at commit `a07f44a` on 2026-10-11
(Lean v4.33.0 / Mathlib v4.33.0 to v4.35.0-rc2 and the module system).
Original author: Scott Armstrong. Original license: Apache License 2.0
(see the LICENSE file of that repository).
-/
module

public import Balaban.External.BKAR.OrderedAssembly.LocalRecursion
public import Balaban.External.BKAR.OrderedAssembly.AllBranches
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesRegrouping
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesTelescoping
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFibers
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberBridge
public import Balaban.External.BKAR.OrderedAssembly.CanonicalForestBridge
public import Balaban.External.BKAR.OrderedAssembly.ChosenGrowth
public import Balaban.External.BKAR.OrderedAssembly.CanonicalSector
public import Balaban.External.BKAR.OrderedAssembly.CubeFold
public import Balaban.External.BKAR.OrderedAssembly.ForestIndexCube
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesSmoothness

/-! # Ordered assembly layer (facade)

Re-exports the assembly of the ordered recursion into the final formula:
the all-branches expansion and its telescoping, regrouping by support and
order, the fiber analysis of the boundary tree sum, canonical forests
realizing each support, sectorwise canonicalization, and the fold into one
cube contribution per forest index.
-/
