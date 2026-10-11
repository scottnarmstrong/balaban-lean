/-
Ported from `scottnarmstrong/BKARForestFormula` at commit `a07f44a` on 2026-10-11
(Lean v4.33.0 / Mathlib v4.33.0 to v4.35.0-rc2 and the module system).
Original author: Scott Armstrong. Original license: Apache License 2.0
(see the LICENSE file of that repository).
-/
module

public import Balaban.External.BKAR.CubePartition
public import Balaban.External.BKAR.CubePartition.Branches
public import Balaban.External.BKAR.CubePartition.CubeIntegral
public import Balaban.External.BKAR.CubePartition.MeasurePartition
public import Balaban.External.BKAR.CubePartition.MeasureSmoothness
public import Balaban.External.BKAR.CubePartition.Orders
public import Balaban.External.BKAR.CubePartition.Prefixed
public import Balaban.External.BKAR.CubePartition.SimplexSector
public import Balaban.External.BKAR.CubePartition.SimplexSector.Equiv
public import Balaban.External.BKAR.CubePartition.SimplexSector.Finite
public import Balaban.External.BKAR.CubePartition.SimplexSector.Pair
public import Balaban.External.BKAR.CubePartition.SimplexSector.Singleton
public import Balaban.External.BKAR.CubePartition.Smoothness
public import Balaban.External.BKAR.CubePartition.Support
public import Balaban.External.BKAR.CubePartition.Support.Contribution
public import Balaban.External.BKAR.CubePartition.Support.Growth
public import Balaban.External.BKAR.CubePartition.Support.Terminal
public import Balaban.External.BKAR.Differential
public import Balaban.External.BKAR.Forest
public import Balaban.External.BKAR.ForestGraph
public import Balaban.External.BKAR.Formula
public import Balaban.External.BKAR.Interpolation
public import Balaban.External.BKAR.OrderedAssembly
public import Balaban.External.BKAR.OrderedAssembly.AllBranches
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberBridge
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberBridge.Core
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberBridge.FollowOrder
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberBridge.LowRank
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFibers
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberSmoothness
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesRegrouping
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesSmoothness
public import Balaban.External.BKAR.OrderedAssembly.AllBranchesTelescoping
public import Balaban.External.BKAR.OrderedAssembly.CanonicalForestBridge
public import Balaban.External.BKAR.OrderedAssembly.CanonicalSector
public import Balaban.External.BKAR.OrderedAssembly.ChosenGrowth
public import Balaban.External.BKAR.OrderedAssembly.CubeFold
public import Balaban.External.BKAR.OrderedAssembly.ForestIndexCube
public import Balaban.External.BKAR.OrderedAssembly.LocalRecursion
public import Balaban.External.BKAR.OrderedBranch
public import Balaban.External.BKAR.OrderedExpansion
public import Balaban.External.BKAR.OrderedForest
public import Balaban.External.BKAR.OrderedTerminalGrowth
public import Balaban.External.BKAR.OrderedParams
public import Balaban.External.BKAR.OrderedRecursion
public import Balaban.External.BKAR.OrderedRemainder
public import Balaban.External.BKAR.OrderedSimplex
public import Balaban.External.BKAR.OrderedTerminal
public import Balaban.External.BKAR.PartialDeriv
public import Balaban.External.BKAR.PartialDerivSymmetry
public import Balaban.External.BKAR.Smoothness
public import Balaban.External.BKAR.Threshold
public import Balaban.External.BKAR.ThresholdComponents
public import Balaban.External.BKAR.ThresholdLayerCake

/-! # The Brydges–Kennedy–Abdesselam–Rivasseau forest interpolation formula

Root facade: importing this module brings in the whole development.

For a finite vertex set `V` and a function `ρ : (Edge V → ℝ) → ℝ` smooth
(`C^∞`) on the edge-coupling space (`BKARContDiff`), the BKAR forest
interpolation formula states

  `ρ(1,…,1) = ∑_{forests F} ∫_{[0,1]^{E(F)}} ∂_{E(F)} ρ (x^F(u)) du`,

summing over all acyclic edge subsets of the complete graph on `V` (the
empty forest contributing `ρ(0,…,0)`), where `∂_{E(F)}` is the mixed
partial derivative in the edge variables of `F` and `x^F(u)` is the
path-minimum interpolation: the coordinate of `x^F(u)` at an edge `{i, j}`
is the minimum of `u` along the unique forest path joining `i` to `j`, and
`0` when `i` and `j` lie in different components of `F`.

The flagship formal statement is
`BKAR.bkar_formula_forestIndex_cube_contributions` in `BKAR.Formula`, with
sector-form and empty-forest-split variants alongside, and a threshold /
layer-cake API for the interpolation points in the `BKAR.Threshold` files.

The formalization assumes `ρ` is `C^∞` (`BKARContDiff = ContDiff ℝ ⊤`)
where the classical statement needs only `C^{|V|-1}`; this is a deliberate
strengthening of the hypothesis.

## References

* D. Brydges, T. Kennedy, *Mayer expansions and the Hamilton–Jacobi
  equation*, J. Statist. Phys. 48 (1987) 19–49.
* A. Abdesselam, V. Rivasseau, *Trees, forests and jungles: a botanical
  garden for cluster expansions*, in Constructive Physics (Palaiseau 1994),
  Lecture Notes in Physics 446, Springer, 1995.  arXiv:hep-th/9409094.
-/
