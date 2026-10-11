/-
Ported from `scottnarmstrong/BKARForestFormula` at commit `a07f44a` on 2026-10-11
(Lean v4.33.0 / Mathlib v4.33.0 to v4.35.0-rc2 and the module system).
Original author: Scott Armstrong. Original license: Apache License 2.0
(see the LICENSE file of that repository).
-/
module

public import Balaban.External.BKAR.OrderedAssembly.AllBranchesFiberBridge.LowRank

/-! # Fiber bridge (facade)

Re-exports the identification of the recursion's boundary support/order
fibers with intrinsic ordered contributions: the order-following growth,
the core bridge identities, and the low-rank (empty, singleton, pair)
cases together with the order sums.
-/
