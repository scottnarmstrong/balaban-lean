/-
Ported from `scottnarmstrong/BKARForestFormula` at commit `a07f44a` on 2026-10-11
(Lean v4.33.0 / Mathlib v4.33.0 to v4.35.0-rc2 and the module system).
Original author: Scott Armstrong. Original license: Apache License 2.0
(see the LICENSE file of that repository).
-/
module

public import Balaban.External.BKAR.CubePartition.Support.Terminal

/-! # Support-indexed contributions (facade)

Re-exports the support layer of the cube partition: growth-order
bookkeeping, contributions grouped by support and order, and their
vanishing and base cases.
-/
