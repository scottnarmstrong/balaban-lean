/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasOperator

/-!
# The reference probability measure in the operator gas

The operator form of P7 (3.26)–(3.28), printed pp. 527–528, uses the
product-space reference measure stated in (H-op) of
`notes/phase1/LF-RECONSTRUCTION.md` §III.10.3.  Its input is an explicitly
chosen probability measure `μ b` for each cube `b`; the measure on all
internal variables is their product.  This is the same product used by
`Polymer.gasOp_eq`.  In particular the definition does not identify the
infinite Lebesgue measures `Def7.gMeasure` with probability measures.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.LargeField

variable {B : Type*} [Fintype B] {Ω : B → Type*}
  [∀ b, MeasurableSpace (Ω b)]

/-- The cube-indexed reference probability measure of (H-op), P7 (3.26). -/
noncomputable def hOpMeasure (μ : ∀ b, Measure (Ω b)) : Measure (∀ b, Ω b) :=
  Measure.pi μ

/-- The reference measure of (H-op) unfolds to the product used in `gasOp_eq`. -/
theorem hOpMeasure_eq_pi (μ : ∀ b, Measure (Ω b)) : hOpMeasure μ = Measure.pi μ := rfl

/-- The product reference measure is a probability measure when every cube measure is. -/
instance hOpMeasure.isProbability (μ : ∀ b, Measure (Ω b))
    [∀ b, IsProbabilityMeasure (μ b)] : IsProbabilityMeasure (hOpMeasure μ) := by
  rw [hOpMeasure_eq_pi]
  infer_instance

end Balaban.LargeField
