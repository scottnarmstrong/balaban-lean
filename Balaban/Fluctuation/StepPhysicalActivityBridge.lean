/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceSliceScaled

/-!
# The complex activity record from the physical one

A real activity record for the step (as produced by the physical direct terms) gives the complex
activity record with the same block scale, rate and constants, through the transport
`stepActivityBoundC_of_activityBound`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ}
  {C : StepClass d L N₁ m₁ k N ϱ}
  {g : Fld d L N₁ m₁ (k + 1) N} {pp a εH Kc : ℝ}

/-- A real activity record with rate `a`, size `εH` and constant `Kc` gives a complex activity
record with the same three values, at a step with ray data beyond `p₁`. -/
theorem complexActivity_of_physical
    (R : S.RayData pp) (hp : 0 < S.p₁) (hlt : S.p₁ < pp)
    (hreal : ∃ I : StepActivityBound S C g,
      I.κH = a ∧ I.εH = εH ∧ I.Kc = Kc) :
    ∃ B : StepActivityBoundC S C g,
      B.κH = a ∧ B.εH = εH ∧ B.Kc = Kc := by
  rcases hreal with ⟨I, hκ, hε, hK⟩
  obtain ⟨B, hκB, hεB, hKB, -, -, -⟩ :=
    stepActivityBoundC_of_activityBound R hp hlt I
  exact ⟨B, hκB.trans hκ, hεB.trans hε, hKB.trans hK⟩

end Balaban.Fluctuation
