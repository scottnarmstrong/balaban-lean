/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.StepData

/-!
# The reference measures do not depend on the solver mass (REGIONAL §3, §6 item 8)

`refMeasure`, `subMeasure`, `outMeasure` take only the localized history, `N`, the level and the
variable set.  `StepData.ker k a` and the sub-measure `subMeasure N a (k+1) (newPrimeVars a k)`
used in `GaussStepSpec` take no solver mass, `h` or background either.  So the comparison of the
complete-background and field-free descriptions of the step is definitional (cost zero); this is
all that REGIONAL's `massChange_measure_compare` states.  Nothing here concerns the open
`massChange_cutoff_reference_glue`.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

/-- **REGIONAL §3 / item 8** (reference measure).  Whatever the dependence of a description of the
step on a solver mass `m` and a background `B`, if its measure on the internal variables is the
landed `refMeasure N a q`, the measures of two descriptions (any two masses and backgrounds)
coincide, and each is `Measure.pi (varMeasure N ∘ isSpin)`. -/
theorem massChange_measure_compare {Mass Bg : Type*} (N : ℕ) (a : LocalHistory S n M K) (q : ℕ)
    (m₁ m₂ : Mass) (B₁ B₂ : Bg) :
    (fun (_ : Mass) (_ : Bg) => refMeasure N a q) m₁ B₁ =
        (fun (_ : Mass) (_ : Bg) => refMeasure N a q) m₂ B₂ ∧
      refMeasure N a q = Measure.pi fun p => varMeasure N p.isSpin :=
  ⟨rfl, rfl⟩

/-- The sub-measure used by the step (`StepData`, `GaussStepSpec`) at the new primed variables is
`Measure.pi (varMeasure N ∘ isSpin)`; it has no mass or background argument. -/
theorem massChange_subMeasure_compare (N : ℕ) (a : LocalHistory S n M K) (k : ℕ) :
    subMeasure N a (k + 1) (newPrimeVars a k) =
      Measure.pi fun p => varMeasure N p.1.isSpin :=
  rfl

/-- The output measure is Lebesgue measure on the output variables, with no mass argument. -/
theorem massChange_outMeasure_compare (N : ℕ) {α : Type} (V : Set α) [Finite V] :
    haveI := Fintype.ofFinite V
    outMeasure N V = Measure.pi fun _ => volume :=
  rfl

end

end Balaban.LargeField
