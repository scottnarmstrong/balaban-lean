/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ParamCarrierLocal
public import Balaban.Fluctuation.HatLabelsDirect
public import Balaban.Fluctuation.PhysicalTerms
public import Balaban.Fluctuation.HatLabelsDep
public import Balaban.Fluctuation.HatDiagContBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Physical label activities with the datum free

The landed route `physical_directTerms` → `labelAct_of_directTerms` freezes the block datum at one
point `Θ₀`.  The point `Θ₀` enters `DirectTerms` in exactly three fields: `mem` (`Θ₀ ∈ SΛ`),
`agΘ` (reflexivity of the source agreement at `Θ₀`) and `meas` (measurability of the diagonal terms
at `Θ₀`); the domains, the terms, the bound, the locality relation and all constants do not involve
`Θ₀`.  Here the activity is rebuilt for every datum `Θ` of an open set `V ⊆ SΛ`.

* `StepSetting.continuous_hatOf`, `continuous_term_hatOf`: the hat map is continuous, and so are
  the diagonal terms composed with it (from `DiagCont`).
* `DirectTermsFamily`, `DirectTerms.atTheta`: the family hypothesis (the same terms, the same
  constants, an open set `V ⊆ SΛ`, reflexivity of the source agreement and continuity of the
  diagonal terms on `V`) and the resulting `DirectTerms` at each `Θ ∈ V`.
* `dtAct`, `labelActFamily`: the activity of `labelAct_of_directTerms` (same formula) at a given
  `DirectTerms`, and the family over the datum.
* `labelActFamily_analytic`: joint analyticity in `(Θ, u)` on `V ×ˢ ball 0 Rσ`.
* `paramMarkFamily_of_marks`, `paramMarkFamily_zero_marks`: the `ParamMarkFamily` with the
  physical activities, carrier `physCarrier`, `𝒰 = ball 0 Rσ`.
* `labelActFamily_local`, `physical_labelActFamily_local`: locality in the datum.
* `nonempty_directTermsFamily`: the family hypothesis is inhabited.

No marks are constructed (they are data satisfying their own fields, or zero), the determinant term
is not treated, and nothing depends on a choice of generating set for the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Metric

section Hat

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

/-- **Continuity of the hat map.**  The hat variable of the block variables is continuous in the
block configuration (product topology). -/
theorem StepSetting.continuous_hatOf (ρ : ℝ) (hp : 0 < S.p₁) :
    Continuous (S.hatOf m₀ ρ hp) := by
  refine continuous_pi fun q => ?_
  have h1 : Continuous (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩ q.2) :=
    (EuclideanSpace.proj q.2).continuous.comp
      ((continuous_apply (⟨q.1, rfl⟩ : {u : S.U // S.cellOf m₀ u = S.cellOf m₀ q.1})).comp
        (continuous_apply (S.cellOf m₀ q.1)))
  exact (continuous_clampC ρ).comp (Complex.continuous_ofReal.comp h1)

end Hat

end Balaban.Fluctuation
