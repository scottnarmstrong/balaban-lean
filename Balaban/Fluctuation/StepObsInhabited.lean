/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepObs

/-!
# `ClassRegularObs` is not contradictory

For the zero effective action and `β = 0`, with `N = 0` components (so that the components `i : Fin N`
of the observable vector are vacuous), `ClassRegularObs` holds.  For `N > 0` the components of
`ℳ_k` contain the field `svec (bgField (dataU (ψ^{(k)} + t ψ')))`, whose regularity along the ray is
an analytic statement about the Background field and is the content of the named input.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem classRegularObs_of_N_zero (S : StepSetting d L N₁ m₁ k 0 ϱ) (hβ : S.β = 0) :
    S.ClassRegularObs (zeroClass d L N₁ m₁ k 0 ϱ) 0 :=
  ⟨classRegularLoc_zero S hβ, fun _ i => i.elim0⟩

theorem nonempty_classRegularObs (hk1 : 1 ≤ k) (a₁ ν p₁ δ : ℝ) :
    ∃ S : StepSetting d L N₁ m₁ k 0 ϱ,
      Nonempty (S.ClassRegularObs (zeroClass d L N₁ m₁ k 0 ϱ) 0) := by
  obtain ⟨S⟩ := nonempty_stepSetting (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (N := 0) (ϱ := ϱ)
    hk1 a₁ ν 0 p₁ δ
  exact ⟨{ S with β := 0 }, ⟨classRegularObs_of_N_zero { S with β := 0 } rfl⟩⟩

end Balaban.Fluctuation
