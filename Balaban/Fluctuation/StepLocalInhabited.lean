/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepLocal

/-!
# `ClassRegularLoc` is inhabited

For the zero effective action and the degenerate coupling `β = 0` the exponent `Φ₁` vanishes, so
`ClassRegularLoc` holds (with the source `g = 0`); this shows the structure is not contradictory.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem Phi1_zero_of_beta (S : StepSetting d L N₁ m₁ k N ϱ) (hβ : S.β = 0) (y : S.E) :
    S.Phi1 (zeroClass d L N₁ m₁ k N ϱ) y = 0 := by
  unfold StepSetting.Phi1 StepSetting.dE
  show -((S.β : ℝ) : ℂ) * S.Vk (S.psi0 + y) +
    (EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _ -
      EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) _) = 0
  simp [EcompAt_zero, hβ]

/-- **`ClassRegularLoc` is inhabited**: zero effective action, `β = 0`, source `g = 0`. -/
theorem classRegularLoc_zero (S : StepSetting d L N₁ m₁ k N ϱ) (hβ : S.β = 0) :
    S.ClassRegularLoc (zeroClass d L N₁ m₁ k N ϱ) 0 := by
  refine ⟨classRegular_zero S, Set.univ, isOpen_univ, ?_, fun _ _ _ _ => Set.mem_univ _⟩
  have : S.Phi1 (zeroClass d L N₁ m₁ k N ϱ) = fun _ => 0 := funext (Phi1_zero_of_beta S hβ)
  rw [this]
  exact contDiffOn_const

theorem nonempty_classRegularLoc (hk1 : 1 ≤ k) (a₁ ν p₁ δ : ℝ) :
    ∃ S : StepSetting d L N₁ m₁ k N ϱ,
      Nonempty (S.ClassRegularLoc (zeroClass d L N₁ m₁ k N ϱ) 0) := by
  obtain ⟨S⟩ := nonempty_stepSetting (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (N := N) (ϱ := ϱ)
    hk1 a₁ ν 0 p₁ δ
  exact ⟨{ S with β := 0 }, ⟨classRegularLoc_zero { S with β := 0 } rfl⟩⟩

end Balaban.Fluctuation
