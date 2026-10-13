/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexSource

/-!
# The old-term split of the exponent increments of a step (FLUCTUATION.md §2.6)

For an arbitrary class member `C` the two exponent increments `W₁`, `W₂` of the complex step split
into the part of the zero class plus the differences of the old terms:

* `WoneC_eq_action_add_oldE`: `W₁ = -β V^{(k)} + (ℰ_k(ψ_k + sψ') - ℰ_k(ψ_k))`;
* `WtwoC_eq_bare_add_oldM`: `W₂(g)` is the bare background-source increment (the value for the zero
  class) plus the difference of the sums of the old observable terms `∑_{j=1}^k ℱ^{(j)}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)
  (C : StepClass d L N₁ m₁ k N ϱ)

/-- The exponent `W₁` of the step for a general class member is the main action plus the
difference of the old energies. -/
theorem WoneC_eq_action_add_oldE (s : ℝ) (x : S.E) :
    S.WoneC C s x =
      -(S.β : ℂ) * S.VkC (S.psiAtC s x) +
      (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (S.dataUC (S.psiAtC s x)) -
       EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (S.dataUC S.psi0C)) := rfl

/-- The exponent `W₂` of the step for a general class member is the value for the zero class plus
the difference of the sums of the old observable terms. -/
theorem WtwoC_eq_bare_add_oldM
    (g : Fld d L N₁ m₁ (k + 1) N) (t : ℝ) (x : S.E) :
    S.WtwoC C g t x =
      S.WtwoC (zeroClass d L N₁ m₁ k N ϱ) g t x +
      ((∑ j ∈ Finset.Icc 1 k,
          Floc C.m₀ C.Tm j
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC (S.psiAtC t x))).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC (S.psiAtC t x))).2 g) -
       (∑ j ∈ Finset.Icc 1 k,
          Floc C.m₀ C.Tm j
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC S.psi0C)).1
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              (S.dataUC S.psi0C)).2 g)) := by
  unfold StepSetting.WtwoC StepSetting.dFC FcompAtC
  have h0 : (zeroClass d L N₁ m₁ k N ϱ).Tm = zeroTerms d L N₁ m₁ (k + 1) N ϱ := rfl
  have h1 : (zeroClass d L N₁ m₁ k N ϱ).m₀ = 0 := rfl
  simp only [h0, h1]
  have z : ∀ ψ : S.EC, ∑ j ∈ Finset.Icc 1 k,
      Floc 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) j
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC ψ)).1
        (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC ψ)).2 g = 0 := by
    intro ψ
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [Floc_zero]
  rw [z, z]
  ring

end Balaban.Fluctuation
