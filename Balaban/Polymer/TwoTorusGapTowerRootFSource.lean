/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexNonvanish
public import Balaban.Fluctuation.StepIdentityInhabited

/-!
# The non-observable source term of the tower's step identity (blocker 7)

The step identity of the tower (`stepIdentity_zeroClass_fibre_fromTowerG`) has the exponent
`-β A_new - E_ppp n_U + ℱ_k(ψ^{(k)}, g) + ∑ e0 + ∑ g mObs`, where `ℱ_k` is
`FcompAtC (zeroClass …).m₀ (zeroClass …).Tm … psiKdC g`.  For the zero class the old terms vanish,
and `ℱ_k` is the bare pairing `⟨g, φ_k⟩₁` of the source with the complex background field `φ_k` of
the step at `psiKdC`.  This pairing

* is linear in `g` and vanishes at `g = 0`, so it is not part of the vacuum term that cancels in
  `Z(g)/Z(0)` (that is `-β A_new - E_ppp n_U + ∑ e0`, free of `g`);
* has the single-site terms `g(y)·φ_k(y)`, nonzero only for `y` in the domain `Ω₁` of the step.

It is the linear part `⟨g, h⟩` of Root-F together with the deviation `φ_k - h` of the background
field from the external field; no landed statement bounds that deviation or writes it as a sum over
polymers with the decay of Root-F, so the pairing is not yet a Root-F term.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.Polymer

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The source term of the zero-class step identity is the pairing with the background field.** -/
theorem fcompAtC_zeroClass_psiKdC_eq (S : StepSetting d L N₁ m₁ k N ϱ)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC g =
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        svec (stepG d L N₁ m₁ k ϱ)
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKdC) y i :=
  FcompAtC_zero_eq 0 S.a S.ν (Nat.le_succ k) S.psiKdC g

/-- The source term vanishes at `g = 0`. -/
theorem fcompAtC_zeroClass_psiKdC_zero (S : StepSetting d L N₁ m₁ k N ϱ) :
    FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC 0 = 0 := by
  rw [fcompAtC_zeroClass_psiKdC_eq]
  simp

/-- The source term is linear in `g`. -/
theorem fcompAtC_zeroClass_psiKdC_add (S : StepSetting d L N₁ m₁ k N ϱ)
    (g g' : Fld d L N₁ m₁ (k + 1) N) :
    FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC (g + g') =
      FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC g +
      FcompAtC (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) S.psiKdC g' := by
  simp only [fcompAtC_zeroClass_psiKdC_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [add_mul]

/-- The single-site terms of the source term vanish off the domain `Ω₁` of the step. -/
theorem fcompAtC_zeroClass_psiKdC_site_eq_zero (S : StepSetting d L N₁ m₁ k N ϱ)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∉ (stepG d L N₁ m₁ k ϱ).Ω 1) (g : Fld d L N₁ m₁ (k + 1) N)
    (i : Fin N) :
    g y i * svec (stepG d L N₁ m₁ k ϱ)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) S.psiKdC) y i = 0 := by
  rw [svec_of_not_mem (stepG d L N₁ m₁ k ϱ) _ hy i, mul_zero]

end Balaban.Fluctuation
