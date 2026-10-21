/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystem

/-!
# The canonical index set of the inherited levels

`AdmPairs m₀ k`: the triples `(j, y, X)` with `1 ≤ j ≤ k`, `y` an `L^j`-aligned site and `X ∈ 𝒟_j`
a polymer containing `y` (the index set of the sum `Edens` over the terms of the class).
`OldTermsCanon S C O`: the inherited levels `O` are the irrelevant terms of the class indexed
canonically, that is `τ ↦ (jL τ, y τ, X τ)` is a bijection of `O.ι` onto `AdmPairs`.  The producer of a
`NewLevelSystem` must prove it (the index set of the old terms is otherwise only constrained through
the sum `hEJ`).

* `OldTermsCanon.areIrrel`: it implies `OldTermsAreIrrel`;
* `oldTermsCanon_pair_equiv`: two canonical systems on two tori whose admissible pairs correspond
  under a map `σ` have the index bijection `e` of the old terms in the box.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The admissible irrelevant pairs of the class.** -/
def AdmPairs (L N₁ m₁ k : ℕ) (d : ℕ) [NeZero L] [NeZero N₁] (m₀ kk : ℕ) :
    Set (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) :=
  {p | 1 ≤ p.1 ∧ p.1 ≤ kk ∧ Aligned (L ^ p.1) p.2.1 ∧ IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k + 1) m₀ p.1 p.2.2 ∧ p.2.1 ∈ p.2.2}

/-- **The inherited levels are the irrelevant terms of the class, indexed canonically.** -/
def OldTermsCanon (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {t : ℝ}
    (O : OldTermSystem S t) : Prop :=
  O.m₀ = C.m₀ ∧ ∃ (i₀ i₁ : Fin N) (y : O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : O.ι → Set (CTorus d L N₁ m₁ (k + 1))),
    (∀ τ r, O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2) ∧
    Set.BijOn (fun τ => (O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k)

theorem OldTermsCanon.areIrrel {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {t : ℝ} {O : OldTermSystem S t} (h : OldTermsCanon S C O) : OldTermsAreIrrel S C O := by
  obtain ⟨h0, i₀, i₁, y, X, hE, -⟩ := h
  exact ⟨h0, i₀, i₁, y, X, hE⟩

end Balaban.Inhabited
