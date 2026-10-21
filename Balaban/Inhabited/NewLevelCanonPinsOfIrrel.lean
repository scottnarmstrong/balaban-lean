/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelClassE
public import Balaban.Inhabited.NewLevelSystem

/-!
# The canonical pins of the inherited levels from `OldTermsAreIrrel`

`OldTermsAreIrrel` (ruling R13) gives the labels `(jL τ, y τ, X τ)` of the inherited levels in
`AdmPairs`, injectively, and `Eτ`.  `OldTermsCanonPinsAt` is `OldTermsAreIrrel` together with two
more facts that are not consequences of it: every admissible pair is the label of an inherited level
(surjectivity; the constraint `∑ τ, Eτ τ = Jr.EJ C` on the sum does not force it), and the covering
data `X₁f`, `𝒦X`, `Gk`, `ρ` are functions `F` of the label.
`oldTermsCanonPinsAt_of_irrel` assembles the pins from these two facts.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The canonical pins from the labels of `OldTermsAreIrrel`, surjectivity onto the admissible
pairs and the covering data as functions of the label.** -/
theorem oldTermsCanonPinsAt_of_irrel {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {t : ℝ} {O : OldTermSystem S t}
    (F : CanonCover d L N₁ m₁ k ϱ O.ϱ₁) (hm : O.m₀ = C.m₀) (i₀ i₁ : Fin N)
    (y : O.ι → CTorus d L N₁ m₁ (k + 1)) (X : O.ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hE : ∀ τ r, O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2)
    (hlab : ∀ τ, 1 ≤ O.jL τ ∧ O.jL τ ≤ k ∧ Aligned (L ^ O.jL τ) (y τ) ∧
      IsPolyDom C.m₀ (O.jL τ) (X τ) ∧ y τ ∈ X τ)
    (hinj : ∀ τ τ', O.jL τ = O.jL τ' → y τ = y τ' → X τ = X τ' → τ = τ')
    (hsurj : ∀ p ∈ AdmPairs L N₁ m₁ k d C.m₀ k, ∃ τ, (O.jL τ, y τ, X τ) = p)
    (hpin : ∀ τ, O.X₁f τ = F.X₁fC (O.jL τ) (y τ) (X τ) ∧ O.𝒦X τ = F.𝒦XC (O.jL τ) (y τ) (X τ) ∧
      O.Gk τ = F.GkC (O.jL τ) (y τ) (X τ) ∧ O.Gj τ = F.GjC (O.jL τ) (y τ) (X τ) ∧ O.ρ = F.ρC ∧
      O.XL τ = polySet C.m₀ (O.jL τ) (y τ) (X τ)) :
    OldTermsCanonPinsAt S C O F i₀ i₁ :=
  ⟨hm, y, X, hE, ⟨fun τ _ => hlab τ, fun a _ b _ h => by
      simp only [Prod.mk.injEq] at h
      exact hinj a b h.1 h.2.1 h.2.2, fun p hp => by
      obtain ⟨τ, hτ⟩ := hsurj p hp
      exact ⟨τ, Set.mem_univ _, hτ⟩⟩, hpin⟩

end Balaban.Inhabited
