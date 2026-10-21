/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelTermPair

/-!
# The explicit thick activities of two systems from the premises of the old terms

`NewLevelSystem.H_twoTorus_of_pairs`: `NewLevelSystem.H_twoTorus` with the two per-term equalities
discharged by `evTerm_twoTorus_of_premises`: the premises `TermPairPremises` of each old term in the
domain at the marks `(u, 0)` and `(0, 0)`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ : ℝ}

open Classical in
/-- **The explicit thick activities of two systems agree, from the premises of the old terms.** -/
theorem NewLevelSystem.H_twoTorus_of_pairs
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (e : NS.O.ι ≃ NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : {Y // Y ∈ NS.𝒴C}) (Y' : {Y // Y ∈ NS'.𝒴C}) (u : ℂ)
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (hcond : ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < MarkBudgetAudit.corrU) ↔
      ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw S'.G' (compWeight L S'.a₁) S'.ν (k + 1) 1 t' ∧ ‖u‖ < MarkBudgetAudit.corrU))
    (hP : ∀ τ, Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) ↔
      Y'.1 ∈ polyDom S'.G' (NS'.O.X₁f (e τ)) NS'.O.m₀ (NS'.O.jL (e τ)) (NS'.O.𝒦X (e τ)))
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hX : ∀ τ, NS'.O.X₁f (e τ) = (NS.O.X₁f τ).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : ∀ τ, NS'.O.jL (e τ) = NS.O.jL τ)
    (hY : Y'.1 = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' Y.1)
    (hu : ∀ τ, Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) →
      TermPairPremises NS NS' e τ θ θ' Y.1 Φ Φ' u 0)
    (h0 : ∀ τ, Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) →
      TermPairPremises NS NS' e τ θ θ' Y.1 Φ Φ' 0 0) :
    NS'.H θ' Y' u Φ' = NS.H θ Y u Φ :=
  NS.H_twoTorus NS' e θ θ' Y Y' u u Φ Φ' hcond hP (by rw [hβ])
    (fun τ hτ => evTerm_twoTorus_of_premises NS NS' e τ θ θ' Y.1 Y'.1 Φ Φ' u 0 haS hνS hβ hbU
      (hX τ) hm₀ (hj τ) hY (hu τ hτ))
    (fun τ hτ => evTerm_twoTorus_of_premises NS NS' e τ θ θ' Y.1 Y'.1 Φ Φ' 0 0 haS hνS hβ hbU
      (hX τ) hm₀ (hj τ) hY (h0 τ hτ))

end Balaban.Inhabited
