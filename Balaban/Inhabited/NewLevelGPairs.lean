/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelHPairs

/-!
# The marks of the old terms of two systems from the premises of the old terms

`NewLevelSystem.G₁_twoTorus_of_pairs`: the marks `G₁` of corresponding old terms of two systems
agree: the `t`-derivative at `0` of the localized old term is the derivative of equal functions,
equal for the marks `t'` near `0` by `evTerm_twoTorus_of_premises`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ : ℝ}

open Classical in
/-- **The marks of corresponding old terms of two systems agree.** -/
theorem NewLevelSystem.G₁_twoTorus_at_of_pairs
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (τ' : NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z})
    (q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
      (fun τ => polyDom S'.G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) z'})
    (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (hcond : ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < MarkBudgetAudit.corrU) ↔
      ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw S'.G' (compWeight L S'.a₁) S'.ν (k + 1) 1 t' ∧ ‖u‖ < MarkBudgetAudit.corrU))
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hq1 : q'.1.1 = τ')
    (hq2 : q'.1.2 = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' q.1.2)
    (hX : NS'.O.X₁f τ' = (NS.O.X₁f q.1.1).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : NS'.O.jL τ' = NS.O.jL q.1.1)
    (hpairs : ∀ᶠ s in nhds (0 : ℂ),
      TermPairPremisesAt NS NS' q.1.1 τ' θ θ' q.1.2 Φ Φ' u s) :
    NS'.G₁ θ' q' u Φ' = NS.G₁ θ q u Φ := by
  rw [NS.hG₁, NS'.hG₁]
  by_cases hc : ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < MarkBudgetAudit.corrU)
  · have hc' := hcond.1 hc
    simp only [hc.1, hc.2, hc'.1, and_self, ite_true]
    rcases q' with ⟨⟨b', Y2⟩, hq'⟩
    simp only at hq1 hq2
    subst hq1 hq2
    have aux : ∀ {c c' : ℂ} {f f' : ℂ → ℂ}, c' = c → f' =ᶠ[nhds 0] f →
        c' * deriv f' 0 = c * deriv f 0 := fun hc h => by rw [hc, h.deriv_eq]
    refine aux (by rw [hβ]) ?_
    filter_upwards [hpairs] with s hs
    exact evTerm_twoTorus_of_premisesAt NS NS' q.1.1 _ θ θ' q.1.2 _ Φ Φ' u s haS hνS hβ hbU
      hX hm₀ hj rfl hs
  · have hc' : ¬ ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw S'.G' (compWeight L S'.a₁) S'.ν (k + 1) 1 t' ∧ ‖u‖ < MarkBudgetAudit.corrU) :=
      fun h => hc (hcond.2 h)
    simp only [hc, hc', ite_false]

open Classical in
/-- **The marks of corresponding old terms of two systems agree.** -/
theorem NewLevelSystem.G₁_twoTorus_of_pairs
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (e : NS.O.ι ≃ NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (q : {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z})
    (q' : {q // q ∈ markedIdx (fun _ : NS'.O.ι => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
      (fun τ => polyDom S'.G' (NS'.O.X₁f τ) NS'.O.m₀ (NS'.O.jL τ) (NS'.O.𝒦X τ)) z'})
    (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (hcond : ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < MarkBudgetAudit.corrU) ↔
      ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw S'.G' (compWeight L S'.a₁) S'.ν (k + 1) 1 t' ∧ ‖u‖ < MarkBudgetAudit.corrU))
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hq1 : q'.1.1 = e q.1.1)
    (hq2 : q'.1.2 = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' q.1.2)
    (hX : ∀ τ, NS'.O.X₁f (e τ) = (NS.O.X₁f τ).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : ∀ τ, NS'.O.jL (e τ) = NS.O.jL τ)
    (hpairs : ∀ᶠ s in nhds (0 : ℂ),
      TermPairPremises NS NS' e q.1.1 θ θ' q.1.2 Φ Φ' u s) :
    NS'.G₁ θ' q' u Φ' = NS.G₁ θ q u Φ :=
  NS.G₁_twoTorus_at_of_pairs NS' (e q.1.1) θ θ' q q' u Φ Φ' hcond haS hνS hβ hbU hq1 hq2 (hX _) hm₀ (hj _) hpairs

end Balaban.Inhabited
