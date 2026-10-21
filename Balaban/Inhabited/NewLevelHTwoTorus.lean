/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystem
public import Balaban.Inhabited.NewLevelHTransport

/-!
# The explicit thick activity of two new-level systems

`NewLevelSystem.H_twoTorus`: for two systems `NS`, `NS'` (on two step tori) whose old terms
correspond under a bijection `e` of the index types, with `Y ∈ polyDom τ ↔ Y' ∈ polyDom' (e τ)`,
the same domain condition on the parameters, and corresponding values of the localized terms at the
marks `(u, 0)` and `(0, 0)` (the conclusions of `evDec_oldTerm_of_pair`), the explicit activities
`H` agree.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ : ℝ}

open Classical in
/-- **The explicit thick activities of two systems agree.** -/
theorem NewLevelSystem.H_twoTorus
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (e : NS.O.ι ≃ NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : {Y // Y ∈ NS.𝒴C}) (Y' : {Y // Y ∈ NS'.𝒴C}) (u u' : ℂ) (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (hcond : ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < MarkBudgetAudit.corrU) ↔
      ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw S'.G' (compWeight L S'.a₁) S'.ν (k + 1) 1 t' ∧ ‖u'‖ < MarkBudgetAudit.corrU))
    (hP : ∀ τ, Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) ↔
      Y'.1 ∈ polyDom S'.G' (NS'.O.X₁f (e τ)) NS'.O.m₀ (NS'.O.jL (e τ)) (NS'.O.𝒦X (e τ)))
    (hβ : (S'.β : ℂ) = S.β)
    (hu : ∀ τ, Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) →
      evDec (NS'.O.X₁f (e τ)) NS'.O.m₀ (NS'.O.jL (e τ)) (NS'.O.𝒦X (e τ)) S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L (e τ)) (NS'.O.SolL (e τ))
        (eTermFun S'.G' (NS'.O.Gk (e τ)) (NS'.O.Gj (e τ)) (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL (e τ)) (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ (e τ) r))
        (S'.blockU z') u' 0 Y'.1
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ') =
      evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) u 0 Y.1
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ))
    (h0 : ∀ τ, Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) →
      evDec (NS'.O.X₁f (e τ)) NS'.O.m₀ (NS'.O.jL (e τ)) (NS'.O.𝒦X (e τ)) S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L (e τ)) (NS'.O.SolL (e τ))
        (eTermFun S'.G' (NS'.O.Gk (e τ)) (NS'.O.Gj (e τ)) (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL (e τ)) (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ (e τ) r))
        (S'.blockU z') 0 0 Y'.1
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ') =
      evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) 0 0 Y.1
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ)) :
    NS'.H θ' Y' u' Φ' = NS.H θ Y u Φ := by
  have := NS.O.fin
  have := NS'.O.fin
  rw [NS.hH, NS'.hH]
  by_cases hc : ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t ∧ ‖u‖ < MarkBudgetAudit.corrU)
  · have hc' := hcond.1 hc
    simp only [hc.1, hc.2, hc'.1, hc'.2, and_self, ite_true]
    refine @sum_ite_sub_equiv _ _ NS.O.fin NS'.O.fin e
      (fun τ => Y.1 ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
      (fun τ' => Y'.1 ∈ polyDom S'.G' (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ'))
      _ _
      (S.β : ℂ) (S'.β : ℂ) hβ
      (fun τ => evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) u 0 Y.1
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ))
      (fun τ => evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) 0 0 Y.1
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ))
      (fun τ' => evDec (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ') S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L τ') (NS'.O.SolL τ')
        (eTermFun S'.G' (NS'.O.Gk τ') (NS'.O.Gj τ') (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL τ') (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ τ' r))
        (S'.blockU z') u' 0 Y'.1
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ'))
      (fun τ' => evDec (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ') S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L τ') (NS'.O.SolL τ')
        (eTermFun S'.G' (NS'.O.Gk τ') (NS'.O.Gj τ') (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL τ') (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ τ' r))
        (S'.blockU z') 0 0 Y'.1
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ'))
      hP hu h0
  · have hc' : ¬ ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw S'.G' (compWeight L S'.a₁) S'.ν (k + 1) 1 t' ∧ ‖u'‖ < MarkBudgetAudit.corrU) :=
      fun h => hc (hcond.2 h)
    simp only [hc, hc', ite_false]

end Balaban.Inhabited
