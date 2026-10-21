/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelHTwoTorus
public import Balaban.Polymer.OldTermPair

/-!
# The localized old terms of two new-level systems from `OldTermPair`

`evTerm_twoTorus_of_pair`: the value of the localized old term `τ` of `NS` at a mark `(u, t₀)`
and the value of the old term `e τ` of `NS'` agree, from the premises structure `OldTermPair` at
the data of the pair.  The old terms of the second system have the label cubes
`NS'.O.X₁f (e τ) = (NS.O.X₁f τ).image bm` (`X₁f_image_boxMap` is the hypothesis `hX`), the common
constants of the two steps are equal, and `θ`, `θ'` are the raw parts of data `D`, `D'`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.Polymer.TwoTorusStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ : ℝ}

/-- **The localized old terms of two systems agree, from the premises structure.** -/
theorem evTerm_twoTorus_of_pairAt
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Y' : Set (CTorus d L N₁' m₁ (k + 1)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ)
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hX : NS'.O.X₁f τ' = (NS.O.X₁f τ).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : NS'.O.jL τ' = NS.O.jL τ)
    (hY : Y' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' Y)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ cψ δc : ℝ}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {r₀ δ₃ δfl : ℝ} {jj : ℕ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X₀' : Finset (CTorus d L N₁' m₁ (k + 1))} {R : ℕ} {Z : Set (CTorus d L N₁ m₁ (k + 1))}
    {D : BgData S.G' N} {D' : BgData S'.G' N}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) = rawOf D')
    (P : OldTermPair S.G' S'.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁' m₁ k ϱ) S.a₁ S.ν c BG κ eps
      Kc Cx c₂ BG₂ δ₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) cψ δc (NS.O.F₁L τ)
      (NS'.O.F₁L τ') (NS.O.SolL τ) (NS'.O.SolL τ') NS.O.m₀ (NS.O.jL τ) X (NS.O.𝒦X τ)
      X' (NS'.O.𝒦X τ') (NS.O.X₁f τ) (NS.O.Gk τ) (NS'.O.Gk τ') (NS.O.Gj τ) (NS'.O.Gj τ') r₀ δ₃ δfl jj X₀ X₀'
      (NS.O.FkL τ) (NS'.O.FkL τ') (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (fun r => (S.β : ℂ)⁻¹ * NS'.O.Eτ τ' r) Z R Y D D'
      (S.hatOf 1 NS.O.ρ NS.hp Φ) (S'.hatOf 1 NS'.O.ρ NS'.hp Φ') (S.blockU z) (S'.blockU z')
      u t₀) :
    evDec (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ') S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L τ') (NS'.O.SolL τ')
        (eTermFun S'.G' (NS'.O.Gk τ') (NS'.O.Gj τ') (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL τ') (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ τ' r))
        (S'.blockU z') u t₀ Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ') =
      evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) u t₀ Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ) := by
  have key := evDec_oldTerm_of_pair P
  rw [hθ, hθ'] 
  rw [hX, hm₀, hj, hY, haS, hνS, hbU, hβ]
  exact key

/-- **The localized old terms of two systems agree, from the premises structure.** -/
theorem evTerm_twoTorus_of_pair
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (e : NS.O.ι ≃ NS'.O.ι) (τ : NS.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Y' : Set (CTorus d L N₁' m₁ (k + 1)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ)
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hX : NS'.O.X₁f (e τ) = (NS.O.X₁f τ).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : NS'.O.jL (e τ) = NS.O.jL τ)
    (hY : Y' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' Y)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ cψ δc : ℝ}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} {X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {r₀ δ₃ δfl : ℝ} {jj : ℕ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X₀' : Finset (CTorus d L N₁' m₁ (k + 1))} {R : ℕ} {Z : Set (CTorus d L N₁ m₁ (k + 1))}
    {D : BgData S.G' N} {D' : BgData S'.G' N}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) = rawOf D')
    (P : OldTermPair S.G' S'.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁' m₁ k ϱ) S.a₁ S.ν c BG κ eps
      Kc Cx c₂ BG₂ δ₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) cψ δc (NS.O.F₁L τ)
      (NS'.O.F₁L (e τ)) (NS.O.SolL τ) (NS'.O.SolL (e τ)) NS.O.m₀ (NS.O.jL τ) X (NS.O.𝒦X τ)
      X' (NS'.O.𝒦X (e τ)) (NS.O.X₁f τ) (NS.O.Gk τ) (NS'.O.Gk (e τ)) (NS.O.Gj τ) (NS'.O.Gj (e τ)) r₀ δ₃ δfl jj X₀ X₀'
      (NS.O.FkL τ) (NS'.O.FkL (e τ)) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (fun r => (S.β : ℂ)⁻¹ * NS'.O.Eτ (e τ) r) Z R Y D D'
      (S.hatOf 1 NS.O.ρ NS.hp Φ) (S'.hatOf 1 NS'.O.ρ NS'.hp Φ') (S.blockU z) (S'.blockU z')
      u t₀) :
    evDec (NS'.O.X₁f (e τ)) NS'.O.m₀ (NS'.O.jL (e τ)) (NS'.O.𝒦X (e τ)) S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L (e τ)) (NS'.O.SolL (e τ))
        (eTermFun S'.G' (NS'.O.Gk (e τ)) (NS'.O.Gj (e τ)) (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL (e τ)) (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ (e τ) r))
        (S'.blockU z') u t₀ Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ') =
      evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) u t₀ Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ) := by
  exact evTerm_twoTorus_of_pairAt NS NS' τ (e τ) θ θ' Y Y' Φ Φ' u t₀ haS hνS hβ hbU hX hm₀ hj hY hθ hθ' P

/-- **The premises of the comparison of the old term `τ` of `NS` with the old term `e τ` of `NS'`
at the mark `(u, t₀)`**: some constants, a box radius, a label margin `Z`, data `D`, `D'` with raw
parts `θ`, `θ'`, and the premises structure `OldTermPair` of these data. -/
def TermPairPremisesAt
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ) : Prop :=
  ∃ (c BG κ eps Kc Cx c₂ BG₂ δ₁ cψ δc : ℝ) (X : Set (CTorus d L N₁ m₁ (k + 1)))
    (X' : Set (CTorus d L N₁' m₁ (k + 1))) (r₀ δ₃ δfl : ℝ) (jj : ℕ)
    (X₀ : Finset (CTorus d L N₁ m₁ (k + 1))) (X₀' : Finset (CTorus d L N₁' m₁ (k + 1))) (R : ℕ)
    (Z : Set (CTorus d L N₁ m₁ (k + 1))) (D : BgData S.G' N) (D' : BgData S'.G' N),
    (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D ∧
    (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) = rawOf D' ∧
    Nonempty (OldTermPair S.G' S'.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁' m₁ k ϱ) S.a₁ S.ν c BG κ
      eps Kc Cx c₂ BG₂ δ₁ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) cψ δc (NS.O.F₁L τ)
      (NS'.O.F₁L τ') (NS.O.SolL τ) (NS'.O.SolL τ') NS.O.m₀ (NS.O.jL τ) X (NS.O.𝒦X τ)
      X' (NS'.O.𝒦X τ') (NS.O.X₁f τ) (NS.O.Gk τ) (NS'.O.Gk τ') (NS.O.Gj τ) (NS'.O.Gj τ')
      r₀ δ₃ δfl jj X₀ X₀' (NS.O.FkL τ) (NS'.O.FkL τ') (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (fun r => (S.β : ℂ)⁻¹ * NS'.O.Eτ τ' r) Z R Y D D'
      (S.hatOf 1 NS.O.ρ NS.hp Φ) (S'.hatOf 1 NS'.O.ρ NS'.hp Φ') (S.blockU z) (S'.blockU z') u t₀)

/-- **The localized old terms of two systems agree, from the premises.** -/
theorem evTerm_twoTorus_of_premisesAt
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Y' : Set (CTorus d L N₁' m₁ (k + 1)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ)
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hX : NS'.O.X₁f τ' = (NS.O.X₁f τ).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : NS'.O.jL τ' = NS.O.jL τ)
    (hY : Y' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' Y)
    (hP : TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀) :
    evDec (NS'.O.X₁f τ') NS'.O.m₀ (NS'.O.jL τ') (NS'.O.𝒦X τ') S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L τ') (NS'.O.SolL τ')
        (eTermFun S'.G' (NS'.O.Gk τ') (NS'.O.Gj τ') (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL τ') (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ τ' r))
        (S'.blockU z') u t₀ Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ') =
      evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) u t₀ Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ) := by
  obtain ⟨c, BG, κ, eps, Kc, Cx, c₂, BG₂, δ₁, cψ, δc, X, X', r₀, δ₃, δfl, jj, X₀, X₀', R, Z, D, D',
    hθ, hθ', ⟨P⟩⟩ := hP
  exact evTerm_twoTorus_of_pairAt NS NS' τ τ' θ θ' Y Y' Φ Φ' u t₀ haS hνS hβ hbU hX hm₀ hj hY hθ hθ' P

/-- **The premises of the comparison of the old term `τ` of `NS` with the old term `e τ` of `NS'`
at the mark `(u, t₀)`**: some constants, a box radius, a label margin `Z`, data `D`, `D'` with raw
parts `θ`, `θ'`, and the premises structure `OldTermPair` of these data. -/
def TermPairPremises
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (e : NS.O.ι ≃ NS'.O.ι) (τ : NS.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ) : Prop :=
  TermPairPremisesAt NS NS' τ (e τ) θ θ' Y Φ Φ' u t₀

/-- **The localized old terms of two systems agree, from the premises.** -/
theorem evTerm_twoTorus_of_premises
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {z' : RootIdx d L N₁' m₁ (k + 1)} {t' pp' : ℝ} {Jr' : S'.JointRep t' pp'}
    (NS' : NewLevelSystem S' C' z' Jr')
    (e : NS.O.ι ≃ NS'.O.ι) (τ : NS.O.ι) (θ : physParam N S) (θ' : physParam N S')
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Y' : Set (CTorus d L N₁' m₁ (k + 1)))
    (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, (S'.blockSplit 1 NS'.hp).Ωb b)
    (u t₀ : ℂ)
    (haS : S'.a₁ = S.a₁) (hνS : S'.ν = S.ν) (hβ : S'.β = S.β) (hbU : S'.betaU = S.betaU)
    (hX : NS'.O.X₁f (e τ) = (NS.O.X₁f τ).image
      (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (hm₀ : NS'.O.m₀ = NS.O.m₀) (hj : NS'.O.jL (e τ) = NS.O.jL τ)
    (hY : Y' = (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))) '' Y)
    (hP : TermPairPremises NS NS' e τ θ θ' Y Φ Φ' u t₀) :
    evDec (NS'.O.X₁f (e τ)) NS'.O.m₀ (NS'.O.jL (e τ)) (NS'.O.𝒦X (e τ)) S'.a₁ S'.ν S'.hG'
        ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS'.O.F₁L (e τ)) (NS'.O.SolL (e τ))
        (eTermFun S'.G' (NS'.O.Gk (e τ)) (NS'.O.Gj (e τ)) (stepG d L N₁' m₁ k ϱ)
          (compWeight L S'.a₁) (NS'.O.FkL (e τ)) (fun r => (S'.β : ℂ)⁻¹ * NS'.O.Eτ (e τ) r))
        (S'.blockU z') u t₀ Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), S'.hatOf 1 NS'.O.ρ NS'.hp Φ') =
      evDec (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) S.a₁ S.ν S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (NS.O.F₁L τ) (NS.O.SolL τ)
        (eTermFun S.G' (NS.O.Gk τ) (NS.O.Gj τ) (stepG d L N₁ m₁ k ϱ)
          (compWeight L S.a₁) (NS.O.FkL τ) (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r))
        (S.blockU z) u t₀ Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 NS.O.ρ NS.hp Φ) := by
  exact evTerm_twoTorus_of_premisesAt NS NS' τ (e τ) θ θ' Y Y' Φ Φ' u t₀ haS hνS hβ hbU hX hm₀ hj hY hP

end Balaban.Inhabited
