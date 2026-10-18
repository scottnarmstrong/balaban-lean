/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyGCore
public import Balaban.Fluctuation.MarkedEvParam
import Mathlib.Tactic.Linarith

/-!
# The explicit terms of the core in the form `evDec`

The core `e0CoeffFamily_value_fromTowerG_core` exports the terms `Tt` of the direct terms of the
zero class at zero source as the potential part with the marked energy functional written out
(`evTerm … (fun u s => blockEnergyFun … )`, hat variable `hatPsiF`).  `explicit_evDec_of_core`
rewrites this by `FFmarked_one_zero` into the form `evDec … ∅ 1 0` with the hat constant
`(β L^(k(d-2)))^(-1/2)` used by the two-torus comparison.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

/-- **The explicit terms of the core in the form `evDec`.** -/
theorem explicit_evDec_of_core {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁] (ν β p₁ : ℝ) {ϱ : ℝ}
    (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    {Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) →
      ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
      (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ}
    {F₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    {Sol₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
        ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)}
    (hT : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                Tt Y x w σ (Θ, 0) = -(S.β : ℂ) *
                  ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      S.G' 1 (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k z
                        (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat S.G' (stepG d L N₁ T.m₁ k ϱ) (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                              (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                          (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0) :
    ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
      (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
      (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
      Tt Y x w σ (Θ, 0) = -(S.β : ℂ) *
        ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
            (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) S.a₁ S.ν S.hG'
            (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
            (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y)
            w.1) taylorWeight x.1 σ Θ
        else 0 := by
  intro Y x w σ Θ
  have hd2 : 2 ≤ d := by have := T.hd; omega
  have hb : S.betaU = β * (L : ℝ) ^ (k * (d - 2)) := by
    subst hS
    exact hatStepKG_betaU T.hN hd2 k T.m₁ _ hk ν β p₁ T.δ
  rw [hT Y x w σ Θ, hb]
  refine congrArg (fun t => -((S.β : ℝ) : ℂ) * t) (Finset.sum_congr rfl fun z _ => ?_)
  by_cases hY : Y ∈ polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
      (LocalCover.fam 1 (LocalCover.blockSite k z))
  · rw [ite_eq_left hY, ite_eq_left hY]
    exact congrArg (fun FF => rayTerm (dl3 (evTerm
      (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) :
        Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' 1
      (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z))) FF Y) w.1)
        taylorWeight x.1 σ Θ)
      (FFmarked_one_zero (a₁ := S.a₁) (ν := S.ν)
        (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) S.hG'
        (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
        (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k z) ∅).symm
  · rw [ite_eq_right hY, ite_eq_right hY]

end Balaban.Inhabited
