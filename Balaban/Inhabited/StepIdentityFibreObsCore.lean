/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsFamilyJointCore
public import Balaban.Inhabited.StepIdentityFibre
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The observable family of all sites with the formulas of its activity and its terms

`obsFamily_pair_fibre_fromTowerG_rho_core` is `obsFamily_pair_fibre_fromTowerG_rho` together with
the formulas of `obsFamily_full_fromTowerG_rho_core`: the labels correspond to the domains of the
local covers of the blocks and of the sites, the activity `A` has its explicit values at the zero
source and at a nonzero source, and for every site `(y, i)` the family `Ev` of the coefficient
`mObs y i` is `evTerm … (siteFun … y i …)` for a decoupled pair.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- **The observable coefficient family of all sites with the formulas of the activity and of the
terms.**  The statement of `obsFamily_pair_fibre_fromTowerG_rho` with the three clauses of
`obsFamily_full_fromTowerG_rho_core`: after the labels `Lab` and the activity `A` are chosen, the
labels correspond to the domains of the local covers of the blocks and of the sites and `A` has its
explicit values at the zero source (decoupled pairs per block) and at a nonzero source (decoupled
pairs per site); for every site `(y, i)` the family `Ev` of `mObs y i` is
`evTerm … (siteFun … y i …)` for a decoupled pair `(F₁, Sol)`. -/
theorem obsFamily_pair_fibre_fromTowerG_rho_core {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 d L T.κ0 + 1))
        (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
            Set.univ) → ℂ),
        2 * εH ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∃ (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1)))) (ys : Lb ≃ {Y // Y ∈ 𝒴}),
          (∀ l, Lab.ysite l = (ys l).1) ∧
          𝒴 = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
              polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
            (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
              polyDom S.G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)) ∧
          ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)),
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₁ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol z p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2)) ∧
        ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb)
          (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          (A ((e.1, 0) : physParam N S) σ).H l Φ = -(S.β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Lab.ysite l ∈ polyDom S.G'
                (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                S.G' T.m₀ (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z
                  (F₁ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                    flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₁ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                        (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z)
                    (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) (Lab.ysite l))
                (S.hatOf T.m₀ p₁ hp Φ)) taylorWeight (S.hatOf T.m₀ p₁ hp Φ) σ
                (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
            else 0) ∧
      (∃ (F₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
              (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N →
              ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ))
          (Ev₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N → Set (CTorus d L N₁ T.m₁ (k + 1)) →
            RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ),
        (∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N) (s : DecParams S.G') (D : BgData S.G' N),
          (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₃ a (s, rawOf D) = (φ, α)) ∧
        (∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N)
          (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N),
          (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₃ a p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₃ a p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₃ a p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₃ a p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ a p).2)) ∧
        (∀ a : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Ev₃ a =
          evTerm
                  (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' T.m₀
                  (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ a.1))
                  (fun u t => siteFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) a.1 a.2
                    (F₃ a (extParams S.G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t, u.1))
                    (Sol₃ a (extParams S.G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t,
                      flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                        (F₃ a (extParams S.G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t, u.1))
                        u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃ a)
                          (extParams S.G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t) u.1 u.2))).1
                    (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃ a)
                      (extParams S.G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t) u.1 u.2))) ∧
        (∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁ T.m₁ (k + 1))),
          AnalyticOnNhd ℂ (Ev₃ a Y) (XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
        ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
          (A e σ).H l Φ = (A ((e.1, 0) : physParam N S) σ).H l Φ +
            ∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N,
              if Lab.ysite l ∈ polyDom S.G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k
                  (LocalCover.fam T.m₀ s.1) then
                e.2 s.1 s.2 * dirTerm (Ev₃ s (Lab.ysite l)) (fun _ => (1 : ℂ))
                  (S.hatOf T.m₀ p₁ hp Φ) (S.hatOf T.m₀ p₁ hp Φ) σ
                  (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
              else 0) ∧
        (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y),
            IsDj T.m₀ (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))),
            1 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ∧
            obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH ≤
              stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
                RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf S.G') × Edat (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)),
        (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S.G') × Edat (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol p).1 = dphi (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1) p.2.2.1 p.2.1
              (pertSource (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
            Dec2.DecFixed (coverOf S.G') (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
              (pertSource (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
            Small (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
                (pertSource (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' T.m₀
          (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ y))
          (fun u s => siteFun S.G' (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) y i
            (F₁ (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
            (Sol (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
              flEdat S.G' (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₁ (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
                  (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              (extParams S.G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))) ∧
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit T.m₀ hp).μ
                (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
                (fun m => blockMarkC S T.m₀ hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (obsUnitVec S m)) T.m₀ T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 T.m₀ (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (rootCube (m₀ := T.m₀) (blockIndex y))))
                (fun θ => obsGrFam S T.m₀ hp Ev
                  (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                  (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖mObs y i θ T'‖ ≤
                  ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
                      (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 +
                          K0 d L T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
                      (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
                      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
                    CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
                        (obsLab (Lab.sum Lab) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 T.m₀ (Lb ⊕ Lb)
                              (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                              (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
                  physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                    physRestrict (sitesOf T') (physIncl N S θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
        ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < q →
            (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N),
              (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
                ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
                  ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                  g y i * (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                    g y i =
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N,
                g y i * ∑ T', mObs y i ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T' := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ := obsFamily_full_fromTowerG_rho_core T hA p hCR hs0 hs ρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, hamp, hlab, hsrc, hsite⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1 Dsc S hS hp
  -- the site domains are polymer domains (from the covers of the scale datum)
  have hdj₀ : ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (_ : Fin N),
      ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y),
        IsDj T.m₀ (k + 1) Y := by
    subst hS
    exact fun y i => obsDomains_isDj (X₁f := LocalCover.nbhdF T.m₀ y) _ T.hd
      (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1
  have hbU0 : 0 < S.betaU := by
    rw [hS, show (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) from
      hatStepKG_betaU T.hN (by have := T.hd; omega) k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ]
    have : 0 < β := by linarith
    have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  choose hR hR1 hRθ Ev hEvx ha hd hb _ _ hcl hval using fun y i => hsite y i (hdj₀ y i)
  refine ⟨Lb, hLb, Lab, εH, hεH, A, fun y i θ T' => obsCoeffParam (S.blockSplit T.m₀ hp).μ
    (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le
      (hdj₀ y i) (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) (hR y i)
      (ball (0 : ℂ) (3 / 2)) θ t σ)
    (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
    (fun m => blockMarkC S T.m₀ hp m.1 m.2)
    (fun θ m T'' => obsHker
      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (fun Y => hatCoeff (Ev y i Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
        (obsUnitVec S m)) T.m₀ T'')
    (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (fun Y => Sum.inl (Sum.inr Y))
      (obsY0 T.m₀ (Lb ⊕ Lb)
        (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (rootCube (m₀ := T.m₀) (blockIndex y))))
    (fun θ => obsGrFam S T.m₀ hp (Ev y i)
      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
      (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T', hamp, hlab, hsrc, ?_, ?_⟩
  · intro y i hdj
    exact ⟨hR y i, hR1 y i, hRθ y i, Ev y i, hEvx y i, ha y i, hd y i, hb y i, fun _ _ => rfl,
      fun T' => ⟨(hcl y i T').2.2.2.1, (hcl y i T').2.2.2.2.1, (hcl y i T').2.2.2.2.2.1,
        (hcl y i T').2.2.2.2.2.2.1, (hcl y i T').2.2.2.2.2.2.2⟩⟩
  · intro D hDh hX g hg
    have hM := fun y i => (hval y i).1 D hDh hX g hg
    exact ⟨hM, rpow_neg_half_mul_sum_pair hbU0 g _ _ hM⟩

end Balaban.Inhabited
