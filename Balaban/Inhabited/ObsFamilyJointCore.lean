/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffFamily
public import Balaban.Inhabited.ObsCoeffFibreValue
public import Balaban.Inhabited.Thm31bFromTower
public import Balaban.Inhabited.ObsCoeffLocal
public import Balaban.Inhabited.ObsCoeffExactSites
public import Balaban.Inhabited.OffFibreM0CoeffSum

/-!
# The coefficient family of the observable with the formulas of its activity and its terms

`obsFamily_full_fromTowerG_rho_core` is `obsFamily_full_fromTowerG_rho` together with the explicit
formulas that the latter does not state: after the labels and the activity `A` are chosen, the
labels correspond to the domains of the local covers of the blocks and of the sites, and `A` has
its explicit values at the zero source (the potential part of the direct terms, for decoupled pairs
per block) and at a nonzero source (the potential part plus the source part, for decoupled pairs per
site); for every site `(y, i)` the family `Ev` is `evTerm … (siteFun … y i …)` for a decoupled pair.
The formulas are those of `obsTiltLabels_local_fromTowerG_rho` and `obsEv_fromTower_rawYG`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- **The observable coefficient family at the tower with the formulas of the activity and of the
terms.**  The statement of `obsFamily_full_fromTowerG_rho` with three further clauses: after the
labels `Lab` and the activity `A` are chosen,
* the labels correspond (`ys`) to the domains of the local covers of the blocks and of the sites,
  and at a parameter `(e.1, 0)` with `e ∈ physVqRho …`, `‖σ‖ < 2`, the activity of a label is the
  potential part `-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evTerm_z(Y)) ω ψ̂ σ e.1` for a decoupled pair
  `(F₁, Sol)` per block;
* at a parameter `e`, the activity is its value at `(e.1, 0)` plus the source part
  `∑_s [Y ∈ polyDom_s] e.2 s · dirTerm (Ev₃ s Y) …` with `Ev₃ s = evTerm … (siteFun … s …)` for a
  decoupled pair `(F₃ s, Sol₃ s)` per site;
* for every site `(y, i)` the chosen family is `Ev = evTerm … (siteFun … y i …)` for a decoupled
  pair `(F₁, Sol)`. -/
theorem obsFamily_full_fromTowerG_rho_core {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
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
          (K0 d L T.κ0 + 1)),
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
        ∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
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
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)) ∧
        ObsRayIdentity S T.m₀ hp
          (fun ψh => svec (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
            (flFieldOne S.G' (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.BG₂ T.κ 1 ν D
              (hatLift S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) D ψh)) y i) Ev D
          (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))) ∧
      ((∀ m : ObsMarkIdx S, Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (fun _ : Unit => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) m)
        (fun _ _ _ => blockMarkC S T.m₀ hp m.1 m.2) (2 * T.κdec - 1)
        (fun _ => S.p₁ * Real.exp ((2 * T.κdec - 1) * (obsLab (Lab.sum Lab) hdj).dl
          (obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)))
        (physVqRho S S.a₁ S.ν T.t ρ q) (ball (0 : ℂ) (3 / 2)) (physCarrier S T.m₀ hp))) ∧
      Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
        (fun θ t => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
          (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
            (rootCube (m₀ := T.m₀) (blockIndex y))))
        (obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t)) (2 * T.κdec - 1)
        (fun _ => 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2)
        (physVqRho S S.a₁ S.ν T.t ρ q) (ball (0 : ℂ) (3 / 2)) (physCarrier S T.m₀ hp))) ∧
      (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
        Set.univ),
      ((∀ (m : ObsMarkIdx S) (S' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
        (K := k + 1) T.m₀ (k + 1) Set.univ)),
      AnalyticOnNhd ℂ (fun θ => markIntTerm (S.blockSplit T.m₀ hp).μ ((fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ)
        (obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (blockMarkC S T.m₀ hp m.1 m.2) S')
        (physVqRho S S.a₁ S.ν T.t ρ q)) ∧
    AnalyticOnNhd ℂ (fun θ => kernelMarkSum
      (fun m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
      (fun m S' => markIntTerm (S.blockSplit T.m₀ hp).μ ((fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ) (obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
        (blockMarkC S T.m₀ hp m.1 m.2) S') T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
    AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit T.m₀ hp).μ (obsLab (Lab.sum Lab) hdj)
      (fun t => (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ) θ t 1)
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))))
      (obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) T')
      (physVqRho S S.a₁ S.ν T.t ρ q) ∧
    AnalyticOnNhd ℂ (fun θ => obsCoeffParam (S.blockSplit T.m₀ hp).μ (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
        (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T')
      (physVqRho S S.a₁ S.ν T.t ρ q) ∧
      (∀ θ ∈ (physVqRho S S.a₁ S.ν T.t ρ q),
        ‖obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
          ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
            (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
      (∀ θ ∈ (physVqRho S S.a₁ S.ν T.t ρ q),
        obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
        rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ (physVqRho S S.a₁ S.ν T.t ρ q), ∀ θ' ∈ (physVqRho S S.a₁ S.ν T.t ρ q),
        agreeOn (thickSet S.G' (sitesOf T')) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) → (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) →
        obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' =
        obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ' T') ∧
      (∀ θ ∈ (physVqRho S S.a₁ S.ν T.t ρ q), ∀ θ' ∈ (physVqRho S S.a₁ S.ν T.t ρ q),
        physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
          physRestrict (sitesOf T') (physIncl N S θ') →
        obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' =
        obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ' T'))) ∧
      (∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x', ∑ i', ‖g x' i'‖ < q →
          (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
            ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N) T.κ0_ent hεH.le hdj (le_refl _)
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ)
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T') ∧
      ∃ Jr : S.JointRep T.t (2 * p₁),
        (∀ (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N q →
            ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
              Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                  (rawOf D, Balaban.Fluctuation.yhat x) +
                Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g
                  (rawOf D, (t : ℂ) • Balaban.Fluctuation.yhat x) =
                ∑ w, (physAct A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g)
                  (t : ℂ)).H w ((S.blockSplit T.m₀ hp).restr x)) ∧
        ∀ (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ g : Fld d L N₁ T.m₁ (k + 1) N, g ∈ l1BallRho d L N₁ T.m₁ (k + 1) N q →
            ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
              S.avgJ (Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)))
                (Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g)
                (Jr.McJ (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i) (rawOf D) =
              ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T',
                obsCoeffParam (S.blockSplit T.m₀ hp).μ
                  (fun θ t σ => tiltActObs A (show L ^ T.m₀ ∣ N₁ from h3N)
                    T.κ0_ent hεH.le hdj (le_refl _)
                    (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR
                    (ball (0 : ℂ) (3 / 2)) θ t σ)
                  (fun m => obsY1 T.m₀ S (Lb ⊕ Lb)
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
                  (fun m => blockMarkC S T.m₀ hp m.1 m.2)
                  (fun θ m T'' => obsHker
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (fun Y => hatCoeff (Ev Y)
                      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec S m)) T.m₀ T'')
                  (obsRemLab
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (fun Y => Sum.inl (Sum.inr Y))
                    (obsY0 T.m₀ (Lb ⊕ Lb)
                      (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                      (rootCube (m₀ := T.m₀) (blockIndex y))))
                  (fun θ => obsGrFam S T.m₀ hp Ev
                    (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
                    (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ)
                  ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T'
    := by
  classical
  have hK0 := T.marks_K0_pos
  have hc1 : 0 < c1 d L := by linarith [one_le_c1 d L]
  have hKo : 0 < (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0 := by linarith
  have hΘ : 0 < stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ' :=
    div_pos one_pos (mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hKo 3)) hc1)
      (Real.exp_pos _))
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, hmain⟩ := obsTiltLabels_local_fromTowerG_rho T hA p hCR hs0 hs hΘ ρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, fun k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq1
    Dsc S hS hp => ?_⟩
  obtain ⟨Lb, instLb, Lab, εH, hεH, A, hAloc, hAlocExact, hεb, hae, hrest, hlab, hRaw⟩ := hmain k hk N₁ h3N hN ν hνpos hν β hβ p₁
    hp0 hp₁ q hq0 hq1 Dsc S hS hp (Kc := K0 d L T.κ0 + 1) (by linarith)
  refine ⟨Lb, instLb, Lab, εH, hεH, A, hεb, hlab, hRaw.2, fun y i hdj => ?_⟩
  obtain ⟨-, -, A3, A4, A5⟩ := hrest hdj (le_refl _)
  obtain ⟨h1, hεΘ, hR, -⟩ := A5 0 (by simpa using hq0)
  refine ⟨hR, h1, hεΘ, ?_⟩
  have hhol := (A4 _ hR h1).1
  have hcont := (A4 _ hR h1).2
  have hσ := fun e he => (A3 _ hR h1 e he).2.1
  have hzero := fun e he => (A3 _ hR h1 e he).2.2
  obtain ⟨⟨JrR, hRawAct⟩, -⟩ := hRaw
  subst hS
  let S := T.step k hk N₁ ν β p₁
  obtain ⟨Ev, ha, hdRaw, hb, hD, hEvx⟩ := obsEv_fromTower_rawYG T k hk N₁ ν β p₁ hN hνpos hν
    Dsc (ϱ := rhoSepG d L T.m₁) rfl (S := T.step k hk N₁ ν β p₁) rfl hp y i (Lab.sum Lab)
  have hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
      ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
      AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u' := by
    intro Y u hu u' hu' h
    exact hdRaw Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1) h.2
  have fam := obsFamilies_of_EvG_rho T k hk N₁ ν β p₁ Dsc _ rfl hp y h3N Lab hεH A
    hdj (le_refl _) _ hR rfl hνpos hν hhol hcont Ev ha hb
  have hT' := fun T' => obsCoeffParam_analytic_of_EvG_rho T k hk N₁ ν β p₁ Dsc _ rfl hp y
    h3N Lab hεH A hdj (le_refl _) _ hR rfl hνpos hν h1 (le_refl _) hhol hcont hεΘ
    Ev ha hd hb T'
  refine ⟨Ev, hEvx, ha, hd, hb, hD, fam, ⟨fun T' => ⟨(hT' T').1, (hT' T').2.1, (hT' T').2.2.1,
    (hT' T').2.2.2, fun θ hθ => ?_, fun θ hθ => ?_, fun θ hθ θ' hθ' hr hg => ?_,
    fun θ hθ θ' hθ' hπ => ?_⟩, ?_, ⟨JrR, hRawAct, ?_⟩⟩⟩
  · exact obsCoeffParam_bound_of_EvG_rho T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab hεH A hdj (le_refl _) _
      hR h1 (le_refl _) hσ hzero hεΘ Ev ha hd hb (fun D hD' => (hD D hD').1) θ hθ T'
  · exact obsCoeffParam_support_of_EvG_rho T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab hεH A hdj (le_refl _) _
      hR h1 (le_refl _) hεΘ Ev ha hd hb (fun D hD' => (hD D hD').1) θ hθ T'
  · exact obsCoeffParam_local_of_EvG_rho T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab hεH A hdj (le_refl _) _
      hR hAloc Ev hd hθ hθ' T' hr hg
  · exact obsCoeffParam_local_of_Ev_physRestrictG_rho T k hk N₁ ν β p₁ Dsc S rfl hp y h3N Lab
      hεH A hdj (le_refl _) _ hR Ev hAlocExact hdRaw hθ hθ' T' hπ
  · intro D hDh hDx g hg
    have hN3 : L ^ T.m₀ ∣ N₁ := h3N
    have hDx' : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D := hDx
    obtain ⟨hhalf, hid⟩ := hD D hDx'
    have hmemθ : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N (T.step k hk N₁ ν β p₁).G'), g) ∈
        physVqRho (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t ρ q :=
      ⟨⟨⟨D, hDx, rfl⟩, lt_of_lt_of_le hg hq1⟩, hg⟩
    let S := T.step k hk N₁ ν β p₁
    obtain ⟨hholt, hholσ, hzero⟩ := A3 (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR h1 _ hmemθ
    have hν0 := hνpos.le
    obtain ⟨R0⟩ := Dsc.ray
    have hr0 := Dsc.r_pos
    have hcψ0 := Dsc.cψ_pos
    have hC := Dsc.core
    have hHB := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
    have hmem := compWeight_one_mem T.hL hk
    have hCs : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ :=
      covSupConstC_nonneg (by have := T.hd; omega) (by have := T.hL; omega) (by linarith [hmem.1]) T.κ
    have hbU : 0 ≤ S.betaU := R0.betaU_pos.le
    have hβ3 : 3 ≤ β := le_trans h3 hβ
    have hpc : 2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
      have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp
      linarith [Dsc.ray_margin]
    have hδp : Real.sqrt (N : ℝ) *
        (S.betaU ^ (-(1 / 2 : ℝ)) *
          (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ * (2 * p₁))) < T.t := by
      refine lt_of_le_of_lt ?_ Dsc.fl_radius
      rw [S.norm_betaU_rpow (show 0 ≤ β by linarith)]
      have hb := Real.rpow_nonneg hbU (-(1 / 2 : ℝ))
      have hs := Real.sqrt_nonneg (N : ℝ)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpc.le hCs) hb) hs
    obtain ⟨Jr⟩ := S.nonempty_jointRep (pp := 2 * p₁) hC T.large_block T.dom_margin T.coer_margin
      T.δc_small one_pos T.c7_cap (R := 2) (by norm_num) T.bg1_cap (by
        show 0 ≤ β
        linarith) (by linarith) hδp
    have hCh : 0 ≤ cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) :=
      div_nonneg (cK2'_famConst_mul_t_posG T).le hcψ0.le
    have hκ0h : T.κ0 ≤ 2 * T.κdec := by
      have := T.marks_κ0_le_κH; linarith
    have hεpos : 0 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH :=
      mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
    obtain ⟨I, hI⟩ := obsRecord_of_halves S T.m₀ hp (Lab.sum Lab) _ hdj hN3 Ev D _ _ hCh T.κ0_ent
      hκ0h hhalf hid
      (fun r x => (S.withDatum D hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) 1 x +
        (S.withDatum D hDh).WtwoC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g r x)
      (ball (0 : ℂ) (3 / 2)) h1 isOpen_ball (fun r hr => seg_mem_ball_three_halves r hr)
      subset_rfl
      (fun t σ => tiltActObs A hN3 T.κ0_ent hεH.le hdj
        (Kobs := (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) le_rfl
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) t σ)
      hholt (fun r hr => hholσ _ (seg_mem_ball_three_halves r hr)) (fun r _ => hzero _)
      (fun r hr => by
        filter_upwards [hae] with x hx
        exact (hx D hDh hDx' g hg r hr hdj (Kobs := (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) +
          K0 d L T.κ0 + K0 d L T.κ0) le_rfl).2 _ hR h1)
      (by linarith) hεpos T.marks_hκ' T.marks_κ0_le_κ' T.marks_hκ hεΘ
    let hI' := ObsMarks.toConsumer (Jr.withDatum D hDh) hC one_pos hHB T.c7_cap (R := 2) le_rfl
      T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block T.dom_margin T.coer_margin
      T.δc_small hcψ0.le Dsc.fl_radius hp Dsc.p_lt hpc hDx g y i (S.blockSplit T.m₀ hp) I
    have hval := (thm31b_coeff hI' (κb := min hI'.κh hI'.κ' - hI'.κ0 - 1) le_rfl).1
    have hM : (S.withDatum D hDh).M0C (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) g y i =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T', obsCoeff hI' T' := by
      rw [← hval]; rfl
    rw [hM]
    congr 1
    refine Finset.sum_congr rfl fun T' _ => ?_
    have := (obsCoeffParam_fibre S T.m₀ hp Ev _ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) _ _ _ D
      (θ := ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g)) rfl ⟨D, hDx', rfl⟩ T').trans
      (hI T').symm
    exact this.symm
  · intro D hDx g hg
    have hN3 : L ^ T.m₀ ∣ N₁ := h3N
    have hDx' : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D := hDx
    obtain ⟨hhalf, hid⟩ := hD D hDx'
    have hmemθ : ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N (T.step k hk N₁ ν β p₁).G'), g) ∈
        physVqRho (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t ρ q :=
      ⟨⟨⟨D, hDx, rfl⟩, lt_of_lt_of_le hg hq1⟩, hg⟩
    let S := T.step k hk N₁ ν β p₁
    obtain ⟨hholt, hholσ, hzero⟩ := A3 (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR h1 _ hmemθ
    have hν0 := hνpos.le
    obtain ⟨R0⟩ := Dsc.ray
    have hr0 := Dsc.r_pos
    have hcψ0 := Dsc.cψ_pos
    have hC := Dsc.core
    have hHB := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hν0 hν
    have hKo : 0 < (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0 := by
      linarith
    have hpc : 2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
      have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos hr0 hp
      linarith [Dsc.ray_margin]
    have hCh : 0 ≤ cK2' d L N (famConst d L T.BG₂ T.κ) * T.t /
        lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) :=
      div_nonneg (cK2'_famConst_mul_t_posG T).le hcψ0.le
    have hκ0h : T.κ0 ≤ 2 * T.κdec := by
      have := T.marks_κ0_le_κH; linarith
    have hεpos : 0 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εH + εH) εH :=
      mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
    obtain ⟨I, hI, hsumI⟩ := JrR.obsRecord_raw_M0_of_activity (S.withDatumH D) hC one_pos hHB
      T.c7_cap (R := 2) le_rfl T.bg1_cap T.t_cap T.bg0_cap T.cK2_cap T.cK2'_cap T.large_block
      T.dom_margin T.coer_margin T.δc_small hcψ0.le Dsc.fl_radius hpc hDx hp Dsc.p_lt hN3
      (Lab.sum Lab) _ hdj Ev g y i _ hCh T.κ0_ent hκ0h hhalf hid
      (ball (0 : ℂ) (3 / 2)) h1 isOpen_ball (fun r hr => seg_mem_ball_three_halves r hr)
      subset_rfl
      (fun t σ => tiltActObs A hN3 T.κ0_ent hεH.le hdj
        (Kobs := (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) le_rfl
        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
        ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) t σ)
      hholt (fun r hr => hholσ _ (seg_mem_ball_three_halves r hr)) (fun r _ => hzero _)
      (fun r hr => by
        filter_upwards [hRawAct D hDx g hg r hr] with x hx
        rw [tiltActObs_total_one A hN3 T.κ0_ent hεH.le hdj
          (Kobs := (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) le_rfl
          hR h1 (seg_mem_ball_three_halves r hr)]
        exact hx)
      (by linarith) hεpos T.marks_hκ' T.marks_κ0_le_κ' T.marks_hκ hεΘ
    refine hsumI.symm.trans ?_
    congr 1
    refine Finset.sum_congr rfl fun T' _ => ?_
    have := (obsCoeffParam_fibre S T.m₀ hp Ev _ (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) _ _ _ D
      (θ := ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g)) rfl ⟨D, hDx', rfl⟩ T').trans
      (hI T').symm
    exact this.symm

end Balaban.Inhabited
