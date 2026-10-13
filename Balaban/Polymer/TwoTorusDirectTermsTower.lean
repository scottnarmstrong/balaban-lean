/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDirectTerms
public import Balaban.Inhabited.SourceDirectTermsFromTower

/-!
# The direct terms of the zero class at the tower, explicitly, and the energy coefficient on two tori

The landed chain from the resummation step to the direct terms of the zero class at the tower
(`expansion_of_AE_rel`, …, `sourceDirectTerms_scale_fromTowerG_ray_rho`) now carries, as appended
conjuncts, the explicit form of the chosen witnesses: the terms of the expansion of one block are
`evTerm … FF` for a pair `(F₁, Sol)` of decoupled background and fluctuation maps with their
defining properties, and the direct terms of the zero class at zero source are the potential part
`-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ Ev_z(Y)(Θ, σ t x₀) dt`, with domains those of the potential
and of the source part.  This file turns these conjuncts into the hypotheses `hI𝒴`, `hIT` of
`gsumCoeff_e1_twoTorus_of_directTerms` and applies it.

## D2: the explicit form of the tower witness

* `sourceDirectTerms_explicit_fromTowerG`: for the general tower, the domains `𝒴` and terms `Tt` of
  the direct terms of the zero class (instances exist at every point of the slice) are explicit:
  `𝒴` is the union of the block and site domains, and at zero source `Tt` is the potential part
  with the localized block energy terms `evDec … (F₂ z) (Sol₂ z) (blockEnergyFun … z) ∅ 1 0`.
* `directTerms_explicit_fromTowerG`: at block scale `T.m₀ = 1`, every `DirectTerms` instance with
  these domains and terms satisfies `hI𝒴` and `hIT` in the form of
  `gsumCoeff_e1_twoTorus_of_directTerms`, with `cc = (β L^(k(d-2)))^(-1/2)`.

## D3: the energy coefficient on two tori

* `gsumCoeff_e1_twoTorus_fromTowerG`: at `T.m₀ = 1`, the energy coefficient of the zero class with
  the labels and activity of the tower witnesses agrees on two tori, for labels and blocks of a
  common box.  The remaining hypotheses are those of `gsumCoeff_e1_twoTorus_of_domainLabels` on the
  marks, the root and the data, and the radius `markedRad … c_ψ … < t` with `2 ρ_I ≤ c_ψ`.

Not done here: the observable coefficient on two tori, the assembly of `E0`, the specialization to
`T.step`/`T.m₀` in the root theorem, the last scales.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale Balaban.Inhabited
  Balaban.Inhabited.LevelStep MeasureTheory

section Explicit

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => (((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ))

/-- **D2: the direct terms of the zero class at the tower, in explicit form.**  For the general
tower `T`, the step `S = T.step k hk N₁ ν β p₁` and the slice `η = q/β`: there are the expanded
function `val`, the domains `𝒴` and the terms `Tt` of `sourceDirectTerms_scale_fromTowerG_ray_rho`
(a `DirectTerms` instance with these domains and terms exists at every point of the slice), and a
pair `(F₂, Sol₂)` of decoupled background and fluctuation maps per block with the defining
properties of `i4b_analytic` and `Dec2.i4a_analytic`, such that

* the domains are those of the potential part (the polymer domains of the blocks `z` with the local
  covers `X₁ = nbhdF T.m₀ (blockSite k z)`) and of the source part (the local covers of the sites);
* at zero source the term of a domain `Y` is the potential part
  `-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ evDec_z(Y)(Θ, σ t x₀) dt` with the localized block energy
  terms `evDec … (F₂ z) (Sol₂ z) (blockEnergyFun … z) ∅ 1 0` (marks `(1, 0)`, no mask).

The terms come from the appended conjuncts of the landed chain (`sourceDirectTerms_scale_fromTowerG_ray_rho`);
the marked form is `FFmarked_one_zero`. -/
theorem sourceDirectTerms_explicit_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁)
    (hN : 5 < N₁) (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β ρ : ℝ)
    (hρ : 0 < ρ) (hβρ : max 1 ρ ≤ β) (p₁ q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρ)
    (D : StepScaleDataG T k hk N₁ ν β p₁)
    (S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁) :
    ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ),
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
        ∃ I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
            (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))
            (2 * T.κdec - 1) Θ (physSΛEta S S.a₁ S.ν T.t (q / S.β))
            (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
            (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      ∃ (F₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
              (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N →
              ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)),
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₂ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₂ z p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2)) ∧
        𝒴 =
          (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
            polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
              (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
            (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
              polyDom S.G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)) ∧
        ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
          (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
          Tt Y x w σ (Θ, 0) = -((S.β : ℝ) : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
              if Y ∈ polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                  (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
                rayTerm (dl3 (evDec (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                  (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
                  (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
              else 0 := by
  obtain ⟨val, 𝒴, Tt, -, -, -, hI, -, -, -, h𝒴, F₂, Sol₂, hF₂, hSol₂, hTt⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_rho T k hk N₁ hLN hN ν hνpos hν β ρ hρ hβρ p₁ q hq0 hq
      D S hS hp
  refine ⟨val, 𝒴, Tt, hI, F₂, Sol₂, hF₂, hSol₂, h𝒴, fun Y x w σ Θ => ?_⟩
  rw [hTt]
  refine congrArg (fun t => -((S.β : ℝ) : ℂ) * t) (Finset.sum_congr rfl fun z _ => ?_)
  by_cases hY : Y ∈ polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
      (LocalCover.fam T.m₀ (LocalCover.blockSite k z))
  · rw [ite_eq_left hY, ite_eq_left hY]
    exact congrArg (fun FF => rayTerm (dl3 (evTerm
      (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) :
        Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' T.m₀
      (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) FF Y) w.1)
        taylorWeight x.1 σ Θ)
      (FFmarked_one_zero (a₁ := S.a₁) (ν := S.ν)
        (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) S.hG'
        ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
        (blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z)
        ∅).symm
  · rw [ite_eq_right hY, ite_eq_right hY]

/-- **D2 at `T.m₀ = 1`, in the form of `gsumCoeff_e1_twoTorus_of_directTerms`.**  For the tower
with block scale `T.m₀ = 1` and the step `T.step k hk N₁ ν β p₁`: there are the expanded function,
the domains `𝒴` and the terms `Tt` of the tower (a `DirectTerms` instance with these domains and
terms exists at every point of the slice `η = q/β`), and maps `(F₂, Sol₂)` with the defining
properties of the decoupled background and fluctuation maps, such that EVERY `DirectTerms` instance
`I` of the step with block scale `1`, domains `𝒴` and terms `Tt` satisfies the two hypotheses
`hI𝒴` and `hIT` of `gsumCoeff_e1_twoTorus_of_directTerms`, with `cc = (β L^(k(d-2)))^(-1/2)`. -/
theorem directTerms_explicit_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (hLN : L ^ T.m₀ ∣ N₁) (hN : 5 < N₁) (ν : ℝ) (hνpos : 0 < ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β ρ : ℝ) (hρ : 0 < ρ) (hβρ : max 1 ρ ≤ β)
    (p₁ q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρ) (D : StepScaleDataG T k hk N₁ ν β p₁)
    (hp : 0 < (SA).p₁) :
    ∃ (val : FA → FA → ℂ → ΛA → ℂ) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → ℂ → ΛA → ℂ),
      (∀ Θ ∈ physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β),
        ∃ I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
            ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SA).β))
            (2 * T.κdec - 1) Θ (physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β))
            (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
            (physAgΘ (SA)) (AgFDirPair (SA)),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      ∃ (F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ))
          (Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
            ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)),
        (∀ (z : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
            (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
            F₂ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₂ z p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1 p.2.1
              (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
              (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Small (HA) (Sol₂ z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (HA) (Sol₂ z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (HA) (Sol₂ z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
                (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2)) ∧
        ∀ {ρI Rσ εU a : ℝ} {Θ₀ : ΛA} {SΛ : Set ΛA} {XW : Set (FA × FA)}
          {val' : FA → FA → ℂ → ΛA → ℂ} {AgΘ : Set (CTorus d L N₁ T.m₁ (k + 1)) → ΛA → ΛA → Prop}
          {AgF : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → Prop}
          (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀ SΛ XW val' AgΘ AgF),
          I.𝒴 = 𝒴 → I.T = Tt →
          I.𝒴 =
            (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
              polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
              (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
                polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1)) ∧
          ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1))) (x w : FA) (σ : ℂ)
            (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
            I.T Y x w σ (Θ, 0) = -(((SA).β : ℝ) : ℂ) *
              ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
                if Y ∈ polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                    (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                  rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                    (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 ν (SA).hG' (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
                    (blockEnergyFun (GA) (HA) (compWeight L 1) ν k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
                else 0 := by
  have hd2 : 2 ≤ d := by have := T.hd; omega
  have hb : (SA).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN hd2 k T.m₁ _ hk ν β p₁ T.δ
  obtain ⟨val, 𝒴, Tt, hI, F₂, Sol₂, hF₂, hSol₂, h𝒴, hTt⟩ :=
    sourceDirectTerms_explicit_fromTowerG T k hk N₁ hLN hN ν hνpos hν β ρ hρ hβρ p₁ q hq0 hq D _
      rfl hp
  rw [hm₀] at hI h𝒴 hTt
  rw [hb] at hTt
  refine ⟨val, 𝒴, Tt, hI, F₂, Sol₂, hF₂, hSol₂, fun I h1 h2 => ⟨h1.trans h𝒴, fun Y x w σ Θ => ?_⟩⟩
  rw [h2]
  exact hTt Y x w σ Θ

end Explicit

section TwoTori

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "SB" => StepTowerG.step T k hk N₁' ν β p₁
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (k := k + 1)
  (ϱ := rhoSepG d L T.m₁) k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := T.m₁)
  (K := k + 1) (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "ΛB" => RawData d L (N₁' * L ^ T.m₁) (k + 1) N ×
  (CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => (((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ))
set_option hygiene false in
local notation "FB" => (((SB).U × Fin N → ℂ) × ((SB).U × Fin N → ℂ))

/-- **D3: the energy coefficient of the zero class on two tori, unconditional form.**  For the tower
`T` with block scale `T.m₀ = 1` and its steps `SA = T.step k hk N₁ ν β p₁`,
`SB = T.step k hk N₁' ν β p₁` on two tori (per-scale packages `D`, `D'`), with the hypotheses of
`gsumCoeff_e1_twoTorus_of_domainLabels` on the marks, the root and the data, and the radius
`markedRad … cψ (β L^(k(d-2)))^(-1/2) < t`: there are the expanded functions, domains and terms of
the direct terms of the zero class on both tori (`DirectTerms` instances with these domains and
terms exist at every point of the slices `η = q/β`), such that for EVERY pair of instances `I`,
`I'` with these domains and terms, relative families `hF`, `hF'` and `2 ρ_I ≤ c_ψ`, the energy
coefficients agree: `c′ θ′ (cubeMap '' Tb) = c θ Tb`.  This is
`gsumCoeff_e1_twoTorus_of_directTerms` with its hypotheses `hI𝒴`, `hIT` (and the primed ones)
discharged by `directTerms_explicit_fromTowerG` on both tori.  Only labels and blocks of a common box
are compared. -/
theorem gsumCoeff_e1_twoTorus_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁]
    [NeZero N₁'] (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (h5 : 5 < N₁) (h5' : 5 < N₁')
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β ρs : ℝ) (hρs : 0 < ρs)
    (hβρ : max 1 ρs ≤ β) (p₁ q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρs)
    (D : StepScaleDataG T k hk N₁ ν β p₁) (D' : StepScaleDataG T k hk N₁' ν β p₁)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (z : TA) {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) ν (k + 1) 1 T.t)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) ν (k + 1) 1 T.t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 →
      ‖u‖ * markedRad d L N k 1 T.κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t)
    (hGdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol ρ hp z T.t θ i u))
    (hL2 : 2 ≤ L) (hdom : ∀ b, ∀ Y ∈ e1DomG (SA) b, IsDj 1 (k + 1) Y)
    (hdom' : ∀ b, ∀ Y ∈ e1DomG (SB) b, IsDj 1 (k + 1) Y)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hrad : markedRad d L N k 1 T.κ cψ (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t)
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x) :
    ∃ (val : FA → FA → ℂ → ΛA → ℂ) (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
      (Tt : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → ℂ → ΛA → ℂ)
      (val' : FB → FB → ℂ → ΛB → ℂ) (𝒴' : Finset (Set (CTorus d L N₁' T.m₁ (k + 1))))
      (Tt' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → ℂ → ΛB → ℂ),
      (∀ Θ ∈ physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β),
        ∃ I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
            ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SA).β))
            (2 * T.κdec - 1) Θ (physSΛEta (SA) (SA).a₁ (SA).ν T.t (q / (SA).β))
            (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
            (physAgΘ (SA)) (AgFDirPair (SA)),
          I.𝒴 = 𝒴 ∧ I.T = Tt) ∧
      (∀ Θ ∈ physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β),
        ∃ I' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) p₁ 2
            ((SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / (SB).β))
            (2 * T.κdec - 1) Θ (physSΛEta (SB) (SB).a₁ (SB).ν T.t (q / (SB).β))
            (physXW (SB) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
              (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
            (physAgΘ (SB)) (AgFDirPair (SB)),
          I'.𝒴 = 𝒴' ∧ I'.T = Tt') ∧
      ∀ {ρI Rσ εU a κ0 KcL : ℝ} {Θ₀ : ΛA} {Θ₀' : ΛB} {SΛ : Set ΛA} {SΛ' : Set ΛB}
        {XW : Set (FA × FA)} {XW' : Set (FB × FB)} {valI : FA → FA → ℂ → ΛA → ℂ}
        {valI' : FB → FB → ℂ → ΛB → ℂ} {AgΘ : Set (CTorus d L N₁ T.m₁ (k + 1)) → ΛA → ΛA → Prop}
        {AgΘ' : Set (CTorus d L N₁' T.m₁ (k + 1)) → ΛB → ΛB → Prop}
        {AgF : Set (CTorus d L N₁ T.m₁ (k + 1)) → FA → FA → Prop}
        {AgF' : Set (CTorus d L N₁' T.m₁ (k + 1)) → FB → FB → Prop}
        (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀ SΛ XW valI AgΘ AgF)
        (I' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀' SΛ' XW' valI' AgΘ' AgF'),
        I.𝒴 = 𝒴 → I.T = Tt → I'.𝒴 = 𝒴' → I'.T = Tt' →
        ∀ {cJ cJ' : ℂ} {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
          (hF : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I V)
          (hF' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' V')
          (hρI : 0 < ρI) (hRσ : 1 < Rσ) (hεU : 0 ≤ εU) (hκ0 : aEnt d L + 2 ≤ κ0)
          (hKc : K0 d L κ0 ≤ KcL),
          ((θ.1, 0) : physParam N (SA)) ∈ V → ((θ'.1, 0) : physParam N (SB)) ∈ V' →
          2 * ρI ≤ cψ →
        gsumCoeff ((SB).blockSplit 1 hp').μ
            (commonLabels (thickLabels I'.𝒴 I'.dom) hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
            (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
                hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
              hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom'
              (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
            (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB)) (bc z) i')
            (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc z) T.t θ' i' u Φ') (Tb.image (σc)) =
          gsumCoeff ((SA).blockSplit 1 hp).μ
            (commonLabels (thickLabels I.𝒴 I.dom) hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
            (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
                hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
              hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom
              (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
            (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
            (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z T.t θ i u Φ) Tb := by
  have hLN : L ^ T.m₀ ∣ N₁ := by rw [hm₀]; exact hN
  have hLN' : L ^ T.m₀ ∣ N₁' := by rw [hm₀]; exact hN'
  have hm₁ : 1 ≤ T.m₁ := by have := T.m₁_four; omega
  obtain ⟨val, 𝒴, Tt, hI, F₂, Sol₂, hF₂, hSol₂, hE⟩ :=
    directTerms_explicit_fromTowerG T hm₀ k hk N₁ hLN h5 ν hνpos hν β ρs hρs hβρ p₁ q hq0 hq D hp
  obtain ⟨val', 𝒴', Tt', hI', F₂', Sol₂', hF₂', hSol₂', hE'⟩ :=
    directTerms_explicit_fromTowerG T hm₀ k hk N₁' hLN' h5' ν hνpos hν β ρs hρs hβρ p₁ q hq0 hq D'
      hp'
  refine ⟨val, 𝒴, Tt, val', 𝒴', Tt', hI, hI', ?_⟩
  intro ρI Rσ εU a κ0 KcL Θ₀ Θ₀' SΛ SΛ' XW XW' valI valI' AgΘ AgΘ' AgF AgF' I I' h1 h2 h1' h2'
    cJ cJ' V V' hF hF' hρI hRσ hεU hκ0 hKc hV hV' hρc
  obtain ⟨hI𝒴, hIT⟩ := hE I h1 h2
  obtain ⟨hI𝒴', hIT'⟩ := hE' I' h1' h2'
  exact gsumCoeff_e1_twoTorus_of_directTerms T.hN hk ν β p₁ T.δ D.core D'.core
    (SA).hG' (SB).hG' T.large_block T.dom_margin T.coer_margin T.δc_small hF₁ hF₁' hSol hSol'
    hN hN' hm₁ z hz hrc hroot hn hn' θ θ' hθ hθ' hraw hρ hp hp' hum hGdep hL2 hdom hdom'
    (Lb := Unit) (Lb' := Unit) I I' hF hF' hρI hRσ hεU hκ0 hKc hV hV' _ hcψ hρc hrad hF₂ hF₂'
    hSol₂ hSol₂' hI𝒴 hI𝒴' hIT hIT' Tb hTb

end TwoTori

end Balaban.Polymer.TwoTorusStep
