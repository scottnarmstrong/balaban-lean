/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsSource

/-!
# The coefficient of the observable on two tori, from the tower, at nonzero source

`obsCoeffParam_twoTorus_fromTowerG_source` is `obsCoeffParam_twoTorus_fromTowerG` at parameters of
arbitrary source.  Besides the exports used there, it uses the explicit source part of the direct
terms of the zero class (the appended conjunct of `sourceDirectTerms_scale_fromTowerG_ray_rho`): the
terms `Ev₃_s` of the expansions of the site functionals `δφ(s)`, `s = (x, i)`, in the explicit form
`evTerm … (siteFun …)` for decoupled pairs `(F₃, Sol₃)` and analytic on the data of the chart, and
the decomposition `hAs` of the activity family `A` at a parameter `e` of the chart into the
activity at `(e.1, 0)` and the source part
`∑_s e.2(s) [Y ∈ polyDom_s] dirTerm (Ev₃_s Y) (fun _ => 1) ψ̂ ψ̂ σ e.1` at the domain `Y` of the label
(the activity of a label at `e` is the term of its domain in the direct terms at `(e.1, e.2/β)`;
`β · (e.2/β) = e.2`).  The sources of the two parameters agree on the box of radius `R`.

Not covered: `hAs` is not yet exported by `obsTiltLabels_local_fromTowerG`; it is a hypothesis in the
form of the conjunct to be appended there (see the report).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale Balaban.Inhabited
  Balaban.Inhabited.LevelStep MeasureTheory Metric

section Tower

set_option hygiene false in
local notation "SA" => StepTowerG.step T k hk N₁ ν β p₁
set_option hygiene false in
local notation "SB" => StepTowerG.step T k hk N₁' ν β p₁
set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ T.m₁) * L ^ (k + 1)) ((N₁' * L ^ T.m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ T.m₁) * L ^ (k + 1 - k))
  ((N₁' * L ^ T.m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := T.m₁)
  (K := k + 1) (m₀ := T.m₀) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "𝒴A" => obsDomains (SA) (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)
set_option hygiene false in
local notation "𝒴B" => obsDomains (SB) (LocalCover.nbhdF T.m₀ (bm y)) T.m₀ k
  (LocalCover.fam T.m₀ (bm y))

/-- **The coefficient of the observable on two tori, from the tower, at nonzero source.**  The
statement of `obsCoeffParam_twoTorus_fromTowerG` for parameters `θ`, `θ'` of arbitrary source,
with sources agreeing on the box of radius `R` (`hsrc`), and the explicit source part of the
activities (`hAs`, `hAs'`, with the terms `Ev₃`, `Ev₃'` of the source sites in the form exported by
`sourceDirectTerms_scale_fromTowerG_ray_rho`; `hanEv₃` their analyticity).  Then
`obsCoeffParam … θ' (cubeMap '' Tc) = obsCoeffParam … θ Tc`. -/
theorem obsCoeffParam_twoTorus_fromTowerG_source {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁] [NeZero N₁']
    (hN : L ^ T.m₀ ∣ N₁) (hN' : L ^ T.m₀ ∣ N₁') {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) (D' : StepScaleDataG T k hk N₁' ν β p₁) {R : ℕ}
    (hn : 4 * R + 12 * L ^ (k + 1 + T.m₁) + 7 * L ^ (k + 1) + 5 <
      (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + T.m₁) + 7 * L ^ (k + 1) + 5 <
      (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (hnS : 2 * (R + (3 * L ^ (k + 1 + T.m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + T.m₁)) +
      5 * (L * cellSide L 0 T.m₁ (k + 1)) < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hnS' : 2 * (R + (3 * L ^ (k + 1 + T.m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + T.m₁)) +
      5 * (L * cellSide L 0 T.m₁ (k + 1)) < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L T.m₀ T.m₁ (k + 1)) < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L T.m₀ T.m₁ (k + 1)) < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (y : CTorus d L N₁ T.m₁ (k + 1)) (iy : Fin N)
    (hX₁R : ∀ x ∈ LocalCover.nbhd T.m₀ y, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    {cψ : ℝ} (hcψ : 0 < cψ) (hq : p₁ / cψ ≤ 1 / 4) (hρ : 2 * p₁ ≤ cψ)
    (hrad : markedRad d L N k 1 T.κ cψ
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < T.t)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    -- the terms of the site functionals (`obsEv_fromTower_rawYG`)
    {Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
      RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts (SA).G' × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' T.m₁ (k + 1)) →
      RawData d L (N₁' * L ^ T.m₁) (k + 1) N × (unitPts (SB).G' × Fin N → ℂ) → ℂ}
    (hdEv : ∀ Y, ∀ u ∈ XiCRaw (SA).G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts (SA).G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw (SA).G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts (SA).G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt (SA).hG' y, i) = u'.2 (unitPt (SA).hG' y, i)) →
      Ev Y u = Ev Y u')
    {F₁ : DecParams (SA).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((SA).G'.Ω 1 × Fin N → ℂ) × ((SA).G'.Ω 1 → ℂ)}
    {Sol : Dec2.DecParams (coverOf (SA).G') × Edat (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (SA).G') (D : BgData (SA).G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (SA).G' (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (SA).G'.Ω 1 × Fin N → ℂ)
        (α : (SA).G'.Ω 1 → ℂ), IsDecBg (SA).G' (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hSol : ∀ p : Dec2.DecParams (coverOf (SA).G') × Edat (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol p).1 = dphi (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf (SA).G') (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1) p.2.2.1 p.2.1
          (pertSource (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (SA).G') (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (SA).G') (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hEv : Ev = evTerm (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) (SA).G' T.m₀
      (X1 (SA).G' T.m₀ k (LocalCover.fam T.m₀ y))
      (fun u s => siteFun (SA).G' (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) y iy
        (F₁ (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
        (Sol (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
          flEdat (SA).G' (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₁ (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
            u.1.1 (hatPsiF (SA).G' 1 ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
              (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, hatPsiF (SA).G' 1 ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁
          (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)))
    {F₁' : DecParams (SB).G' × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
      ((SB).G'.Ω 1 × Fin N → ℂ) × ((SB).G'.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (SB).G') × Edat (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N → ((lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    (hF₁' : ∀ (s : DecParams (SB).G') (D : BgData (SB).G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (SB).G' (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (SB).G'.Ω 1 × Fin N → ℂ)
        (α : (SB).G'.Ω 1 → ℂ), IsDecBg (SB).G' (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (SB).G') × Edat (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol' p).1 = dphi (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf (SB).G') (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1) p.2.2.1 p.2.1
          (pertSource (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (SB).G') (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol' p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol' p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol' p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (SB).G') (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (hEv' : Ev' = evTerm (fun i : ParIdx (SB).G' (↑(LocalCover.nbhdF T.m₀ (bm y)) : Set (CTorus d L N₁' T.m₁ (k + 1))) => i.1.1) (SB).G' T.m₀
      (X1 (SB).G' T.m₀ k (LocalCover.fam T.m₀ (bm y)))
      (fun u s => siteFun (SB).G' (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (bm y) iy
        (F₁' (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (bm y)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s, u.1))
        (Sol' (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (bm y)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s,
          flEdat (SB).G' (lvLowG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (F₁' (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (bm y)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s, u.1))
            u.1.1 (hatPsiF (SB).G' 1 ν (SB).hG' (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁'
              (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (bm y)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, hatPsiF (SB).G' 1 ν (SB).hG' (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁'
          (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (bm y)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s) u.1 u.2)))
    -- the labels and the activities (`obsTiltLabels_local_fromTowerG`)
    {Lb Lb' : Type} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ Lb')
    {εH εH' Kc Kc' : ℝ}
    (A : physParam N (SA) → ℂ →
      LabelAct Lab ((SA).blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
    (A' : physParam N (SB) → ℂ →
      LabelAct Lab' ((SB).blockSplit T.m₀ hp').Ωb εH' (2 * T.κdec - 1) T.κ0 Kc')
    {q : ℝ}
    {𝒴v : Finset (Set (CTorus d L N₁ T.m₁ (k + 1)))} (ys : Lb ≃ {Y // Y ∈ 𝒴v})
    (hys : ∀ l, Lab.ysite l = (ys l).1)
    (h𝒴v : 𝒴v = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
              polyDom (SA).G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
            (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
              polyDom (SA).G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)))
    {F₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams (SA).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → ((SA).G'.Ω 1 × Fin N → ℂ) × ((SA).G'.Ω 1 → ℂ)}
    {Sol₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf (SA).G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    (hF₂ : ∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams (SA).G') (D : BgData (SA).G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC (SA).G' (bgC0 d L N) (c7 d L N T.BG T.κ) (SA).ν D → ∀ (φ : (SA).G'.Ω 1 × Fin N → ℂ)
            (α : (SA).G'.Ω 1 → ℂ), IsDecBg (SA).G' (compWeight L (SA).a₁) (SA).ν (rho4 d L N T.BG T.κ) s D φ α →
            F₂ z (s, rawOf D) = (φ, α))
    (hSol₂ : ∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf (SA).G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₂ z p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf (SA).G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Dec2.DecFixed (coverOf (SA).G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf (SA).G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2))
    (hAx : ∀ e ∈ physVq (SA) (SA).a₁ (SA).ν T.t q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb)
          (Φ : ∀ b, ((SA).blockSplit T.m₀ hp).Ωb b),
          (A ((e.1, 0) : physParam N (SA)) σ).H l Φ = -((SA).β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Lab.ysite l ∈ polyDom (SA).G'
                (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                (SA).G' T.m₀ (X1 (SA).G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν k z
                  (F₂ z (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol₂ z (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                    flEdat (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂ z (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                        (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                    (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) (Lab.ysite l))
                ((SA).hatOf T.m₀ p₁ hp Φ)) taylorWeight ((SA).hatOf T.m₀ p₁ hp Φ) σ
                (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
            else 0)
    {𝒴v' : Finset (Set (CTorus d L N₁' T.m₁ (k + 1)))} (ys' : Lb' ≃ {Y // Y ∈ 𝒴v'})
    (hys' : ∀ l, Lab'.ysite l = (ys' l).1)
    (h𝒴v' : 𝒴v' = (Finset.univ.biUnion fun z : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
              polyDom (SB).G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
            (Finset.univ.biUnion fun s : CTorus d L N₁' T.m₁ (k + 1) × Fin N =>
              polyDom (SB).G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)))
    {F₂' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams (SB).G' × RawData d L (N₁' * L ^ T.m₁) (k + 1) N → ((SB).G'.Ω 1 × Fin N → ℂ) × ((SB).G'.Ω 1 → ℂ)}
    {Sol₂' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf (SB).G') × Edat (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    (hF₂' : ∀ (z : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams (SB).G') (D : BgData (SB).G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC (SB).G' (bgC0 d L N) (c7 d L N T.BG T.κ) (SB).ν D → ∀ (φ : (SB).G'.Ω 1 × Fin N → ℂ)
            (α : (SB).G'.Ω 1 → ℂ), IsDecBg (SB).G' (compWeight L (SB).a₁) (SB).ν (rho4 d L N T.BG T.κ) s D φ α →
            F₂' z (s, rawOf D) = (φ, α))
    (hSol₂' : ∀ (z : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf (SB).G') × Edat (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₂' z p).1 = dphi (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf (SB).G') (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
            Dec2.DecFixed (coverOf (SB).G') (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
            Small (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol₂' z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol₂' z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol₂' z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf (SB).G') (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' z p).2))
    (hAx' : ∀ e ∈ physVq (SB) (SB).a₁ (SB).ν T.t q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb')
          (Φ : ∀ b, ((SB).blockSplit T.m₀ hp).Ωb b),
          (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ = -((SB).β : ℂ) *
            ∑ z : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Lab'.ysite l ∈ polyDom (SB).G'
                (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx (SB).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁' T.m₁ (k + 1))) => i.1.1)
                (SB).G' T.m₀ (X1 (SB).G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun (SB).G' (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν k z
                  (F₂' z (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s, u.1))
                  (Sol₂' z (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s,
                    flEdat (SB).G' (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (F₂' z (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF (SB).G' (SB).a₁ (SB).ν (SB).hG' (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                        (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF (SB).G' (SB).a₁ (SB).ν (SB).hG' (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                    (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁' T.m₁ (k + 1))) s) u.1 u.2)) (Lab'.ysite l))
                ((SB).hatOf T.m₀ p₁ hp Φ)) taylorWeight ((SB).hatOf T.m₀ p₁ hp Φ) σ
                (e.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N)
            else 0)
    {F₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N →
      DecParams (SA).G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
        ((SA).G'.Ω 1 × Fin N → ℂ) × ((SA).G'.Ω 1 → ℂ)}
    {Sol₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (SA).G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    {Ev₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N → Set (CTorus d L N₁ T.m₁ (k + 1)) →
      RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts (SA).G' × Fin N → ℂ) → ℂ}
    (hF₃ : ∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N) (s : DecParams (SA).G')
      (D : BgData (SA).G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (SA).G' (bgC0 d L N) (c7 d L N T.BG T.κ) (SA).ν D → ∀ (φ : (SA).G'.Ω 1 × Fin N → ℂ)
        (α : (SA).G'.Ω 1 → ℂ), IsDecBg (SA).G' (compWeight L (SA).a₁) (SA).ν (rho4 d L N T.BG T.κ) s D φ α →
        F₃ a (s, rawOf D) = (φ, α))
    (hSol₃ : ∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (SA).G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol₃ a p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf (SA).G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Dec2.DecFixed (coverOf (SA).G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
        Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₃ a p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₃ a p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₃ a p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (SA).G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ a p).2))
    (hEv₃ : ∀ a : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Ev₃ a =
      evTerm (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) =>
        i.1.1) (SA).G' T.m₀ (X1 (SA).G' T.m₀ k (LocalCover.fam T.m₀ a.1))
        (fun u t => siteFun (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) a.1 a.2
          (F₃ a (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t,
            u.1))
          (Sol₃ a (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t,
            flEdat (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
              (F₃ a (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃ a)
                (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃ a)
            (extParams (SA).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃ : ∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N)
      (Y : Set (CTorus d L N₁ T.m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃ a Y) (XiCRaw (SA).G' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts (SA).G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {F₃' : CTorus d L N₁' T.m₁ (k + 1) × Fin N →
      DecParams (SB).G' × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
        ((SB).G'.Ω 1 × Fin N → ℂ) × ((SB).G'.Ω 1 → ℂ)}
    {Sol₃' : CTorus d L N₁' T.m₁ (k + 1) × Fin N →
      Dec2.DecParams (coverOf (SB).G') × Edat (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)}
    {Ev₃' : CTorus d L N₁' T.m₁ (k + 1) × Fin N → Set (CTorus d L N₁' T.m₁ (k + 1)) →
      RawData d L (N₁' * L ^ T.m₁) (k + 1) N × (unitPts (SB).G' × Fin N → ℂ) → ℂ}
    (hF₃' : ∀ (a : CTorus d L N₁' T.m₁ (k + 1) × Fin N) (s : DecParams (SB).G')
      (D : BgData (SB).G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (SB).G' (bgC0 d L N) (c7 d L N T.BG T.κ) (SB).ν D → ∀ (φ : (SB).G'.Ω 1 × Fin N → ℂ)
        (α : (SB).G'.Ω 1 → ℂ), IsDecBg (SB).G' (compWeight L (SB).a₁) (SB).ν (rho4 d L N T.BG T.κ) s D φ α →
        F₃' a (s, rawOf D) = (φ, α))
    (hSol₃' : ∀ (a : CTorus d L N₁' T.m₁ (k + 1) × Fin N)
      (p : Dec2.DecParams (coverOf (SB).G') × Edat (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol₃' a p).1 = dphi (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf (SB).G') (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν p.1)
          p.2.2.1 p.2.1 (pertSource (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Dec2.DecFixed (coverOf (SB).G') (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν p.1 false p.2.2.1 p.2.1
          (pertSource (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃' a p).2 ∧
        Small (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol₃' a p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol₃' a p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (Sol₃' a p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (SB).G') (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) (SB).ν p.1 false p.2.2.1 p.2.1
            (pertSource (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SB).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃' a p).2))
    (hEv₃' : ∀ a : CTorus d L N₁' T.m₁ (k + 1) × Fin N, Ev₃' a =
      evTerm (fun i : ParIdx (SB).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁' T.m₁ (k + 1))) =>
        i.1.1) (SB).G' T.m₀ (X1 (SB).G' T.m₀ k (LocalCover.fam T.m₀ a.1))
        (fun u t => siteFun (SB).G' (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁)) a.1 a.2
          (F₃' a (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁' T.m₁ (k + 1))) t,
            u.1))
          (Sol₃' a (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁' T.m₁ (k + 1))) t,
            flEdat (SB).G' (stepG d L N₁' T.m₁ k (rhoSepG d L T.m₁))
              (F₃' a (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁' T.m₁ (k + 1))) t,
                u.1))
              u.1.1 (hatPsiF (SB).G' (SB).a₁ (SB).ν (SB).hG' (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃' a)
                (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁' T.m₁ (k + 1))) t)
                u.1 u.2))).1
          (u.1, hatPsiF (SB).G' (SB).a₁ (SB).ν (SB).hG' (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃' a)
            (extParams (SB).G' (↑(LocalCover.nbhdF T.m₀ a.1) : Set (CTorus d L N₁' T.m₁ (k + 1))) t)
            u.1 u.2)))
    (hanEv₃' : ∀ (a : CTorus d L N₁' T.m₁ (k + 1) × Fin N)
      (Y : Set (CTorus d L N₁' T.m₁ (k + 1))),
      AnalyticOnNhd ℂ (Ev₃' a Y) (XiCRaw (SB).G' (compWeight L (SB).a₁) (SB).ν (k + 1) 1 T.t ×ˢ
        {ψh : unitPts (SB).G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hAs : ∀ e ∈ physVq (SA) (SA).a₁ (SA).ν T.t q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb)
      (Φ : ∀ b, ((SA).blockSplit T.m₀ hp).Ωb b),
      (A e σ).H l Φ = (A ((e.1, 0) : physParam N (SA)) σ).H l Φ +
        ∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N,
          if Lab.ysite l ∈ polyDom (SA).G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k
              (LocalCover.fam T.m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃ s (Lab.ysite l)) (fun _ => (1 : ℂ))
              ((SA).hatOf T.m₀ p₁ hp Φ) ((SA).hatOf T.m₀ p₁ hp Φ) σ
              (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          else 0)
    (hAs' : ∀ e ∈ physVq (SB) (SB).a₁ (SB).ν T.t q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lb')
      (Φ : ∀ b, ((SB).blockSplit T.m₀ hp').Ωb b),
      (A' e σ).H l Φ = (A' ((e.1, 0) : physParam N (SB)) σ).H l Φ +
        ∑ s : CTorus d L N₁' T.m₁ (k + 1) × Fin N,
          if Lab'.ysite l ∈ polyDom (SB).G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k
              (LocalCover.fam T.m₀ s.1) then
            e.2 s.1 s.2 * dirTerm (Ev₃' s (Lab'.ysite l)) (fun _ => (1 : ℂ))
              ((SB).hatOf T.m₀ p₁ hp' Φ) ((SB).hatOf T.m₀ p₁ hp' Φ) σ
              (e.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N)
          else 0)
    (hεH : 0 ≤ εH) (hεH' : 0 ≤ εH') {Kobs Kobs' : ℝ}
    (hK : Kc + Kc + K0 d L T.κ0 + K0 d L T.κ0 ≤ Kobs)
    (hK' : Kc' + Kc' + K0 d L T.κ0 + K0 d L T.κ0 ≤ Kobs') (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    -- the parameters and the cubes
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθV : θ ∈ physVq (SA) (SA).a₁ (SA).ν T.t q) (hθV' : θ' ∈ physVq (SB) (SB).a₁ (SB).ν T.t q)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (SA).G' (compWeight L 1) ν (k + 1) 1 T.t)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) ∈
      XiCRaw (SB).G' (compWeight L 1) ν (k + 1) 1 T.t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
      (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
    (hsrc : ∀ x, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x → ∀ i,
      θ'.2 (bm x) i = θ.2 x i)
    (Tc : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ))
    (hTc : ∀ b ∈ Tc, ∀ x ∈ box b.1 (cellSide L T.m₀ T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x) :
    obsCoeffParam ((SB).blockSplit T.m₀ hp').μ
        (fun θ t σ => tiltActObs A' hN' T.κ0_ent hεH' (D'.isDj_obsDomains rfl rfl (bm y) iy) hK'
          Rg hR 𝒰 θ t σ)
        (fun m => obsY1 T.m₀ (SB) (Lb' ⊕ Lb') (𝒴B) m)
        (fun m => blockMarkC (SB) T.m₀ hp' m.1 m.2)
        (fun θ m T'' => obsHker (𝒴B) (fun Y => hatCoeff (Ev' Y)
          (θ.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N) (obsUnitVec (SB) m)) T.m₀ T'')
        (obsRemLab (𝒴B) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb' ⊕ Lb') (𝒴B) (rootCube (m₀ := T.m₀) (blockIndex (bm y)))))
        (fun θ => obsGrFam (SB) T.m₀ hp' Ev' (𝒴B)
          (XiCRaw (SB).G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ' (Tc.image (σc)) =
      obsCoeffParam ((SA).blockSplit T.m₀ hp).μ
        (fun θ t σ => tiltActObs A hN T.κ0_ent hεH (D.isDj_obsDomains rfl rfl y iy) hK
          Rg hR 𝒰 θ t σ)
        (fun m => obsY1 T.m₀ (SA) (Lb ⊕ Lb) (𝒴A) m)
        (fun m => blockMarkC (SA) T.m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker (𝒴A) (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (obsUnitVec (SA) m)) T.m₀ T'')
        (obsRemLab (𝒴A) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb ⊕ Lb) (𝒴A) (rootCube (m₀ := T.m₀) (blockIndex y))))
        (fun θ => obsGrFam (SA) T.m₀ hp Ev (𝒴A)
          (XiCRaw (SA).G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ Tc := by
  have hd2 : 2 ≤ d := by have := T.hd; omega
  have hb : (SA).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN hd2 k T.m₁ _ hk ν β p₁ T.δ
  have hb' : (SB).betaU = β * (L : ℝ) ^ (k * (d - 2)) :=
    hatStepKG_betaU T.hN hd2 k T.m₁ _ hk ν β p₁ T.δ
  rw [hb] at hEv hAx hEv₃
  rw [hb'] at hEv' hAx' hEv₃'
  -- the domains of the labels on two tori
  have hmemV : ∀ Y : Set (CTorus d L N₁ T.m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ 𝒴v' ↔ Y ∈ 𝒴v) := by
    intro Y hY
    rw [h𝒴v, h𝒴v', Finset.mem_union, Finset.mem_union]
    exact or_congr (mem_vDomains_boxMap_iff (ϱ := rhoSepG d L T.m₁) hN hN' hnF hnF' hY)
      (mem_fDomains_boxMap_iff (ϱ := rhoSepG d L T.m₁) hN hN' hnF hnF' hY)
  refine obsCoeffParam_twoTorus_source T.hN hk ν β p₁ T.δ D.core D'.core T.large_block
    T.dom_margin T.coer_margin T.δc_small hN hN' hn hn' hnS hnS' hnF hnF' y iy hX₁R
    (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hq hrad hF₁ hF₁' hSol hSol'
    hEv hEv' (fun Y _ u hu u' hu' h => hdEv Y u hu u' hu' (agreeOn_mono (fun x hx => Or.inl hx) h.1)
      h.2) (D.isDj_obsDomains rfl rfl y iy) (D'.isDj_obsDomains rfl rfl (bm y) iy) θ θ' hθ hθ'
    hraw hp hp' Tc hTc T.m₀_pos hρ Lab Lab' ys ys' hys hys' hmemV A A' T.κ0_ent
    T.κ0_ent hεH hεH' hK hK' Rg hR 𝒰 hF₂ hF₂' hSol₂ hSol₂' hθV hθV' ?_ ?_ hF₃ hSol₃ hEv₃ hanEv₃ hF₃' hSol₃' hEv₃' hanEv₃'
    ?_ ?_ hsrc
  · intro e he σ hσ l Φ
    refine (hAx e he σ hσ l Φ).trans ?_
    exact congrArg (fun t => -(β : ℂ) * t) (rayTerm_evTerm_eq_evDec (SA).hG'
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₂ Sol₂ (Lab.ysite l) _ _ σ _)
  · intro e he σ hσ l Φ
    refine (hAx' e he σ hσ l Φ).trans ?_
    exact congrArg (fun t => -(β : ℂ) * t) (rayTerm_evTerm_eq_evDec (SB).hG'
      (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₂' Sol₂' (Lab'.ysite l) _ _ σ _)
  · intro e he σ hσ l Φ
    exact hAs e he σ hσ l Φ
  · intro e he σ hσ l Φ
    exact hAs' e he σ hσ l Φ

end Tower

end Balaban.Polymer.TwoTorusStep
