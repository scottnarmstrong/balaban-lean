/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerCoreFamCoef
import Mathlib.Tactic.Linarith

/-!
# Uniqueness of the core coefficient family

`coreE0_unique`: two systems of the objects of `e0CoeffFamily_value_fromTowerG_core` on the same
step (each with the properties that the core exports) give the same family on `physV`:
`e0' θ C = e0 θ C` for `θ ∈ physV` and every set `C` of cubes.  The determinant parts are the
explicit sums of rooted activities; the interpolation parts agree by `coreCoeff_unique` (the
pinned `F₁`, `Sol`, `F₂`, `Sol₂` are unique on the chart, so the marks and the direct terms
agree, and the labels are the same polymer domains).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory
  Balaban.Polymer.TwoTorusStep

section Unique

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

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

/-- **Uniqueness of the core coefficient family.**  See the module doc-string. -/
theorem coreE0_unique
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁]
    (hN : L ^ 1 ∣ N₁) (ν β p₁ : ℝ)
    (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < (SA).p₁)
    (z : TA) (θ : physParam N (SA)) (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν T.t)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Lb : Type} [Fintype Lb]
    {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb} {εH : ℝ}
    {A₀ : physParam N (SA) → ℂ →
      LabelAct (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        ((SA).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {c : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hc : ∀ θ C, c θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
      (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)) (A₀ θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
        commonAnchor Lb (fun _ => Set.univ) (e1DomG (SA)) z i)
      (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) C)
    {val : FA → FA → ℂ → ΛA → ℂ}
    (I0 : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
      (2 * T.κdec - 1) (rawOf (SA).D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SA) (SA).a₁ (SA).ν T.t (1 / (SA).β))
      (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
      (physAgΘ (SA)) (AgFDirPair (SA)))
    (hFd : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0
      (physVq (SA) (SA).a₁ (SA).ν T.t 1))
    (hεU : 0 ≤ (SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
    (hLbI : Lb = {Y // Y ∈ I0.𝒴})
    (hεHI : εH = 2 ^ 2 * (2 * ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))))
    (hLabI : HEq Lab₀ (thickLabels I0.𝒴 I0.dom))
    (hAI : HEq A₀ (commonAct (zeroSourceAct
      (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0 hFd hN hp
        (by norm_num) hεU T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two)) 
    (hI𝒴 : I0.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hSol : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol b))
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hSol₂ : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol₂ b))
    (hT : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : FA) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                I0.T Y x w σ (Θ, 0) = -((SA).β : ℂ) *
                  ∑ z : TA, if Y ∈ polyDom (SA).G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      (SA).G' 1 (X1 (SA).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν k z
                        (F₂ z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂ z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂ z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                              (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                          (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0)
    (hGdep : ∀ θ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u))
    {Lb' : Type} [Fintype Lb']
    {Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb'} {εH' : ℝ}
    {A₀' : physParam N (SA) → ℂ →
      LabelAct (commonLabels Lab₀' hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        ((SA).blockSplit 1 hp).Ωb εH' (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {c' : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hc' : ∀ θ C, c' θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
      (commonLabels Lab₀' hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)) (A₀' θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
        commonAnchor Lb' (fun _ => Set.univ) (e1DomG (SA)) z i)
      (fun i u Φ => e1MarkGParamG (SA) F₁' Sol' p₁ hp z T.t θ i u Φ) C)
    {val' : FA → FA → ℂ → ΛA → ℂ}
    (I0' : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
      (2 * T.κdec - 1) (rawOf (SA).D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SA) (SA).a₁ (SA).ν T.t (1 / (SA).β))
      (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
      (physAgΘ (SA)) (AgFDirPair (SA)))
    (hFd' : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0'
      (physVq (SA) (SA).a₁ (SA).ν T.t 1))
    (hεU' : 0 ≤ (SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
    (hLbI' : Lb' = {Y // Y ∈ I0'.𝒴})
    (hεHI' : εH' = 2 ^ 2 * (2 * ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))))
    (hLabI' : HEq Lab₀' (thickLabels I0'.𝒴 I0'.dom))
    (hAI' : HEq A₀' (commonAct (zeroSourceAct
      (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0' hFd' hN hp
        (by norm_num) hεU' T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU')) T.κ0_two)) 
    (hI𝒴' : I0'.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hF₁' : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    (hSol' : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol' b))
    {F₂' : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {Sol₂' : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    (hF₂' : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    (hSol₂' : ∀ b, SolSpec (GA) (HA) (SA).a₁ (SA).ν T.BG T.BG₂ T.κ T.t T.t (Sol₂' b))
    (hT' : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : FA) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                I0'.T Y x w σ (Θ, 0) = -((SA).β : ℂ) *
                  ∑ z : TA, if Y ∈ polyDom (SA).G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z)) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                      (SA).G' 1 (X1 (SA).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                      (fun u s => blockEnergyFun (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L (SA).a₁) (SA).ν k z
                        (F₂' z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                        (Sol₂' z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                          flEdat (SA).G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂' z (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                              (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF (SA).G' (SA).a₁ (SA).ν (SA).hG' (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z)
                          (extParams (SA).G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0)
    (hGdep' : ∀ θ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁' Sol' p₁ hp z T.t θ i u))
    {eps κ'' cdet : ℝ} (E : DetExpansionLocC (SA) 1 z eps κ'' cdet)
    (E' : DetExpansionLocC (SA) 1 z eps κ'' cdet)
    (hEterm : ∀ D Y, E.term D Y = ∑ y ∈ (SA).blockU z,
      detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y Y)
    (hEterm' : ∀ D Y, E'.term D Y = ∑ y ∈ (SA).blockU z,
      detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y Y)
    {dz dz' : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hdz : ∀ (D' : BgData (SA).G' N), XiCData (SA).G' (SA).a (SA).ν (k + 1) 1 T.t D' →
      ∀ g C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C = E.term D' C)
    (hdz' : ∀ (D' : BgData (SA).G' N), XiCData (SA).G' (SA).a (SA).ν (k + 1) 1 T.t D' →
      ∀ g C, dz' (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C = E'.term D' C)
    {e0 e0' : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (he0 : ∀ θ C, e0 θ C = dz θ C + c θ C)
    (he0' : ∀ θ C, e0' θ C = dz' θ C + c' θ C)
    (C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    e0' θ C = e0 θ C := by
  obtain ⟨D₀, hD₀, hD₀θ⟩ := hθ.1
  have e1 : θ = (⟨rawOf D₀, rawOf_mem_rawSub D₀⟩, θ.2) := Prod.ext (Subtype.ext hD₀θ) rfl
  have hdd : dz' θ C = dz θ C := by
    rw [e1, hdz' D₀ hD₀, hdz D₀ hD₀, hEterm, hEterm']
  rw [he0', he0, hdd, coreCoeff_unique T hm₀ hk hN ν β p₁ D hp z θ hθ (hc := hc) (hc' := hc')
    (hGdep := hGdep) (hGdep' := hGdep') (I0 := I0) (I0' := I0') (hFd := hFd) (hFd' := hFd')
    (hεU := hεU) (hεU' := hεU') (hLbI := hLbI) (hLbI' := hLbI') (hεHI := hεHI)
    (hεHI' := hεHI') (hLabI := hLabI) (hLabI' := hLabI') (hAI := hAI) (hAI' := hAI')
    (hI𝒴 := hI𝒴) (hI𝒴' := hI𝒴') (hF₁ := hF₁) (hF₁' := hF₁') (hSol := hSol) (hSol' := hSol')
    (hF₂ := hF₂) (hF₂' := hF₂') (hSol₂ := hSol₂) (hSol₂' := hSol₂') (hT := hT) (hT' := hT') C]

end Unique

end Balaban.Inhabited
