/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyTorusCoef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The energy coefficient `e0 = dz + c` of the core family on two tori

`coreE0_twoTorus` compares, on two tori `N₁`, `N₁'` at a common box, the coefficient family
`e0 θ C = dz θ C + c θ C` of the core `e0CoeffFamily_value_fromTowerG_core`:
the root `z` and the set `C` of cubes of the box on the first torus, the root `bc z` and the set
`cubeMap '' C` on the second, parameters `θ`, `θ'` of `physV` whose raw data agree on the box.
The determinant part `dz` is the term of the determinant record (`detTerm_twoTorus_fromTowerG`);
the interpolation part `c` is `coreCoeff_twoTorus`.  The objects of the core on each torus enter
with exactly the properties that the core exports.
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

section E0

variable {d L N : ℕ} [NeZero L] {κmin : ℝ}

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

/-- **The coefficient `e0 = dz + c` of the core on two tori.**  See the module doc-string. -/
theorem coreE0_twoTorus
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁]
    [NeZero N₁'] (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (h5 : 5 < N₁) (h5' : 5 < N₁') (ν : ℝ) (hν0 : 0 ≤ ν)
    (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (D : StepScaleDataG T k hk N₁ ν β p₁) (D' : StepScaleDataG T k hk N₁' ν β p₁)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
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
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν T.t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν T.t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
    (hGdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u))
    (hGdep' : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SB)) (bc z)})
      (u : ℂ), DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkGParamG (SB) F₁' Sol' p₁ hp' (bc z) T.t θ' i u))
    (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
      InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
    {Lb : Type} [Fintype Lb]
    {Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb} {εH : ℝ}
    {A₀ : physParam N (SA) → ℂ →
      LabelAct (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl))
        ((SA).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {Lb' : Type} [Fintype Lb']
    {Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ Lb'} {εH' : ℝ}
    {A₀' : physParam N (SB) → ℂ →
      LabelAct (commonLabels Lab₀' hN' (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl))
        ((SB).blockSplit 1 hp').Ωb εH' (2 * T.κdec - 1) T.κ0
        (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)}
    {c : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    {c' : physParam N (SB) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hc : ∀ θ C, c θ C = gsumCoeff ((SA).blockSplit 1 hp).μ
      (commonLabels Lab₀ hN (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)) (A₀ θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z} =>
        commonAnchor Lb (fun _ => Set.univ) (e1DomG (SA)) z i)
      (fun i u Φ => e1MarkGParamG (SA) F₁ Sol p₁ hp z T.t θ i u Φ) C)
    (hc' : ∀ θ C, c' θ C = gsumCoeff ((SB).blockSplit 1 hp').μ
      (commonLabels Lab₀' hN' (by have := T.hL; omega)
        (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl)) (A₀' θ)
      (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SB)) (bc z)} =>
        commonAnchor Lb' (fun _ => Set.univ) (e1DomG (SB)) (bc z) i)
      (fun i u Φ => e1MarkGParamG (SB) F₁' Sol' p₁ hp' (bc z) T.t θ i u Φ) C)
    {eps κ'' cdet : ℝ} (E : DetExpansionLocC (SA) 1 z eps κ'' cdet)
    (E' : DetExpansionLocC (SB) 1 (bc z) eps κ'' cdet)
    (hEterm : ∀ D Y, E.term D Y = ∑ y ∈ (SA).blockU z,
      detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y Y)
    (hEterm' : ∀ D Y, E'.term D Y = ∑ y ∈ (SB).blockU (bc z),
      detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y Y)
    {dz : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    {dz' : physParam N (SB) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (hdz : ∀ (D' : BgData (SA).G' N), XiCData (SA).G' (SA).a (SA).ν (k + 1) 1 T.t D' →
      ∀ g C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C = E.term D' C)
    (hdz' : ∀ (D' : BgData (SB).G' N), XiCData (SB).G' (SB).a (SB).ν (k + 1) 1 T.t D' →
      ∀ g C, dz' (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C = E'.term D' C)
    {e0 : physParam N (SA) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    {e0' : physParam N (SB) →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ}
    (he0 : ∀ θ C, e0 θ C = dz θ C + c θ C)
    (he0' : ∀ θ C, e0' θ C = dz' θ C + c' θ C)
    {val : FA → FA → ℂ → ΛA → ℂ}
    (I0 : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ 2
      ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
      (2 * T.κdec - 1) (rawOf (SA).D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SA) (SA).a₁ (SA).ν T.t (1 / (SA).β))
      (physXW (SA) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
      (physAgΘ (SA)) (AgFDirPair (SA)))
    {val' : FB → FB → ℂ → ΛB → ℂ}
    (I0' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) p₁ 2
      ((SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SB).β))
      (2 * T.κdec - 1) (rawOf (SB).D', (0 : CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ))
      (physSΛEta (SB) (SB).a₁ (SB).ν T.t (1 / (SB).β))
      (physXW (SB) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
        (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
      (physAgΘ (SB)) (AgFDirPair (SB)))
    (hFd : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0
      (physVq (SA) (SA).a₁ (SA).ν T.t 1))
    (hFd' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) (((1 / (SB).β : ℝ)) : ℂ)) I0'
      (physVq (SB) (SB).a₁ (SB).ν T.t 1))
    (hεU : 0 ≤ (SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))
    (hεU' : 0 ≤ (SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SB).β))
    (hLbI : Lb = {Y // Y ∈ I0.𝒴})
    (hLbI' : Lb' = {Y // Y ∈ I0'.𝒴})
    (hεHI : εH = 2 ^ 2 * (2 * ((SA).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SA).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SA).β))))
    (hεHI' : εH' = 2 ^ 2 * (2 * ((SB).β * prop33EpsEtaScaled d L N T.m₁ k 1 (SB).a₁ T.BG T.BG₂ T.κ T.t
      (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / (SB).β))))
    (hLabI : HEq Lab₀ (thickLabels I0.𝒴 I0.dom))
    (hLabI' : HEq Lab₀' (thickLabels I0'.𝒴 I0'.dom))
    (hAI : HEq A₀ (commonAct (zeroSourceAct
      (labelActFamilyOn (SA) 1 (physInclScaled N (SA) (((1 / (SA).β : ℝ)) : ℂ)) I0 hFd hN hp
        (by norm_num) hεU T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SA)) (e1DomG_isDj_of_eq T hm₀ D rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two))
    (hAI' : HEq A₀' (commonAct (zeroSourceAct
      (labelActFamilyOn (SB) 1 (physInclScaled N (SB) (((1 / (SB).β : ℝ)) : ℂ)) I0' hFd' hN' hp'
        (by norm_num) hεU' T.κ0_ent T.marks_K0_le) 2 (by norm_num))
      hN' (by have := T.hL; omega)
      (fun _ => Set.univ) (e1DomG (SB)) (e1DomG_isDj_of_eq T hm₀ D' rfl rfl)
      (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU')) T.κ0_two))
    (hI𝒴 : I0.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hI𝒴' : I0'.𝒴 = (Finset.univ.biUnion fun z : TB =>
        polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁' T.m₁ (k + 1) × Fin N =>
        polyDom (GB) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₂' : TB → DecParams (GB) × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp T.κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    {Sol₂ : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol₂' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HA) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Small (HA) (Sol₂ b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₂ b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HA) (Sol₂ b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ b p).2))
    (hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
      StrictDataM (HB) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
        (Sol₂' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small (HB) (Sol₂' b p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₂' b p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        SupBounds (HB) (Sol₂' b p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hIT : ∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1))) (x w : FA) (σ : ℂ)
        (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
      I0.T Y x w σ (Θ, 0) = -(((SA).β : ℝ) : ℂ) * ∑ z : TA,
        if Y ∈ polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 ν (SA).hG'
            (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z) (Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) ν k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0)
    (hIT' : ∀ (Y : Set (CTorus d L N₁' T.m₁ (k + 1))) (x w : FB) (σ : ℂ)
        (Θ : RawData d L (N₁' * L ^ T.m₁) (k + 1) N),
      I0'.T Y x w σ (Θ, 0) = -(((SB).β : ℝ) : ℂ) * ∑ z : TB,
        if Y ∈ polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 ν (SB).hG'
            (((β * (L : ℝ) ^ (k * (d - 2))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z) (Sol₂' z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) ν k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0) :
    e0' θ' (Tb.image (σc)) = e0 θ Tb := by
  classical
  have hrc' : L ^ (k + 1) * rc ≤ R := le_trans (Nat.le_add_right _ _) hrc
  have hcc := coreCoeff_twoTorus T hm₀ hk hN hN' ν β p₁ D D' hp hp' hF₁ hF₁' hSol hSol' z hz hrc'
    hroot hn hn' θ θ' hθ hθ' hraw hGdep hGdep' Tb hTb hc hc' I0 I0' hFd hFd' hεU hεU' hLbI hLbI'
    hεHI hεHI' hLabI hLabI' hAI hAI' hI𝒴 hI𝒴' hF₂ hF₂' hSol₂ hSol₂' hIT hIT'
  obtain ⟨D₀, hD₀, hθD⟩ := hθ.1
  obtain ⟨D₀', hD₀', hθD'⟩ := hθ'.1
  have hraw₀ : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
      (rawOf D₀) (rawOf D₀') := by
    rw [← hθD, ← hθD']; exact hraw
  have hdd : dz' θ' (Tb.image (σc)) = dz θ Tb := by
    have e1 : θ = (⟨rawOf D₀, rawOf_mem_rawSub D₀⟩, θ.2) := Prod.ext (Subtype.ext hθD) rfl
    have e2 : θ' = (⟨rawOf D₀', rawOf_mem_rawSub D₀'⟩, θ'.2) := Prod.ext (Subtype.ext hθD') rfl
    rw [e2, hdz' D₀' hD₀', e1, hdz D₀ hD₀]
    exact detExpansionLocC_term_twoTorus_fromTowerG T hk hN hN' h5 h5' hν0 hν β p₁ hD₀ hD₀' z hz
      hrc hroot hn hn' hraw₀ Tb hTb E E' hEterm hEterm'
  rw [he0', he0, hdd, hcc]

end E0

end Balaban.Inhabited
