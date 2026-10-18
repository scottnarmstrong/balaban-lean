/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyDirect
public import Balaban.Polymer.TwoTorusGapStepDetPair

/-!
# The energy coefficient at the cells of a polymer on two tori (blocker 7)

`gsumCoeff_e1_cellSites`: the pair theorem of the gap-scale clause for the energy coefficient of a
root: the recentring vector is chosen for the π'-cube of the root and the sites of the cubes of the
cells (`exists_recentring_int`), and `gsumCoeff_e1_recentred_of_directTerms` is applied at it.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep MeasureTheory

section Cells

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "𝔅A" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
  Set.univ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "σAc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tA)
set_option hygiene false in
local notation "σBi" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tB)⁻¹

set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "tAz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "tBz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "τA" => (fun μ => ((((tAz μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "τB" => (fun μ => ((((tBz μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "σc1" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "σAc1" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := 1) (Equiv.addRight tAz)
set_option hygiene false in
local notation "σBi1" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := 1) (Equiv.addRight tBz)⁻¹

set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "ΛB" => RawData d L (N₁' * L ^ m₁) (k + 1) N ×
  (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => ((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ)
set_option hygiene false in
local notation "FB" => ((SB).U × Fin N → ℂ) × ((SB).U × Fin N → ℂ)

/-- **The energy coefficient of a root at the cubes of the cells of a polymer, on two tori** (the pair
theorem of the gap-scale clause, analogue of `sum_blockU_detActivityBg_cellSites_gen`).  Let `X` be a
set of cells of the quarter box (`Kn ≤ Kn'` cells per side), `Y`, `Y'` the cubes of its cells on the
two tori, and `z` a root such that the π'-cube of its root cell and the sites of `Y` have spread `Ds`
and lie within `q` of the origin, with the slacks `hslack` and the label margins `hlab`.  If the raw
data correspond under the recentred map for every recentring vector (`hraw`), the energy coefficient
of the root `bc z` at `Y'` equals that of `z` at `Y`, for direct terms of the explicit form.  The
recentring vector is `exists_recentring_int`; the root, the cubes and the margins come from
`det_root_recentred`, `cubeAct_recentred_cells`; the rest is
`gsumCoeff_e1_recentred_of_directTerms`. -/
theorem gsumCoeff_e1_cellSites
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hd : 0 < d) (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (hm₁ : 1 ≤ m₁)
    {Kn Kn' Ds q : ℕ} [NeZero Kn] [NeZero Kn'] (hK : 26 ≤ Kn) (hKK' : Kn ≤ Kn')
    (hm : (N₁ * L ^ m₁) * L ^ (k + 1) = cellSide L 1 m₁ (k + 1) * Kn)
    (hm' : (N₁' * L ^ m₁) * L ^ (k + 1) = cellSide L 1 m₁ (k + 1) * Kn')
    {Dc : ℕ} (hDc : Dc ≤ (Kn - 26) / 25) (hDsdef : Ds = cellSide L 1 m₁ (k + 1) * (Dc + 1) - 1)
    {X : Set (Fin d → ℤ)} (hXq : ∀ c ∈ X, ∀ μ, (c μ).natAbs ≤ Kn / 4)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (hY : sitesOf Y = {x | (fun μ => (((((x μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) :
      ZMod Kn)).valMinAbs) ∈ X})
    (hY' : sitesOf Y' = {x' | (fun μ => (((((x' μ).val / cellSide L 1 m₁ (k + 1) : ℕ)) :
      ZMod Kn')).valMinAbs) ∈ X})
    (z : TA)
    (hsp : ∀ x ∈ box (rootCube (m₀ := 1) z).1 (L * cellSide L 1 m₁ (k + 1)),
      ∀ y ∈ box (rootCube (m₀ := 1) z).1 (L * cellSide L 1 m₁ (k + 1)) ∪ sitesOf Y, ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ Ds)
    (hq : ∀ x ∈ box (rootCube (m₀ := 1) z).1 (L * cellSide L 1 m₁ (k + 1)) ∪ sitesOf Y, ∀ μ,
      |(x μ).valMinAbs| ≤ q)
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack' : 20 * (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hlab : 2 * ((Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 2 * ((L - 1) * cellSide L 1 m₁ (k + 1) +
      L * cellSide L 1 m₁ (k + 1))) + 5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hlab' : 2 * ((Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1)) + 2 * ((L - 1) * cellSide L 1 m₁ (k + 1) +
      L * cellSide L 1 m₁ (k + 1))) + 5 * (L * cellSide L 1 m₁ (k + 1)) <
        (N₁' * L ^ m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : ∀ zv : Fin d → ℤ, (∀ μ, ((cellSide L 1 m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ) →
      (∀ x ∈ box (rootCube (m₀ := 1) z).1 (L * cellSide L 1 m₁ (k + 1)) ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + zv μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
          ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight tAz) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
        (symRaw (Equiv.addRight tBz) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 →
      ‖u‖ * markedRad d L N k 1 κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hGdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u))
    (hL2 : 2 ≤ L) (hdom : ∀ b, ∀ Y ∈ e1DomG (SA) b, IsDj 1 (k + 1) Y)
    (hdom' : ∀ b, ∀ Y ∈ e1DomG (SB) b, IsDj 1 (k + 1) Y)
    -- the direct terms of the two steps and their relative families
    {Rσ εU a κ0 KcL : ℝ} {Θ₀ : ΛA} {Θ₀' : ΛB} {SΛ : Set ΛA} {SΛ' : Set ΛB}
    {XW : Set (FA × FA)} {XW' : Set (FB × FB)} {val : FA → FA → ℂ → ΛA → ℂ}
    {val' : FB → FB → ℂ → ΛB → ℂ} {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → ΛA → ΛA → Prop}
    {AgΘ' : Set (CTorus d L N₁' m₁ (k + 1)) → ΛB → ΛB → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → FA → FA → Prop}
    {AgF' : Set (CTorus d L N₁' m₁ (k + 1)) → FB → FB → Prop}
    (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) p₁ Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (I' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) p₁ Rσ εU a Θ₀' SΛ' XW' val' AgΘ' AgF')
    {cJ cJ' : ℂ} {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
    (hF : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I V)
    (hF' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' V')
    (hp0 : 0 < p₁) (hRσ : 2 ≤ Rσ) (hεU : 0 ≤ εU) (hκ0 : aEnt d L + 2 ≤ κ0)
    (hKc : K0 d L κ0 ≤ KcL)
    (hV : ((θ.1, 0) : physParam N (SA)) ∈ V) (hV' : ((θ'.1, 0) : physParam N (SB)) ∈ V')
    -- the explicit form of the direct terms at the zero source
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρc : 2 * p₁ ≤ cψ)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₂' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    {Sol₂ : TA →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol₂' : TB →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Small (HA) (Sol₂ b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₂ b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₂ b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ b p).2))
    (hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small (HB) (Sol₂' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₂' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₂' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hI𝒴 : I.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hI𝒴' : I'.𝒴 = (Finset.univ.biUnion fun z : TB =>
        polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁' m₁ (k + 1) × Fin N =>
        polyDom (GB) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hIT : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (x w : FA) (σ : ℂ)
        (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      I.T Y x w σ (Θ, 0) = -(((SA).β : ℝ) : ℂ) * ∑ z : TA,
        if Y ∈ polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 νS hGA cc (F₂ z) (Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) νS k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0)
    (hIT' : ∀ (Y : Set (CTorus d L N₁' m₁ (k + 1))) (x w : FB) (σ : ℂ)
        (Θ : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      I'.T Y x w σ (Θ, 0) = -(((SB).β : ℝ) : ℂ) * ∑ z : TB,
        if Y ∈ polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 νS hGB cc (F₂' z) (Sol₂' z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) νS k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0) :
    gsumCoeff ((SB).blockSplit 1 hp').μ
        (commonLabels (thickLabels I'.𝒴 I'.dom) hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
        (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
            hp0 (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
          hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom'
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
        (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB)) (bc z) i')
        (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc z) eps θ' i' u Φ') Y' =
      gsumCoeff ((SA).blockSplit 1 hp).μ
        (commonLabels (thickLabels I.𝒴 I.dom) hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
        (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
            hp0 (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
          hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
        (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
        (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ) Y := by
  classical
  have : NeZero (cellSide L 1 m₁ (k + 1)) := ⟨(cellSide_pos (L := L) 1 m₁ (k + 1)).ne'⟩
  have hapos : 0 < cellSide L 1 m₁ (k + 1) := cellSide_pos (L := L) 1 m₁ (k + 1)
  have hLpos : 0 < L := by omega
  have hpK : 0 < L ^ (k + 1) := pow_pos hLpos _
  have hap : 4 * L ^ (k + 1) ≤ cellSide L 1 m₁ (k + 1) := by
    have h4 : 4 ≤ L ^ (1 + m₁) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ L ^ 2 := Nat.pow_le_pow_left hL2 2
        _ ≤ L ^ (1 + m₁) := Nat.pow_le_pow_right hLpos (by omega)
    have : cellSide L 1 m₁ (k + 1) = L ^ (k + 1) * L ^ (1 + m₁) := by
      unfold cellSide; rw [← pow_add]; congr 1; omega
    rw [this]
    nlinarith
  have hbox : ∃ b, box b (L * cellSide L 1 m₁ (k + 1)) ⊆
      box (rootCube (m₀ := 1) z).1 (L * cellSide L 1 m₁ (k + 1)) := ⟨_, subset_rfl⟩
  have hDs1 : Ds + 1 ≤ cellSide L 1 m₁ (k + 1) * (Dc + 1) := by
    have : 1 ≤ cellSide L 1 m₁ (k + 1) * (Dc + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hDsa : cellSide L 1 m₁ (k + 1) ≤ Ds + 1 := by
    rw [hDsdef]
    have := Nat.le_mul_of_pos_right (cellSide L 1 m₁ (k + 1)) (show 0 < Dc + 1 by omega)
    omega
  obtain ⟨hn25, hn25', -⟩ := compact_site_margins (K := Kn) (K' := Kn')
    (cs := cellSide L 1 m₁ (k + 1)) (Dc := Dc) (Ds := Ds) (q := 0) hK hKK' hapos hDc hDs1
    (Nat.zero_le _)
  rw [← hm] at hn25
  rw [← hm'] at hn25'
  obtain ⟨zv, hz, hint⟩ := exists_recentring_int (n := (N₁ * L ^ m₁) * L ^ (k + 1))
    (a := cellSide L 1 m₁ (k + 1)) (L := L) (D := Ds) (q := q) hd hapos hL2
    (cellSide_dvd hN le_rfl) hbox hsp hn25 hq hqn
  have hcsL : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hxX : rootSite z ∈ box (rootCube (m₀ := 1) z).1 (L * cellSide L 1 m₁ (k + 1)) :=
    box_mono _ hcsL (rootSite_mem_box_rootCube (m₀ := 1) z)
  obtain ⟨rc, hzc, hrc, hzz, hroot, -⟩ := det_root_recentred (N₁' := N₁') hd hL2 le_rfl hm₁ z zv
    hDsa hap hn25 hqn hslack hslack' (fun μ => hq _ (Or.inl hxX) μ)
    (fun x hx μ => hint x (Or.inl hx) μ)
  have htA : ∀ μ, L ^ ((k + 1) + 1 + m₁) ∣ (tAz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + 1 + m₁) ∣ (tBz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tAz μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)
  have htB1 : ∀ μ, L ^ (k + 1) ∣ (tBz μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)
  have hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hbd : ∀ y ∈ sitesOf Y, InBox d (Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1))
      ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz) :=
    fun y hy => inBox_mono (by omega) (inBox_add_intCast hnR y zv (hint y (Or.inr hy)))
  have hbm : bm '' sitesOf Y = sitesOf Y' := by
    rw [hY, hY']
    exact boxMap_image_cellSites hm hm' hK hKK' X hXq
  have hYc := cubeAct_recentred_cells hN hN' tAz tBz htA htB Y Y' hbm
    (fun y hy => boxMap_add_intCast hnR y zv (hint y (Or.inr hy))) hbd (by omega)
  have hσB := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := 1) tBz htB)
  have hY'eq : Y' = Y.image (fun b => σBi1 (σc1 (σAc1 b))) := by
    ext b'
    rw [Finset.mem_image]
    constructor
    · intro hb'
      have h1 : Balaban.Fluctuation.cubeMap (Equiv.addRight tBz) b' ∈
          cubeAct (Equiv.addRight tBz) Y' := mem_cubeAct.2 ⟨b', hb', rfl⟩
      rw [hYc] at h1
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h1
      obtain ⟨b, hb, rfl⟩ := mem_cubeAct.1 hc
      refine ⟨b, hb, ?_⟩
      rw [hce, cubeMap_inv hN' hσB]
    · rintro ⟨b, hb, rfl⟩
      have h1 : σc1 (σAc1 b) ∈ cubeAct (Equiv.addRight tBz) Y' := by
        rw [hYc]
        exact Finset.mem_image_of_mem _ (mem_cubeAct.2 ⟨b, hb, rfl⟩)
      obtain ⟨b', hb', he⟩ := mem_cubeAct.1 h1
      rw [← he, cubeMap_inv hN' hσB]
      exact hb'
  set r := Ds + (Ds + 1) / 4 + 2 * L ^ (k + 1) with hr
  have hzc' : InBox d (r / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA) := by
    rw [← rootAct_addRight tAz htA1 z]
    refine inBox_mono ?_ hzc
    rw [Nat.le_div_iff_mul_le hpK, Nat.mul_comm]
    omega
  have hzz' : bc z = bc (z + τA) - τB := by
    rw [rootAct_addRight tBz htB1, rootAct_addRight tAz htA1] at hzz
    rw [← hzz, add_sub_cancel_right]
  have hw : L * cellSide L 1 m₁ (k + 1) ≤ 2 * r + 1 := by
    have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
      (b := (rootCube (m₀ := 1) z).1 + tAz) (s := L * cellSide L 1 m₁ (k + 1)) (r := r)
      (t := min (L * cellSide L 1 m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
      (min_le_left _ _) (min_le_right _ _) (fun x hx => by
        obtain ⟨y, rfl⟩ : ∃ y, x = y + tAz := ⟨x - tAz, by abel⟩
        exact hroot y ((mem_box_add_iff _ _ y _).1 hx))
    rcases min_choice (L * cellSide L 1 m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
    · rw [h] at hw0; exact hw0
    · rw [h] at hw0; omega
  have hrootT : ∀ x ∈ rootSet 1 z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) :=
    fun x hx => hroot x (box_mono _ hcsL hx)
  have hT : ∀ b ∈ Y, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) :=
    fun b hb x hx => hbd x (mem_sitesOf.2 ⟨b, hb, hx⟩)
  rw [hY'eq, hzz']
  exact gsumCoeff_e1_recentred_of_directTerms hN2 hk νS β p₁ δ hC hC' hGA hGB hMX hmar hαK hsm hF₁
    hF₁' hSol hSol' hd hN hN' hm₁ zv hz z hw hslack hslack' hlab hlab' hzc' hrootT θ θ' hθ hθ'
    (hraw zv hz hint) hρ hp hp' hum hGdep hL2 hdom hdom' I I' hF hF' hp0 hRσ hεU hκ0 hKc hV hV' cc
    hcψ hρc hrad hF₂ hF₂' hSol₂ hSol₂' hI𝒴 hI𝒴' hIT hIT' Y hT

end Cells

end Balaban.Polymer.TwoTorusStep
