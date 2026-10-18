/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyCoef
public import Balaban.Polymer.TwoTorusGapTowerTieMem

/-!
# The energy coefficient of a root under the recentring map, for explicit direct terms (blocker 7)

`gsumCoeff_e1_recentred_of_directTerms`: the recentred form of `gsumCoeff_e1_twoTorus_of_directTerms`.
The labels of the energy coefficient are the domains of `DirectTerms` records `I`, `I'` of the two
steps whose domains are those of the local covers of the blocks and of the sites (`hI𝒴`) and whose
terms at zero source are the potential part of decoupled pairs (`hIT`), and the activity is the
zero-source family of their relative families.  The domain labels correspond under
`φ x = bm (x + tA) - tB` (`mem_obsLabelDomains_recentred_iff`, `preimage_recentred`), their activities
by `labelActZero_recentred`, and the rest is `gsumCoeff_e1_recentred_of_domainLabels`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep MeasureTheory

section CoefRec

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

/-- **The energy coefficient of a root under the recentring map, for direct terms of the explicit
form.**  The recentred form of `gsumCoeff_e1_twoTorus_of_directTerms`: the labels are the domains of
`DirectTerms` instances `I`, `I'` of radius `p₁` of the two steps with the explicit domains
(`hI𝒴`, the domains of the local covers of the blocks and of the sites) and the explicit terms at zero
source (`hIT`, the potential part of decoupled pairs `(F₂, Sol₂)`), and the activity is the zero-source
family of the relative families `hF`, `hF'`.  The domain labels correspond by
`mem_obsLabelDomains_recentred_iff` and `preimage_recentred`, their activities by
`labelActZero_recentred`, and the rest is `gsumCoeff_e1_recentred_of_domainLabels`. -/
theorem gsumCoeff_e1_recentred_of_directTerms
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
    (zv : Fin d → ℤ) (hz : ∀ μ, ((cellSide L 1 m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ)
    (z : TA) {R : ℕ} (hw : L * cellSide L 1 m₁ (k + 1) ≤ 2 * R + 1)
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnO : 2 * (R + 2 * ((L - 1) * cellSide L 1 m₁ (k + 1) + L * cellSide L 1 m₁ (k + 1))) +
      5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnO' : 2 * (R + 2 * ((L - 1) * cellSide L 1 m₁ (k + 1) + L * cellSide L 1 m₁ (k + 1))) +
      5 * (L * cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hzc : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA))
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
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
        else 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz)) :
    gsumCoeff ((SB).blockSplit 1 hp').μ
        (commonLabels (thickLabels I'.𝒴 I'.dom) hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
        (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
            hp0 (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
          hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom'
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
        (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB))
          (bc (z + τA) - τB) i')
        (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc (z + τA) - τB) eps θ' i' u Φ')
        (T.image (fun b => σBi1 (σc1 (σAc1 b)))) =
      gsumCoeff ((SA).blockSplit 1 hp).μ
        (commonLabels (thickLabels I.𝒴 I.dom) hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
        (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
            hp0 (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
          hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
        (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
        (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ) T := by
  classical
  obtain ⟨hnF, -, -, -⟩ := gapMargins_of_width hL2 le_rfl hm₁ hw hn20
  obtain ⟨hnF', -, -, -⟩ := gapMargins_of_width hL2 le_rfl hm₁ hw hn20'
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hef : (L - 1) * cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have htA : ∀ μ, L ^ ((k + 1) + 1 + m₁) ∣ (tAz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + 1 + m₁) ∣ (tBz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have hnL : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnL' : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  -- the labels with blocks in `T` lie in the recentred box
  have hyR : ∀ y : {Y // Y ∈ I.𝒴}, blocksOf 1 (k + 1) Set.univ y.1 ⊆ T →
      ∀ x ∈ y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) := by
    intro y hy x hx
    have hDj := I.dom y.1 y.2
    have hs := sitesOf_blocksOf hN (le_refl (k + 1)) isPiUnion_univ_aux hDj.2.1
    have hx' : x ∈ sitesOf (blocksOf 1 (k + 1) Set.univ y.1) := by rw [hs]; exact ⟨hx, trivial⟩
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx'
    exact hT b (hy hb) x hxb
  -- the domains of the recentred box correspond
  have hmem𝒴 : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz)) →
      ((fun x => bm (x + tAz) - tBz) '' Y ∈ I'.𝒴 ↔ Y ∈ I.𝒴) := by
    intro Y hY
    rw [hI𝒴, hI𝒴']
    exact mem_obsLabelDomains_recentred_iff (by omega) hGA hGB hN hN' tAz tBz htA htB hnO hnO' Y hY
  refine gsumCoeff_e1_recentred_of_domainLabels hN2 hk νS β p₁ δ hC hC' hGA hGB hMX hmar hαK hsm
    hF₁ hF₁' hSol hSol' hd hN hN' hm₁ zv hz z hw hn20 hn20' hzc hroot θ θ' hθ hθ' hraw hρ hp hp'
    hum hGdep hL2 hdom hdom' (thickLabels I.𝒴 I.dom) (thickLabels I'.𝒴 I'.dom)
    (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0
    (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0
    (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
      hp0 (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
    (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
      hp0 (by linarith) hεU (by linarith) hKc) 2 (by norm_num)) T hT
    (fun y hy => ⟨(fun x => bm (x + tAz) - tBz) '' y.1, (hmem𝒴 y.1 (hyR y hy)).2 y.2⟩) ?_ ?_ ?_ ?_
  · intro y hy
    exact blocksOf_recentred hN hN' tAz tBz htA htB (by omega) (by omega) (hyR y hy)
  · intro y₁ hy₁ y₂ hy₂ h
    exact Subtype.ext (image_recentred_inj (by omega) tAz tBz (hyR y₁ hy₁) (hyR y₂ hy₂)
      (congrArg Subtype.val h))
  · intro y' hy'
    obtain ⟨Y, hYR, hYimg, hYT⟩ := preimage_recentred hN hN' tAz tBz htA htB hnL hnL' hT
      (I'.dom y'.1 y'.2) hy'
    exact ⟨⟨Y, (hmem𝒴 Y hYR).1 (by rw [hYimg]; exact y'.2)⟩, hYT, Subtype.ext hYimg⟩
  · intro s hs y hy Φ Φ' hR
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    rw [zeroSourceAct_H, zeroSourceAct_H]
    congr 1
    refine labelActZero_recentred hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm hd hL2 le_rfl hm₁ hN hN'
      zv hz _ _ rfl rfl hn20 hn20' hnF hnF' cc hcψ hρc hrad hF₂ hF₂' hSol₂ hSol₂' hp hp'
      (thickLabels I.𝒴 I.dom) (thickLabels I'.𝒴 I'.dom) _ _
      (V := {e : physParam N (SA) | ((e.1, 0) : physParam N (SA)) ∈ V})
      (V' := {e : physParam N (SB) | ((e.1, 0) : physParam N (SB)) ∈ V'})
      (fun e he σ hσ l Φ₀ => ?_) (fun e he σ hσ l Φ₀ => ?_) θ θ' hV hV' hθ hθ' hraw hs1 y _
      (hyR y hy) rfl Φ Φ' hR
    · rw [labelActFamilyOn_H (SA) 1 _ hF hN hp0 _ hεU _ hKc he (by linarith : ‖σ‖ < Rσ)]
      have hJ : physInclScaled N (SA) cJ ((e.1, 0) : physParam N (SA)) =
          ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), 0) := by
        rw [physInclScaled_apply]
        refine Prod.ext rfl ?_
        funext x i
        simp
      rw [hJ, hIT]
      rfl
    · rw [labelActFamilyOn_H (SB) 1 _ hF' hN' hp0 _ hεU _ hKc he (by linarith : ‖σ‖ < Rσ)]
      have hJ : physInclScaled N (SB) cJ' ((e.1, 0) : physParam N (SB)) =
          ((e.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), 0) := by
        rw [physInclScaled_apply]
        refine Prod.ext rfl ?_
        funext x i
        simp
      rw [hJ, hIT']
      rfl

end CoefRec

end Balaban.Polymer.TwoTorusStep
