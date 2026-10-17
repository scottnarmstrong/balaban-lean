/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapIdent

/-!
# The torus clause for the marked block-energy term at the gap scale (item 24, blocker 7)

`evDec_boxMap_blockEnergy` is `evDec_boxMap_of_diameter` for the block functionals of the step, the
block energies `blockEnergyFun` of the block of `x₀` on the first torus and of the block of `bm x₀`
on the second: the hypotheses `hΦan`, `hfamΦ` are discharged (`blockEnergyFun_analytic`,
`hfamΦ_blockEnergy`), the remaining ones are the data correspondence `hfamD` and the read margin of
the block.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section RecentredBlock

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv
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
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)

variable
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))

variable {m₀ j : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hX' : X₁f' = X₁f.image bm)
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    (h𝒦 : 𝒦X.Nonempty)

variable {Ds q : ℕ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hDs : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), ∀ y ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y,
      ∀ μ, |(x μ - y μ).valMinAbs| ≤ Ds)
    (hn25 : 25 * Ds + 25 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn25' : 25 * Ds + 25 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hq : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ, |(x μ).valMinAbs| ≤ q)
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))


    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)

variable
    (hfamD : ∀ z : Fin d → ℤ, (∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
          (rawOf D')) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
        ∀ i, ψh' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = ψh (unitPt hGA y, i)) ∧
      (∀ y, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
          (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
        (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) ∈ Zm' ↔
          unitPt hGA y ∈ Zm)))

variable {x₀ : CTorus d L N₁ m₁ (k + 1)}
    (hZ : readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) ⊆ ↑X₁f)
    (hBM : BlockMargin (GA) X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) :
        Set (CTorus d L N₁ m₁ (k + 1))))
    (hnE : 2 * ((Ds + (Ds + 1) / 4) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * ((Ds + (Ds + 1) / 4) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))

include hC hC' hk hGA hGB hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL hm₀ hm₁ hN hN' hX'
  hcov hX₁ hcov' hX₁' h𝒦 hDs hn25 hn25' hq hqn hD hD' hψh hψh' hum hfamD hZ hBM hnE hnE'

/-- **The torus clause for the marked block-energy term at a compact support** (item 24, part 1):
`evDec_boxMap_of_diameter` for the block energy `blockEnergyFun` of the block of `x₀` (first torus)
and of the block of `bm x₀` (second torus).  The sites read by the block lie in the read region
(`hZ`), the block has the margin against the cover (`hBM`), and `hnE`, `hnE'` are the margins of the
correspondence of the block energies. -/
theorem evDec_boxMap_blockEnergy :
    evDec X₁f' m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k
          (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀))) Zm' um tm (bm '' Y)
        (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k
          (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) Zm um tm Y (rawOf D, ψh) :=
  evDec_boxMap_of_diameter hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL hm₀
    hm₁ hN hN' hX' hcov hX₁ hcov' hX₁' h𝒦 hDs hn25 hn25' hq hqn
    ((blockEnergyFun_analytic _ _ _ _).mono (Set.subset_univ _))
    ((blockEnergyFun_analytic _ _ _ _).mono (Set.subset_univ _)) hD hD' hψh hψh' hum hfamD
    (fun z hz hint SA SmA SB SmB =>
      hfamΦ_blockEnergy hk hN hN' _ _ hZ hBM hnE hnE' z hz hint SA SmA SB SmB)

end RecentredBlock

end Balaban.Polymer.TwoTorusStep
