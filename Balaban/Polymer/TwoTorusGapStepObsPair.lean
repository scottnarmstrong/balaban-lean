/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsCoef
public import Balaban.Polymer.TwoTorusGapStepDetPair
public import Balaban.Polymer.TwoTorusGapObsRecentreIdx

/-!
# The coefficient of the observable at the cells of a polymer: the pair theorem (item 24, blocker 7)

`obsCoeffParam_cellSites`: the analogue of `sum_blockU_detActivityBg_cellSites` for the coefficient of
the observable.  The region of the site `xs` and the sites of the cubes `Y` of the cells of a polymer
lie within a window of spread `Ds` and within `q` of the origin; a recentring vector `z` (from
`exists_recentring_int`) carries the window into the box of radius `Ds + (Ds + 1) / 4`, the recentring
map `bm (x + z) - z` is `bm` on the window, and the coefficients on the two tori agree
(`obsCoeffParam_recentred_of_labelActs`), the cubes `Y'` of the second torus being the box-map image
of `Y`.  The data correspond for every admissible recentring vector (`hraw`, `hmemV`, `hAeq0`,
`hAeqθ`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv

section CellSites

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
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
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : (SB).U)
set_option hygiene false in
local notation "σAc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tA)
set_option hygiene false in
local notation "σBi" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tB)⁻¹
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ (bm xs)) : Set (CTorus d L N₁' m₁ (k + 1)))
set_option hygiene false in
local notation "𝒴A" => polyDom (GA) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs)
set_option hygiene false in
local notation "𝒴B" => polyDom (GB) (LocalCover.nbhdF m₀ (bm xs)) m₀ k (LocalCover.fam m₀ (bm xs))

/-- **The coefficient of the observable at the cells of a polymer on two tori.** -/
theorem obsCoeffParam_cellSites (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    -- the geometry
    {Ds q : ℕ} (hDsa : L * aK ≤ Ds + 1)
    (hn25 : 25 * Ds + 25 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hqn : 2 * q + 2 * (Ds + (Ds + 1) / 4) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack : 20 * (Ds + (Ds + 1) / 4) + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hslack' : 20 * (Ds + (Ds + 1) / 4) + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hbm : bm '' sitesOf Y = sitesOf Y')
    (xs : CTorus d L N₁ m₁ (k + 1)) (iy : Fin N)
    (hsp : ∀ x ∈ LocalCover.nbhd m₀ xs, ∀ y ∈ LocalCover.nbhd m₀ xs ∪ sitesOf Y, ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ Ds)
    (hqS : ∀ x ∈ LocalCover.nbhd m₀ xs ∪ sitesOf Y, ∀ μ, |(x μ).valMinAbs| ≤ q)
    -- the site and the terms of its expansion
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 < cψ) (hq : p₁ / cψ ≤ 1 / 4)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    (hEv : Ev = evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ xs))
        (fun u s => siteFun (GA) (HA) xs iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) 1 νS (SA).hG' cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) 1 νS (SA).hG' cc F₁
            (extParams (GA) (XA) s) u.1 u.2)))
    (hEv' : Ev' = evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm xs)))
        (fun u s => siteFun (GB) (HB) (bm xs) iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) 1 νS (SB).hG' cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) 1 νS (SB).hG' cc F₁'
            (extParams (GB) (XB) s) u.1 u.2)))
    (hdEv : ∀ Y ∈ 𝒴A, ∀ u ∈ XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps ×ˢ
        {ψh : (SA).U × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir (SA).hG' Y u u' → Ev Y u = Ev Y u')
    (hdj : ∀ Y ∈ 𝒴A, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴B, IsDj m₀ (k + 1) Y)
    -- the parameters
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ xs ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
        (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {Lb Lb' : Type} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴v : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    {𝒴v' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴v}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴v'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmemV : ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ xs ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ Z : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Z, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) → ((fun x => bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) '' Z ∈ 𝒴v' ↔ Z ∈ 𝒴v))
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N (SA) → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N (SB) → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0' : aEnt d L + 1 ≤ κ0') (hεH : 0 ≤ εH) (hεH' : 0 ≤ εH')
    {Kobs Kobs' : ℝ} (hK : Kco + Kco + K0 d L κ0 + K0 d L κ0 ≤ Kobs)
    (hK' : Kco' + Kco' + K0 d L κ0' + K0 d L κ0' ≤ Kobs')
    (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    (hAeq0 : ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ xs ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) →
      Lab'.ysite l' = (fun x => bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))))
          ⟨unitPt (SB).hG' (bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' ((θ'.1, 0) : physParam N (SB)) σ).H l' Φ' = (A ((θ.1, 0) : physParam N (SA)) σ).H l Φ)
    (hAeqθ : ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ LocalCover.nbhd m₀ xs ∪ sitesOf Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) →
      Lab'.ysite l' = (fun x => bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))))
          ⟨unitPt (SB).hG' (bm (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) - (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' θ' σ).H l' Φ' = (A θ σ).H l Φ) :
    obsCoeffParam ((SB).blockSplit m₀ hp').μ
        (fun θ t σ => tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ t σ)
        (fun m => obsY1 m₀ (SB) (Lb' ⊕ Lb') (𝒴B) m)
        (fun m => blockMarkC (SB) m₀ hp' m.1 m.2)
        (fun θ m T'' => obsHker (𝒴B) (fun Y => hatCoeff (Ev' Y)
          (θ.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) (obsUnitVec (SB) m)) m₀ T'')
        (obsRemLab (𝒴B) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ (Lb' ⊕ Lb') (𝒴B) (rootCube (m₀ := m₀) (blockIndex (bm xs)))))
        (fun θ => obsGrFam (SB) m₀ hp' Ev' (𝒴B)
          (XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps) θ) θ' Y' =
      obsCoeffParam ((SA).blockSplit m₀ hp).μ
        (fun θ t σ => tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ t σ)
        (fun m => obsY1 m₀ (SA) (Lb ⊕ Lb) (𝒴A) m)
        (fun m => blockMarkC (SA) m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker (𝒴A) (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec (SA) m)) m₀ T'')
        (obsRemLab (𝒴A) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 m₀ (Lb ⊕ Lb) (𝒴A) (rootCube (m₀ := m₀) (blockIndex xs))))
        (fun θ => obsGrFam (SA) m₀ hp Ev (𝒴A)
          (XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps) θ) θ Y := by
  classical
  have hapos : 0 < aK := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have : NeZero aK := ⟨hapos.ne'⟩
  have hLK : L ^ (k + 1) ≤ aK := by
    unfold cellSide
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hbox : ∃ b, box b (L * aK) ⊆ LocalCover.nbhd m₀ xs :=
    ⟨_, fun x hx => box_mono _ (by omega : L * aK ≤ (L - 1) * aK + L * aK) hx⟩
  obtain ⟨zv, hz, hint⟩ := exists_recentring_int (n := (N₁ * L ^ m₁) * L ^ (k + 1)) (a := aK)
    (L := L) (D := Ds) (q := q) hd hapos hL (cellSide_dvd hN le_rfl) hbox hsp hn25 hqS hqn
  have hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hxsin : xs ∈ LocalCover.nbhd m₀ xs := by
    have := LocalCover.mem_nbhdF_self m₀ xs
    rwa [← Finset.mem_coe, LocalCover.coe_nbhdF] at this
  have hbd : ∀ y ∈ sitesOf Y, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y + fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
    fun y hy => inBox_add_intCast hnR y zv (hint y (Or.inr hy))
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣
      ((fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣
      ((fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have hYc := cubeAct_recentred_cells hN hN' _ _ htA htB Y Y' hbm
    (fun y hy => boxMap_add_intCast hnR y zv (hint y (Or.inr hy))) hbd (by omega)
  have hσB := genSymm_mem_pavingSymGroup
    (GenSymm.translate (n := k + 1) (m₀ := m₀)
      (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) htB)
  have hinv : ∀ b, Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
      (K := k + 1) (m₀ := m₀)
      (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))⁻¹
      (Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1)
        (m₀ := m₀)
        (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) b) = b :=
    fun b => cubeMap_inv hN' hσB b
  have hY'eq : Y' = Y.image (fun b => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁')
      (m₁ := m₁) (K := k + 1) (m₀ := m₀)
      (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))⁻¹
      (cubeMap hN hN' le_rfl (Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) (m₀ := m₀)
        (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) b))) := by
    have h1 := congrArg (Finset.image (Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁')
      (m₁ := m₁) (K := k + 1) (m₀ := m₀)
      (Equiv.addRight (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))⁻¹)) hYc
    simp only [cubeAct, Finset.image_image, Function.comp_def, hinv, Finset.image_id'] at h1
    rw [h1]
  rw [hY'eq]
  exact obsCoeffParam_recentred_of_labelActs hN2 hk νS β p₁ δ hC hC' hMX hmar hαK hsm
    (R := Ds + (Ds + 1) / 4) hd hL hm₀ hm₁ hN hN' zv hz _ _ rfl rfl (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) xs (bm xs) iy
    (boxMap_add_intCast hnR xs zv (hint xs (Or.inl hxsin))).symm
    (fun x hx => inBox_add_intCast hnR x zv (hint x (Or.inl hx))) cc hcψ hq hrad hF₁ hF₁' hSol
    hSol' hEv hEv' hdEv hdj hdj' θ θ' hθ hθ' (hraw zv hz hint) hp hp' Y
    (fun b hb x hx => hbd x (mem_sitesOf.2 ⟨b, hb, hx⟩)) Lab Lab' ys ys' hys hys'
    (hmemV zv hz hint) A A' hκ0 hκ0' hεH hεH' hK hK' Rg hR 𝒰 (hAeq0 zv hz hint) (hAeqθ zv hz hint)

end CellSites

end Balaban.Polymer.TwoTorusStep
