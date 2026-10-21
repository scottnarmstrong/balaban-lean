/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEv
public import Balaban.Polymer.ETermFunTransport
public import Balaban.Polymer.LevelGSCorr

/-!
# The coefficients of a localized old term on two tori

`evDec_oldTerm_twoTorus`: the coefficients `evDec` of the localized old term
`eTermFun … Fk E` (the old term `E` as a functional of the decoupled objects) of the whole-lattice
generating sets of two tori agree, when the old terms agree on raw data that agree under the box
map on the label margin `Z` (the box form of the torus independence of the small-field data;
discharged by the inherited D8 of `sfSucc_core`), the localized sets `Gk`, `Gj` correspond on `Z`
and `Gk` is isomorphic to `Gk'` there (`GSIso`).  It is `evDec_twoTorus_core` with
`Φ = eTermFun …` and the hypothesis `hΦ` supplied by `eTermFun_twoTorus`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background Matrix

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ₁ ϱ₁' ϱ₂ ϱ₂' : ℝ}

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

/-- **The coefficients of a localized old term on two tori.** -/
theorem evDec_oldTerm_twoTorus
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
    {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {Gk' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₁'}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {Gj' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₂'}
    {r₀ δ₃ δfl : ℝ} {jj : ℕ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X₀' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hB : BgSetting N (GA) Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f jj)
    (hF : FlSetting N (GA) Gk (HA) a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hB' : BgSetting N (GB) Gk' Gj' a₁ ν c BG κ r₀ eps δ₃ X₀' (X₁f.image bm) jj)
    (hF' : FlSetting N (GB) Gk' (HB) a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f.image bm))
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    {Fk' : RawData d L (N₁' * L ^ m₁) (k + 1) N → (Gk'.Ω 1 × Fin N → ℂ) × (Gk'.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (hFk' : ∀ D : BgData Gk' N, InUnionDomainC Gk' (bgC0 d L N) (bgC1 d L N) ν D →
      Fk' (rawOf D) = (bgFieldC Gk' (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk' (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    (E' : RawData d L (N₁' * L ^ m₁) (k + 1) N → ℂ)
    {Z : Set (CTorus d L N₁ m₁ (k + 1))} (hZX : Z ⊆ ↑X₁f) (hBMZ : BlockMargin (GA) X₁f Z)
    (hGk : GSCorr Gk Gk' bm Z) (hGj : GSCorr Gj Gj' bm Z)
    (hiso : GSIso (compWeight L a₁) ν Gk Gk' bm Z)
    (hblk : ∀ z ∈ Z, z ∈ Gk.Ω 1 →
      (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ Z) ∧ (∀ y ∈ (GA).blk ((GA).layerIndex z) z, y ∈ Z) ∧
      (∀ y ∈ (HA).blk ((HA).layerIndex z) z, y ∈ Z))
    (hblk2 : ∀ z ∈ Z, z ∈ Gj.Ω 1 →
      (∀ y ∈ Gj.blk (Gj.layerIndex z) z, y ∈ Z) ∧ (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ Z))
    (hE : ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) → E' r' = E r)
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => (eTermFun (GA) Gk Gj (HA) (compWeight L a₁) Fk E) t.1 t.2.1 t.2.2)
      (FlReal (GA) (HA) a₁ ν BG κ eps X₁f BG₂ δ₁))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (X₁f.image bm) m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol' (eTermFun (GB) Gk' Gj' (HB) (compWeight L a₁) Fk' E') Zm' um tm (bm '' Y) (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol (eTermFun (GA) Gk Gj (HA) (compWeight L a₁) Fk E) Zm um tm Y (rawOf D, ψh) := by
  classical
  have hL1 : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have hLk : L ^ k ≤ L ^ (k + 1) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ k)
  have hZR : ∀ z ∈ Z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z :=
    fun z hz => hX₁R z (Finset.mem_coe.1 (hZX hz))
  have hGp : GSCorr (GA) (GB) bm Z :=
    (gsCorr_levelGS (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
      (j := k + 1) (Nat.le_add_left 1 k) le_rfl (ρ := R) (by omega) (by omega)).mono
      fun z hz => hZR z hz
  have hHm : GSCorr (HA) (HB) bm Z :=
    (gsCorr_levelGS (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
      (j := k) hk (Nat.le_succ k) (ρ := R) (by omega) (by omega)).mono
      fun z hz => hZR z hz
  refine evDec_twoTorus_core (Φ := eTermFun (GA) Gk Gj (HA) (compWeight L a₁) Fk E)
    (Φ' := eTermFun (GB) Gk' Gj' (HB) (compWeight L a₁) Fk' E') (Rα := ∅) (Rδ := Z) (Rψ := Z)
    (Rφ := Z) (Rθ := Z) (hBM := fun x hx => absurd hx (Set.notMem_empty x)) (hRδ := hZX)
    (hRψ := hZX) (hBMφ := hBMZ) (hRθ := hZX) ?_ (hC := hC) (hC' := hC') (hk := hk) (hGA := hGA) (hGB := hGB) (cc := cc) (hcψ := hcψ) (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (hF₁ := hF₁) (hF₁' := hF₁') (hSol := hSol) (hSol' := hSol') (hcov := hcov) (hX₁ := hX₁) (hcov' := hcov') (hX₁' := hX₁') (hX₁R := hX₁R) (hYR := hYR) (hn := hn) (hn' := hn') (hnS := hnS) (hnS' := hnS') (hnF := hnF) (hnF' := hnF') (hΦan := hΦan) (hD := hD) (hD' := hD') (hraw := hraw) (hψh := hψh) (hψh' := hψh') (hhat := hhat) (hZm := hZm) (hum := hum)
  intro t t' ht ht' _ h2 h3 h4 h5
  exact eTermFun_twoTorus hB hF hB' hF' hFk hFk' E E' (σ := bm) (R := Z) hGk hGp hHm hGj hiso
    hblk hblk2 hE ht ht'
    (fun y hy hy1 hy2 i => h4 ⟨y, hy1⟩ ⟨bm y, hy2⟩ hy rfl i)
    (fun y hy hy1 hy2 i => h2 ⟨y, hy1⟩ ⟨bm y, hy2⟩ hy rfl i)
    (fun y hy => h5 y hy) (fun y hy => h3 y hy)

end Balaban.Polymer.TwoTorusStep
