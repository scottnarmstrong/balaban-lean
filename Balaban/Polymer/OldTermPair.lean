/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusEvOldGen
public import Balaban.Polymer.ETermFunTransport
public import Balaban.Polymer.LevelGSCorr

/-!
# The premises of the old-term coefficient comparison as a structure

`evDec_oldTerm_twoTorus_of_eq` restates `evDec_oldTerm_twoTorus` with the generating sets as bound
variables and the hypotheses `GA' = levelGS (k+1)` etc.; the proof substitutes.  It applies to the
generating set `S.G'` of a step setting that is definitionally `levelGS`.
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

/-- **The premises of `evDec_oldTerm_twoTorus_of_eq` at one pair of old terms** (typing data, the
smallness and margin hypotheses, and the agreement of the old terms on raw data agreeing on the label
margin: the box form of D8, discharged by `sfSucc_core`'s inherited D8). -/
structure OldTermPair
  (GA' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (GB' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ)
  (HA' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (HB' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ)
  (a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ)
  (cc : ℂ)
  (cψ : ℝ)
  (δc : ℝ)
  (F₁ : DecParams GA' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (GA'.Ω 1 × Fin N → ℂ) × (GA'.Ω 1 → ℂ))
  (F₁' : DecParams GB' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (GB'.Ω 1 × Fin N → ℂ) × (GB'.Ω 1 → ℂ))
  (Sol : Dec2.DecParams (coverOf GA') × Edat HA' N → (HA'.Ω 1 × Fin N → ℂ) × (HA'.Ω 1 → ℂ))
  (Sol' : Dec2.DecParams (coverOf GB') × Edat HB' N →
      (HB'.Ω 1 × Fin N → ℂ) × (HB'.Ω 1 → ℂ))
  (m₀ j : ℕ)
  (X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)))
  (X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1)))
  (X₁f : Finset (CTorus d L N₁ m₁ (k + 1)))
  (Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
  (Gk' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₁')
  (Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
  (Gj' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₂')
  (r₀ δ₃ δfl : ℝ)
  (jj : ℕ)
  (X₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
  (X₀' : Finset (CTorus d L N₁' m₁ (k + 1)))
  (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
  (Fk' : RawData d L (N₁' * L ^ m₁) (k + 1) N → (Gk'.Ω 1 × Fin N → ℂ) × (Gk'.Ω 1 → ℂ))
  (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
  (E' : RawData d L (N₁' * L ^ m₁) (k + 1) N → ℂ)
  (Z : Set (CTorus d L N₁ m₁ (k + 1)))
  (R : ℕ)
  (Y : Set (CTorus d L N₁ m₁ (k + 1)))
  (D : BgData GA' N)
  (D' : BgData GB' N)
  (ψh : unitPts GA' × Fin N → ℂ)
  (ψh' : unitPts GB' × Fin N → ℂ)
  (Zm : Finset (unitPts GA'))
  (Zm' : Finset (unitPts GB'))
  (um tm : ℂ) : Prop where
  eGA : GA' = GA
  eGB : GB' = GB
  eHA : HA' = HA
  eHB : HB' = HB
  hC : FlCore N GA' HA' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁
  hC' : FlCore N GB' HB' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁
  hk : 1 ≤ k
  hGA : IsLevel GA' (k + 1)
  hGB : IsLevel GB' (k + 1)
  hcψ : 0 ≤ cψ
  hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc
  hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2
  hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4
  hF₁ : ∀ (s : DecParams GA') (D : BgData GA' N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC GA' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : GA'.Ω 1 × Fin N → ℂ)
          (α : GA'.Ω 1 → ℂ), IsDecBg GA' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α)
  hF₁' : ∀ (s : DecParams GB') (D : BgData GB' N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC GB' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : GB'.Ω 1 × Fin N → ℂ)
          (α : GB'.Ω 1 → ℂ), IsDecBg GB' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α)
  hSol : ∀ p : Dec2.DecParams (coverOf GA') × Edat HA' N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
        StrictDataM HA' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
          (Sol p).1 = dphi HA' (Dec2.decG (coverOf GA') HA' (compWeight L a₁) ν p.1) p.2.2.1
            p.2.1 (pertSource HA' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
          Dec2.DecFixed (coverOf GA') HA' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource HA' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
          Small HA' (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
          Small HA' (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
          SupBounds HA' (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
          (∀ δα' : HA'.Ω 1 → ℂ, Small HA' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf GA') HA' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource HA' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)
  hSol' : ∀ p : Dec2.DecParams (coverOf GB') × Edat HB' N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
        StrictDataM HB' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
          (Sol' p).1 = dphi HB' (Dec2.decG (coverOf GB') HB' (compWeight L a₁) ν p.1) p.2.2.1
            p.2.1 (pertSource HB' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
          Dec2.DecFixed (coverOf GB') HB' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource HB' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
          Small HB' (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
          Small HB' (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
          SupBounds HB' (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
          (∀ δα' : HB'.Ω 1 → ℂ, Small HB' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
            Dec2.DecFixed (coverOf GB') HB' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
              (pertSource HB' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2)
  hcov : CovSetup GA' m₀ j X 𝒦X
  hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 GA' m₀ j 𝒦X
  hcov' : CovSetup GB' m₀ j X' 𝒦X'
  hX₁' : (↑(X₁f.image bm) : Set (CTorus d L N₁' m₁ (k + 1))) = X1 GB' m₀ j 𝒦X'
  hB : BgSetting N GA' Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f jj
  hF : FlSetting N GA' Gk HA' a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f
  hB' : BgSetting N GB' Gk' Gj' a₁ ν c BG κ r₀ eps δ₃ X₀' (X₁f.image bm) jj
  hF' : FlSetting N GB' Gk' HB' a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f.image bm)
  hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
        Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D)
  hFk' : ∀ D : BgData Gk' N, InUnionDomainC Gk' (bgC0 d L N) (bgC1 d L N) ν D →
        Fk' (rawOf D) = (bgFieldC Gk' (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gk' (compWeight L a₁) ν (bgC0 d L N) D)
  hZX : Z ⊆ ↑X₁f
  hBMZ : BlockMargin GA' X₁f Z
  hGk : GSCorr Gk Gk' bm Z
  hGj : GSCorr Gj Gj' bm Z
  hiso : GSIso (compWeight L a₁) ν Gk Gk' bm Z
  hblk : ∀ z ∈ Z, z ∈ Gk.Ω 1 →
        (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ Z) ∧ (∀ y ∈ GA'.blk (GA'.layerIndex z) z, y ∈ Z) ∧
        (∀ y ∈ HA'.blk (HA'.layerIndex z) z, y ∈ Z)
  hblk2 : ∀ z ∈ Z, z ∈ Gj.Ω 1 →
        (∀ y ∈ Gj.blk (Gj.layerIndex z) z, y ∈ Z) ∧ (∀ y ∈ Gk.blk (Gk.layerIndex z) z, y ∈ Z)
  hE : ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
        (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) → E' r' = E r
  hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x
  hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y
  hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)
  hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1)
  hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1)
  hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1)
  hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1)
  hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1)
  hΦan : AnalyticOnNhd ℂ (fun t => (eTermFun GA' Gk Gj HA' (compWeight L a₁) Fk E) t.1 t.2.1 t.2.2)
        (FlReal GA' HA' a₁ ν BG κ eps X₁f BG₂ δ₁)
  hD : XiCData GA' (compWeight L a₁) ν (k + 1) 1 eps D
  hD' : XiCData GB' (compWeight L a₁) ν (k + 1) 1 eps D'
  hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
        (rawOf D) (rawOf D')
  hψh : ∀ p, ‖ψh p‖ ≤ cψ
  hψh' : ∀ p, ‖ψh' p‖ ≤ cψ
  hhat : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        ∀ i, ψh' (unitPt hGB (bm x), i) = ψh (unitPt hGA x, i)
  hZm : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        (unitPt hGB (bm x) ∈ Zm' ↔ unitPt hGA x ∈ Zm)
  hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁

/-- The coefficients of the localized old terms of the pair agree. -/
theorem evDec_oldTerm_of_pair
  {GA' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {GB' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ}
  {HA' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {HB' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
  {cc : ℂ}
  {cψ : ℝ}
  {δc : ℝ}
  {F₁ : DecParams GA' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (GA'.Ω 1 × Fin N → ℂ) × (GA'.Ω 1 → ℂ)}
  {F₁' : DecParams GB' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (GB'.Ω 1 × Fin N → ℂ) × (GB'.Ω 1 → ℂ)}
  {Sol : Dec2.DecParams (coverOf GA') × Edat HA' N → (HA'.Ω 1 × Fin N → ℂ) × (HA'.Ω 1 → ℂ)}
  {Sol' : Dec2.DecParams (coverOf GB') × Edat HB' N →
      (HB'.Ω 1 × Fin N → ℂ) × (HB'.Ω 1 → ℂ)}
  {m₀ j : ℕ}
  {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
  {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
  {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gk' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₁'}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Gj' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ₂'}
  {r₀ δ₃ δfl : ℝ}
  {jj : ℕ}
  {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {X₀' : Finset (CTorus d L N₁' m₁ (k + 1))}
  {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
  {Fk' : RawData d L (N₁' * L ^ m₁) (k + 1) N → (Gk'.Ω 1 × Fin N → ℂ) × (Gk'.Ω 1 → ℂ)}
  {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
  {E' : RawData d L (N₁' * L ^ m₁) (k + 1) N → ℂ}
  {Z : Set (CTorus d L N₁ m₁ (k + 1))}
  {R : ℕ}
  {Y : Set (CTorus d L N₁ m₁ (k + 1))}
  {D : BgData GA' N}
  {D' : BgData GB' N}
  {ψh : unitPts GA' × Fin N → ℂ}
  {ψh' : unitPts GB' × Fin N → ℂ}
  {Zm : Finset (unitPts GA')}
  {Zm' : Finset (unitPts GB')}
  {um tm : ℂ}
    (P : OldTermPair GA' GB' HA' HB' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ cc cψ δc F₁ F₁' Sol Sol' m₀ j X 𝒦X X' 𝒦X' X₁f Gk Gk' Gj Gj' r₀ δ₃ δfl jj X₀ X₀' Fk Fk' E E' Z R Y D D' ψh ψh' Zm Zm' um tm) :
    evDec (X₁f.image bm) m₀ j 𝒦X' a₁ ν P.hGB cc F₁' Sol' (eTermFun GB' Gk' Gj' HB' (compWeight L a₁) Fk' E') Zm' um tm (bm '' Y) (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν P.hGA cc F₁ Sol (eTermFun GA' Gk Gj HA' (compWeight L a₁) Fk E) Zm um tm Y (rawOf D, ψh) := by
  exact evDec_oldTerm_twoTorus_of_eq (eGA := P.eGA) (eGB := P.eGB) (eHA := P.eHA) (eHB := P.eHB) (hC := P.hC) (hC' := P.hC') (hk := P.hk) (hGA := P.hGA) (hGB := P.hGB) (hcψ := P.hcψ) (hMX := P.hMX) (hmar := P.hmar) (hαK := P.hαK) (hsm := P.hsm) (hF₁ := P.hF₁) (hF₁' := P.hF₁') (hSol := P.hSol) (hSol' := P.hSol') (hcov := P.hcov) (hX₁ := P.hX₁) (hcov' := P.hcov') (hX₁' := P.hX₁') (hB := P.hB) (hF := P.hF) (hB' := P.hB') (hF' := P.hF') (hFk := P.hFk) (hFk' := P.hFk') (hZX := P.hZX) (hBMZ := P.hBMZ) (hGk := P.hGk) (hGj := P.hGj) (hiso := P.hiso) (hblk := P.hblk) (hblk2 := P.hblk2) (hE := P.hE) (hX₁R := P.hX₁R) (hYR := P.hYR) (hn := P.hn) (hn' := P.hn') (hnS := P.hnS) (hnS' := P.hnS') (hnF := P.hnF) (hnF' := P.hnF') (hΦan := P.hΦan) (hD := P.hD) (hD' := P.hD') (hraw := P.hraw) (hψh := P.hψh) (hψh' := P.hψh') (hhat := P.hhat) (hZm := P.hZm) (hum := P.hum)

end Balaban.Polymer.TwoTorusStep
