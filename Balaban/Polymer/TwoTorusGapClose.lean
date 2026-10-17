/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapCloseSym
public import Balaban.Polymer.TwoTorusGapCloseCoef
public import Balaban.Polymer.TwoTorusGapAssembly

/-!
# The gap-scale closeness for compact supports, the step with no inherited terms (item 24)

`hFclose` of `resum_gapScale_torus` (`TwoTorusGapAssembly`) asks, for a support `X` of the quarter box
of the step torus `ℓ` that is not wide, the closeness of the term on `ℓ` and on the canonical torus
`can X`.  For `X = Y(C)` of cyclic spread `D`, with `25 D + 25` below both torus sides
(`compact_margin`), `evTerm_boxMap_of_diameter_of_coef` (`TwoTorusRecentre`) gives the equality of the
two terms once the coefficients of the step functional correspond on the families that match under
the recentred map `φ x = bm (x + tA) - tB`.

This file proves that correspondence for the marked functional `FFmarked` of the decoupled expansion
(the functional of the block energy terms, `evDec`), from the landed transport between two tori
(`coef_FFmarked_twoTorus`, the coefficient form of `evDec_twoTorus`) and the translation covariance of
the marked functional (`TwoTorusGapCloseSym`).

-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Recentred

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

variable
    {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))}
    {X₁f X₁fT : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X₁f' X₁fT' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hXT : X₁fT = X₁f.image (Equiv.addRight tA))
    (hX' : X₁f' = X₁f.image (fun x => bm (x + tA) - tB))
    (hXT' : X₁fT' = X₁fT.image bm)
    (hcov : CovSetup (GA) m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j X' 𝒦X')
    (hX₁' : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j 𝒦X')
    (SA : LatSymm (GA) (GA) (Equiv.addRight tA)) (SmA : LatSymm (HA) (HA) (Equiv.addRight tA))
    (SB : LatSymm (GB) (GB) (Equiv.addRight tB)) (SmB : LatSymm (HB) (HB) (Equiv.addRight tB))

variable
    {Φ ΦT : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' ΦT' : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2) (FlReal (GA) (HA) a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦan' : AnalyticOnNhd ℂ (fun t => Φ' t.1 t.2.1 t.2.2)
      (FlReal (GB) (HB) a₁ ν BG κ eps X₁f' BG₂ δ₁))

variable
    (hΦA : ∀ (bg : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) δφ u,
      ΦT (SA.fld bg.1, SA.mul bg.2) (SmA.fld δφ) (symU (Equiv.addRight tA) u) = Φ bg δφ u)
    (hΦB : ∀ (bg : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) δφ u,
      ΦT' (SB.fld bg.1, SB.mul bg.2) (SmB.fld δφ) (symU (Equiv.addRight tB) u) = Φ' bg δφ u)
    {Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))} (hBM : BlockMargin (GA) X₁fT Rα)
    (hRδ : Rδ ⊆ ↑X₁fT) (hRψ : Rψ ⊆ ↑X₁fT)
    (hΦ : ∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
      (t' : (((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) × ((HB).Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ))),
      (∀ (y : (GA).Ω 1) (y' : (GB).Ω 1), (y : CTorus d L N₁ m₁ (k + 1)) ∈ Rα →
        (y' : CTorus d L N₁' m₁ (k + 1)) = bm (y : CTorus d L N₁ m₁ (k + 1)) →
          t'.1.2 y' = t.1.2 y) →
      (∀ (w : (HA).Ω 1) (w' : (HB).Ω 1), (w : CTorus d L N₁ m₁ (k + 1)) ∈ Rδ →
        (w' : CTorus d L N₁' m₁ (k + 1)) = bm (w : CTorus d L N₁ m₁ (k + 1)) →
        ∀ i, t'.2.1 (w', i) = t.2.1 (w, i)) →
      (∀ x ∈ Rψ, t'.2.2.2 (bm x) = t.2.2.2 x) →
      ΦT' t'.1 t'.2.1 t'.2.2 = ΦT t.1 t.2.1 t.2.2)

variable
    {R : ℕ} (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (symRaw (Equiv.addRight tA) (rawOf D)) (symRaw (Equiv.addRight tB) (rawOf D')))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) →
      ∀ i, ψh' (unitPt hGB (bm (y + tA) - tB), i) = ψh (unitPt hGA y, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) →
      (unitPt hGB (bm (y + tA) - tB) ∈ Zm' ↔ unitPt hGA y ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)

include hC hC' hk hGA hGB hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hN hN' htA htB hXT hX' hXT'
  hcov hX₁ hcov' hX₁' SA SmA SB SmB hΦan hΦan' hΦA hΦB hBM hRδ hRψ hΦ
  hX₁R hYR hn hn' hnS hnS' hD hD' hraw hψh hψh' hhat hZm hum

/-- **The coefficient correspondence of the marked step functional under the recentring map** (item 24, part 1).  Let `tA`, `tB` be translations of the two step tori by multiples of the cell side `a_{k+1}`, and let the read region `X₁f` of the first torus (a union of `π'_{k+1}`-cubes, `hX₁`, with its translate and its transport `X₁f' = φ X₁f` of the same kind, `hX₁'`) and the domain `Y` lie, after the translation by `tA`, in the centred box of radius `R` (`hX₁R`, `hYR`), under the margins of the landed transport theorems.  Assume the data on the two tori correspond under the recentred map `φ x = bm (x + tA) - tB` (`hraw`, `hhat`, `hZm`: the raw data, the hat variables and the masks agree, after the translations, under the box map `bm` on the box of radius `R + 3 L^(k+1)` resp. `R`), and that the block functionals `Φ`, `Φ'` of the two tori are transported by the translations to functionals `ΦT`, `ΦT'` (`hΦA`, `hΦB`; for the energy of the block `z` these are the energies of the blocks `z + tA`, `z' + tB`) whose reads correspond under `bm` (`hΦ`, the hypothesis of `evDec_twoTorus`).  Then the coefficients of the marked functional `FFmarked` of the second torus and of the first torus agree on the families `C`, `C'` of cut parameters that correspond under `φ`.  This is the hypothesis `_hcoef` of `evTerm_boxMap_of_diameter_of_coef`.  Proof: the functionals and their coefficients are transported by the translations (`coef_FFmarked_sym`, from the translation covariance of the background, of the fluctuation problem, of the square root and of the mask), the translated cover and read region are the translates of the originals (`covSetup_translate`, `X1_translate`), and the translated functionals are compared by `coef_FFmarked_twoTorus`. -/
theorem coef_FFmarked_recentred :
    ∀ C ∈ connFams (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (GA) m₀
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) Y,
      ∀ C' : Finset (ParIdx (GB) (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1)))),
        (∀ i ∈ C, ∃ i' ∈ C', i'.1.1 = Prod.map id (fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) i.1.1) →
        (∀ i' ∈ C', ∃ i ∈ C, i'.1.1 = Prod.map id (fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) i.1.1) →
        coef (FFmarked X₁f' a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm (rawOf D', ψh')) C' =
          coef (FFmarked X₁f a₁ ν hGA cc F₁ Sol Φ Zm um tm (rawOf D, ψh)) C := by
  classical
  subst hXT hX' hXT'
  have htA' : ∀ μ, L ^ (k + 1 + m₀ + m₁) ∣ (tA μ).val := htA
  have htB' : ∀ μ, L ^ (k + 1 + m₀ + m₁) ∣ (tB μ).val := htB
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  have hUA : UnitBlockPres (Equiv.addRight tA) := unitBlockPres_of_torusSymm (j := k) le_rfl
    (TorusSymm.ofTranslate k tA fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hUB : UnitBlockPres (Equiv.addRight tB) := unitBlockPres_of_torusSymm (j := k) le_rfl
    (TorusSymm.ofTranslate k tB fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  set CSA := CoverSymm.ofTranslate hGA tA
    (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)) with hCSA
  set BA := BlockSymm.ofTranslate hGA tA
    (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)) with hBA
  set PA := PolymerSymm.ofTranslate hGA hN tA htA with hPA
  set CSB := CoverSymm.ofTranslate hGB tB
    (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)) with hCSB
  set BB := BlockSymm.ofTranslate hGB tB
    (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)) with hBB
  set PB := PolymerSymm.ofTranslate hGB hN' tB htB with hPB
  have hXA : (↑(X₁f.image (Equiv.addRight tA)) : Set (CTorus d L N₁ m₁ (k + 1))) =
      (Equiv.addRight tA) '' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := Finset.coe_image
  have hXB : (↑((X₁f.image (Equiv.addRight tA)).image bm) : Set (CTorus d L N₁' m₁ (k + 1))) =
      (Equiv.addRight tB) '' (↑(X₁f.image (fun x => bm (x + tA) - tB)) :
        Set (CTorus d L N₁' m₁ (k + 1))) := by
    rw [Finset.coe_image, Finset.coe_image, Finset.coe_image, Set.image_image, Set.image_image]
    exact Set.image_congr (fun x _ => by simp)
  set ZmT : Finset (unitPts (GA)) := Zm.map (unitAct (GA) SA hUA).toEmbedding with hZmT
  set ZmT' : Finset (unitPts (GB)) := Zm'.map (unitAct (GB) SB hUB).toEmbedding with hZmT'
  have hZA : ∀ y, unitAct (GA) SA hUA y ∈ ZmT ↔ y ∈ Zm := fun y => by
    simp [hZmT]
  have hZB : ∀ y, unitAct (GB) SB hUB y ∈ ZmT' ↔ y ∈ Zm' := fun y => by
    simp [hZmT']
  have hFanA := analyticOnNhd_FFmarked hC hk hHA hGA cc hcψ hMX hmar hαK hsm hF₁ hSol hΦan Zm
    hum hD hψh
  have hFanB := analyticOnNhd_FFmarked hC' hk hHB hGB cc hcψ hMX hmar hαK hsm hF₁' hSol' hΦan' Zm'
    hum hD' hψh'
  have hFanT := analyticOnNhd_FFmarked_sym hC hk hHA hGA cc hcψ hMX hmar hαK hsm hF₁ hSol SA SmA
    hUA CSA BA PA hXA hΦA hZA hum hD hψh hFanA
  have e1 := coef_FFmarked_sym hC hk hHA hGA cc hcψ hMX hmar hαK hsm hF₁ hSol SA SmA
    hUA CSA BA PA hXA hΦA hZA hum hD hψh hFanA
  have e2 := coef_FFmarked_sym hC' hk hHB hGB cc hcψ hMX hmar hαK hsm hF₁' hSol' SB SmB
    hUB CSB BB PB hXB hΦB hZB hum hD' hψh' hFanB
  have hcovT := covSetup_translate SA htA' hcov
  have hX₁T : (↑(X₁f.image (Equiv.addRight tA)) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 (GA) m₀ j ((Equiv.addRight tA) '' 𝒦X) := by
    rw [hXA, hX₁, X1_translate SA htA' hcov]
  have hcovT' := covSetup_translate SB htB' hcov'
  have hX₁T' : (↑((X₁f.image (Equiv.addRight tA)).image bm) : Set (CTorus d L N₁' m₁ (k + 1))) =
      X1 (GB) m₀ j ((Equiv.addRight tB) '' 𝒦X') := by
    rw [hXB, hX₁', X1_translate SB htB' hcov']
  have hX₁RT : ∀ x ∈ X₁f.image (Equiv.addRight tA),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact hX₁R y hy
  have hYRT : ∀ y ∈ (Equiv.addRight tA) '' Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact hYR y hy
  have hDT := xiCData_sym SA hD
  have hDT' := xiCData_sym SB hD'
  have hhatT : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, (fun r : unitPts (GB) × Fin N => ψh' (((unitAct (GB) SB hUB).symm) r.1, r.2))
          (unitPt hGB (bm x), i) =
        (fun r : unitPts (GA) × Fin N => ψh (((unitAct (GA) SA hUA).symm) r.1, r.2))
          (unitPt hGA x, i) := by
    intro x hx i
    have h := hhat (x - tA) (by simpa using hx) i
    simp only [unitAct_symm_unitPt]
    simpa [sub_eq_add_neg] using h
  have hZmT : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      (unitPt hGB (bm x) ∈ ZmT' ↔ unitPt hGA x ∈ ZmT) := by
    intro x hx
    have h := hZm (x - tA) (by simpa using hx)
    simp only [hZmT, hZmT', Finset.mem_map_equiv, unitAct_symm_unitPt]
    simpa [sub_eq_add_neg] using h
  have hL3 := coef_FFmarked_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hcovT hX₁T hcovT' hX₁T' hBM hRδ hRψ hΦ hX₁RT hYRT hn hn' hnS hnS' hDT hDT' hraw
    (ψh := fun r => ψh (((unitAct (GA) SA hUA).symm) r.1, r.2))
    (ψh' := fun r => ψh' (((unitAct (GB) SB hUB).symm) r.1, r.2))
    (fun p => hψh _) (fun p => hψh' _) hhatT hZmT hum hFanT
  have key : ∀ (i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (i' : ParIdx (GB) (↑(X₁f.image (fun x => bm (x + tA) - tB)) :
        Set (CTorus d L N₁' m₁ (k + 1)))),
      i'.1.1 = Prod.map id (fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) i.1.1 →
      ((parEquiv CSB PB hXB) i').1.1 = Prod.map id bm ((parEquiv CSA PA hXA) i).1.1 := by
    intro i i' he
    have ha : ((parEquiv CSA PA hXA) i).1.1 = (i.1.1.1, i.1.1.2 + tA) := rfl
    have hb : ((parEquiv CSB PB hXB) i').1.1 = (i'.1.1.1, i'.1.1.2 + tB) := rfl
    rw [ha, hb, he]
    simp
  intro C hCm C' h1 h2
  have hCT : C.map (parEquiv CSA PA hXA).toEmbedding ∈
      connFams (fun i : ParIdx (GA) (↑(X₁f.image (Equiv.addRight tA)) :
        Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (GA) m₀
        (↑(X₁f.image (Equiv.addRight tA)) : Set (CTorus d L N₁ m₁ (k + 1)))
        ((Equiv.addRight tA) '' Y) := by
    have h := connFams_relabel (fun i : ParIdx (GA) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (fun i : ParIdx (GA) (↑(X₁f.image (Equiv.addRight tA)) :
        Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) (parEquiv CSA PA hXA) (fun _ => rfl)
      (fun i => i.1.2) PA SA (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) Y
    rw [← hXA] at h
    rw [h]
    exact Finset.mem_map_of_mem _ hCm
  refine (e2 C').symm.trans ((hL3 _ hCT _ ?_ ?_).trans (e1 C))
  · intro i hi
    obtain ⟨i0, hi0, rfl⟩ := Finset.mem_map.1 hi
    obtain ⟨i', hi', he⟩ := h1 i0 hi0
    exact ⟨parEquiv CSB PB hXB i', Finset.mem_map_of_mem _ hi', key i0 i' he⟩
  · intro i' hi'
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.1 hi'
    obtain ⟨i0, hi0, he⟩ := h2 j' hj'
    exact ⟨parEquiv CSA PA hXA i0, Finset.mem_map_of_mem _ hi0, key i0 j' he⟩

end Recentred


end Balaban.Polymer.TwoTorusStep
