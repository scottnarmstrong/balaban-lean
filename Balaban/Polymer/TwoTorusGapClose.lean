/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapCloseSym
public import Balaban.Polymer.TwoTorusGapAssembly
import Mathlib.Tactic.Ring

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


omit hn hn' hnS hnS' in
/-- **The recentred torus clause for the marked block-energy term** (item 24, part 2).  Under the hypotheses of `coef_FFmarked_recentred` (with the margins `20 R + 20 < n, n'` in place of the four margins of the transport theorems; they follow from it and from the box of side `L a_{k+1}` in `X₁f`, `gapMargins_of_width`), the terms `evDec` of the second torus at `φ Y` and of the first torus at `Y` are equal, `φ x = bm (x + tA) - tB`: `evTerm_boxMap_recentred` with the coefficient correspondence of `coef_FFmarked_recentred`, transferred to the recentred functions by `coef_recentred_of_coef`. -/
theorem evDec_recentred (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hbox : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1)) :
    evDec X₁f' m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm
        ((fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) '' Y) (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  obtain ⟨b, hb⟩ := hbox
  have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
    (b := b + tA) (s := L * cellSide L m₀ m₁ (k + 1)) (r := R)
    (t := min (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
    (min_le_left _ _) (min_le_right _ _) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ : ∃ y, x = y + tA := ⟨x - tA, by abel⟩
      exact hX₁R y (Finset.mem_coe.1 (hb ((mem_box_add_iff b tA y _).1 hx))))
  have hw : L * cellSide L m₀ m₁ (k + 1) ≤ 2 * R + 1 := by
    rcases min_choice (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
    · rwa [h] at hw0
    · rw [h] at hw0; omega
  obtain ⟨-, h2, h3, -⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn20
  obtain ⟨-, h2', h3', -⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn20'
  have hcoef := coef_FFmarked_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hN hN' tA tB htA htB hXT hX' hXT' hcov hX₁ hcov' hX₁' SA SmA SB SmB hΦan hΦan' hΦA hΦB hBM
    hRδ hRψ hΦ hX₁R hYR h2 h2' h3 h3' hD hD' hraw hψh hψh' hhat hZm hum
  have hFanA := analyticOnNhd_FFmarked hC hk hHA hGA cc hcψ hMX hmar hαK hsm hF₁ hSol hΦan Zm
    hum hD hψh
  have hFanB := analyticOnNhd_FFmarked hC' hk hHB hGB cc hcψ hMX hmar hαK hsm hF₁' hSol' hΦan' Zm'
    hum hD' hψh'
  have hS' : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) =
      (fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) '' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    rw [hX']; exact Finset.coe_image
  have hcoef' := coef_recentred_of_coef hE1 (Nat.le_add_left 1 k) hN hN' tA tB htA htB hFanA hFanB
    (FA := fun u s => FFmarked X₁f a₁ ν hGA cc F₁ Sol Φ Zm um tm u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tA
        (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN tA htA) rfl))
    (FB := fun u s => FFmarked X₁f' a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm u (s ∘ parEquiv
      (DecEquiv.CoverSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) tB
        (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ)))
      (DecEquiv.PolymerSymm.ofTranslate (isLevel_levelGS (by omega) le_rfl) hN' tB htB) rfl))
    rfl rfl hcoef
  have hmain := evTerm_boxMap_recentred (m₀ := m₀) (R := R) hE1 hd hL hm₀ hm₁ hN hN' hn20 hn20'
    tA tB htA htB ⟨b, hb⟩ (fun x hx => hX₁R x (Finset.mem_coe.1 hx)) hYR hS' hFanA hFanB rfl rfl hcoef'
  unfold evDec
  rw [← hX₁, ← hX₁']
  exact hmain

end Recentred


section RecentredBm

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

variable
    {Φ : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ) → ((HA).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ) → ((HB).Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2) (FlReal (GA) (HA) a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦan' : AnalyticOnNhd ℂ (fun t => Φ' t.1 t.2.1 t.2.2)
      (FlReal (GB) (HB) a₁ ν BG κ eps X₁f' BG₂ δ₁))
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

variable
    (hfamΦ : ∀ z : Fin d → ℤ, (∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ) →
      (∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ,
        |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
      ∀ (SA : LatSymm (GA) (GA)
          (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
        (SmA : LatSymm (HA) (HA)
          (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
        (SB : LatSymm (GB) (GB)
          (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))))
        (SmB : LatSymm (HB) (HB)
          (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))),
      ∃ (ΦT : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ) → ((HA).Ω 1 × Fin N → ℂ) →
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
        (ΦT' : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ) → ((HB).Ω 1 × Fin N → ℂ) →
          RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ)
        (Rα Rδ Rψ : Set (CTorus d L N₁ m₁ (k + 1))),
        BlockMargin (GA) (X₁f.image (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) Rα ∧
        Rδ ⊆ ↑(X₁f.image (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) ∧
        Rψ ⊆ ↑(X₁f.image (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) ∧
        (∀ (bg : ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) δφ u,
          ΦT (SA.fld bg.1, SA.mul bg.2) (SmA.fld δφ) (symU (Equiv.addRight
            (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) u) = Φ bg δφ u) ∧
        (∀ (bg : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) δφ u,
          ΦT' (SB.fld bg.1, SB.mul bg.2) (SmB.fld δφ) (symU (Equiv.addRight
            (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) u) = Φ' bg δφ u) ∧
        (∀ (t : (((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)) × ((HA).Ω 1 × Fin N → ℂ) ×
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
          ΦT' t'.1 t'.2.1 t'.2.2 = ΦT t.1 t.2.1 t.2.2))

include hC hC' hk hGA hGB hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hd hL hm₀ hm₁ hN hN' hX'
  hcov hX₁ hcov' hX₁' h𝒦 hDs hn25 hn25' hq hqn hΦan hΦan' hD hD' hψh hψh' hum hfamD hfamΦ

/-- **The torus clause for the marked block-energy term at a compact support anywhere on the torus** (item 24, part 2; the step with no inherited terms).  Let the read region `X₁f` (a nonempty union of `π'_{k+1}`-cubes with its cover data, `hcov`, `hX₁`, `h𝒦`) and the domain `Y` have cyclic spread `Ds` with `25 Ds + 25` below both torus sides (`hDs`, `hn25`, `hn25'`), lie in the centred box of radius `q` of the first torus with `2 q + 2 (Ds + (Ds + 1) / 4) < n` (`hq`, `hqn`; this holds for the supports of the quarter box that are not wide, `compact_site_margins`), and let `X₁f'` be the image of `X₁f` under the box map `bm`.  Assume that for every recentring vector `z` (a multiple of the cell side taking `X₁f ∪ Y` into the centred box of radius `Ds + (Ds + 1) / 4`, as integer sums) the data correspond under the recentred map (`hfamD`: raw data, hat variables and masks, after the translations by `z` on the two tori) and the block functionals have translated functionals with corresponding reads (`hfamΦ`).  Then `evDec` of the second torus at `bm Y` equals `evDec` of the first torus at `Y`: the torus independence of the term, with no assumption on the position of the support.  The recentring vector is `exists_recentring_int` (the map `φ_z x = bm (x + z) - z` equals `bm` on the support because the integer sums stay in the box, `boxMap_add_intCast`), and the proof is `evDec_recentred`. -/
theorem evDec_boxMap_of_diameter :
    evDec X₁f' m₀ j 𝒦X' a₁ ν hGB cc F₁' Sol' Φ' Zm' um tm (bm '' Y) (rawOf D', ψh') =
      evDec X₁f m₀ j 𝒦X a₁ ν hGA cc F₁ Sol Φ Zm um tm Y (rawOf D, ψh) := by
  classical
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  obtain ⟨q0, hq0⟩ := h𝒦
  obtain ⟨b', hb1, hb2, hb3⟩ := hcov.nest q0 hq0
  have hbox : ∃ b, box b (L * cellSide L m₀ m₁ (k + 1)) ⊆
      (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    refine ⟨b', ?_⟩
    rw [hX₁]
    intro x hx
    exact Set.mem_iUnion₂.2 ⟨b', ⟨hb1, hb3, q0, hq0, hb2⟩, hx⟩
  obtain ⟨z, hz, hint⟩ := exists_recentring_int (n := (N₁ * L ^ m₁) * L ^ (k + 1))
    (a := cellSide L m₀ m₁ (k + 1)) (L := L) (D := Ds) (q := q) hd (cellSide_pos m₀ m₁ (k + 1)) hL
    (cellSide_dvd hN le_rfl) hbox hDs hn25 hq hqn
  set tA : CTorus d L N₁ m₁ (k + 1) := fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))
    with htAdef
  set tB : CTorus d L N₁' m₁ (k + 1) := fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))
    with htBdef
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hXR : ∀ x ∈ X₁f, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) :=
    fun x hx => inBox_add_intCast hnR x z (hint x (Or.inl (Finset.mem_coe.2 hx)))
  have hYR : ∀ y ∈ Y, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) :=
    fun y hy => inBox_add_intCast hnR y z (hint y (Or.inr hy))
  have hφ : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, bm (x + tA) - tB = bm x := by
    intro x hx
    have := boxMap_add_intCast (m' := (N₁' * L ^ m₁) * L ^ (k + 1)) hnR x z (hint x hx)
    rw [this]; exact add_sub_cancel_right _ _
  have hXφ : X₁f' = X₁f.image (fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) := by
    rw [hX']
    exact Finset.image_congr (fun x hx => (hφ x (Or.inl hx)).symm)
  have hYφ : (fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB) '' Y = bm '' Y :=
    Set.image_congr (fun y hy => hφ y (Or.inr hy))
  have hSA := LatSymm.ofTranslateLevel hGA tA (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSmA := LatSymm.ofTranslateLevel hHA tA (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSB := LatSymm.ofTranslateLevel hGB tB (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  have hSmB := LatSymm.ofTranslateLevel hHB tB (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  obtain ⟨ΦT, ΦT', Rα, Rδ, Rψ, hBM, hRδ, hRψ, hΦA, hΦB, hΦ⟩ :=
    hfamΦ z hz hint hSA hSmA hSB hSmB
  obtain ⟨hraw, hhat, hZm⟩ := hfamD z hz hint
  have hmain := evDec_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hN hN' tA tB htA htB rfl hXφ rfl hcov hX₁ hcov' hX₁' hSA hSmA hSB hSmB hΦan hΦan' hΦA hΦB hBM
    hRδ hRψ hΦ hXR hYR hD hD' hraw hψh hψh' (fun y hy => hhat y hy) (fun y hy => hZm y hy) hum
    hd hL hm₀ hm₁ hbox (by omega) (by omega)
  rw [hYφ] at hmain
  exact hmain

end RecentredBm


section Margins

/-- **The site-level margins of a compact support.**  Let the cells have side `cs`, the tori have `K ≤ K'` cells per side with `26 ≤ K`, and let a support of the quarter box of the first torus that is not wide have cell spread `Dc ≤ (K - 26) / 25` (`compact_margin`).  If the sites of the read region and of the domain have spread `Ds` with `Ds + 1 ≤ cs (Dc + 1)` and lie within `q ≤ cs (K / 4 + 1) + Ds` of the origin, then `25 Ds + 25` is below both torus sides `cs K`, `cs K'`, and `2 q + 2 (Ds + (Ds + 1) / 4) < cs K`: the margins of `evDec_boxMap_of_diameter`. -/
theorem compact_site_margins {K K' cs Dc Ds q : ℕ} (hK : 26 ≤ K) (hKK' : K ≤ K') (hcs : 0 < cs)
    (hD : Dc ≤ (K - 26) / 25) (hDs : Ds + 1 ≤ cs * (Dc + 1))
    (hq : q ≤ cs * (K / 4 + 1) + Ds) :
    25 * Ds + 25 < cs * K ∧ 25 * Ds + 25 < cs * K' ∧
      2 * q + 2 * (Ds + (Ds + 1) / 4) < cs * K := by
  have h1 : 25 * (Dc + 1) + 1 ≤ K := by omega
  have h2 : cs * (25 * (Dc + 1) + 1) ≤ cs * K := Nat.mul_le_mul_left cs h1
  have h3 : cs * K ≤ cs * K' := Nat.mul_le_mul_left cs hKK'
  have h4 : cs * (K / 4) * 4 ≤ cs * K := by
    have : 4 * (K / 4) ≤ K := Nat.mul_div_le K 4
    calc cs * (K / 4) * 4 = cs * (4 * (K / 4)) := by ring
      _ ≤ cs * K := Nat.mul_le_mul_left cs this
  have h5 : cs * (K / 4 + 1) = cs * (K / 4) + cs := by ring
  have h6 : cs * (25 * (Dc + 1) + 1) = 25 * (cs * (Dc + 1)) + cs := by ring
  have h7 : cs ≤ cs * (Dc + 1) := Nat.le_mul_of_pos_right cs (by omega)
  rw [h6] at h2
  rw [h5] at hq
  refine ⟨by omega, by omega, by omega⟩

end Margins


end Balaban.Polymer.TwoTorusStep
