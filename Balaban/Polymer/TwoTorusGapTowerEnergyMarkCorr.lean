/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerEnergyGeom

/-!
# The corrected marks of a block under the recentring map (blocker 7)

The marks of the energy coefficient are built from the corrected block marks `decMarkCorr` (the
first-order Taylor remainder in the first mark `um` of the `t`-derivative at `0` of the marked
block-energy term `evDec … Zm um t`), with the mask `Zm` of the unit points of the root block.

* `markCorr_eq_of_eqOn`: the Taylor remainder of the `t`-derivative depends only on the marked term
  on the radius set `(‖v‖ + ‖t‖) M < δ₁`.
* `evDec_rootBlock_recentred`: `evDec_blockEnergy_recentred` for an arbitrary mask and arbitrary
  marks of the radius set (`evDec_recentred` with the translated block-energy functionals of
  `hfamΦ_blockEnergy_at`).
* `decMarkCorr_rootBlock_recentred`: the corrected marks of corresponding blocks agree.
* `unitBlock1_unitPt_add`, `rootMask_recentred`: the root masks correspond under the recentring map.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section MarkCorr

/-- **The corrected mark from the marked term.**  If two functions `f`, `g` of the marks `(v, t)`
agree on the radius set `(‖v‖ + ‖t‖) M < δ₁`, then for `‖um‖ M < δ₁` the first-order Taylor
remainders in `v` of their `t`-derivatives at `0` (the form of `decMarkCorr` over `decMarkG`)
agree. -/
theorem markCorr_eq_of_eqOn {f g : ℂ → ℂ → ℂ} {M δ₁ : ℝ} (hδ : 0 < δ₁)
    (h : ∀ v t : ℂ, (‖v‖ + ‖t‖) * M < δ₁ → f v t = g v t) {um : ℂ} (hum : ‖um‖ * M < δ₁) :
    deriv (fun t => f um t) 0 - deriv (fun t => f 0 t) 0 -
        um * deriv (fun v => deriv (fun t => f v t) 0) 0 =
      deriv (fun t => g um t) 0 - deriv (fun t => g 0 t) 0 -
        um * deriv (fun v => deriv (fun t => g v t) 0) 0 := by
  have hG : ∀ v : ℂ, ‖v‖ * M < δ₁ → deriv (fun t => f v t) 0 = deriv (fun t => g v t) 0 := by
    intro v hv
    refine Filter.EventuallyEq.deriv_eq ?_
    have hopen : IsOpen {t : ℂ | (‖v‖ + ‖t‖) * M < δ₁} := isOpen_lt (by fun_prop) continuous_const
    have h0 : (0 : ℂ) ∈ {t : ℂ | (‖v‖ + ‖t‖) * M < δ₁} := by simpa using hv
    filter_upwards [hopen.mem_nhds h0] with t ht
    exact h v t ht
  have hopen : IsOpen {v : ℂ | ‖v‖ * M < δ₁} := isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {v : ℂ | ‖v‖ * M < δ₁} := by simpa using hδ
  have hd : deriv (fun v => deriv (fun t => f v t) 0) 0 =
      deriv (fun v => deriv (fun t => g v t) 0) 0 :=
    Filter.EventuallyEq.deriv_eq (Filter.mem_of_superset (hopen.mem_nhds h0) fun v hv => hG v hv)
  rw [hG um hum, hG 0 h0, hd]

end MarkCorr

section RootBlockRec

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
local notation "tAz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
set_option hygiene false in
local notation "tBz" => (fun μ => ((zv μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))

/-- **The marked block-energy term of a block under the recentring map.**  As
`evDec_blockEnergy_recentred`, for an arbitrary mask `Zm` (corresponding to `Zm'` on the recentred
box, `hZm`) and arbitrary marks `(um, tm)` of the radius set: `evDec_recentred` with the translated
block-energy functionals of `hfamΦ_blockEnergy_at` and the covering data of the local covers. -/
theorem evDec_rootBlock_recentred
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
    {m₀ : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (zv : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (b' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hbb : LocalCover.blockSite k b' + tBz = bm (LocalCover.blockSite k b + tAz))
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tAz) (rawOf D)) (symRaw (Equiv.addRight tBz) (rawOf D')))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz) →
      ∀ i, ψh' (unitPt hGB (bm (y + tAz) - tBz), i) = ψh (unitPt hGA y, i))
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz) →
      (unitPt hGB (bm (y + tAz) - tBz) ∈ Zm' ↔ unitPt hGA y ∈ Zm))
    {um tm : ℂ} (hum : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b')) a₁ ν hGB cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k b') Zm' um tm
        ((fun x => bm (x + tAz) - tBz) '' Y) (rawOf D', ψh') =
      evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν hGA cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm um tm Y (rawOf D, ψh) := by
  classical
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tAz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tBz μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have hSA := LatSymm.ofTranslateLevel hGA tAz (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSmA := LatSymm.ofTranslateLevel hHA tAz (fun μ => (pow_dvd_pow L (by omega)).trans (htA μ))
  have hSB := LatSymm.ofTranslateLevel hGB tBz (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  have hSmB := LatSymm.ofTranslateLevel hHB tBz (fun μ => (pow_dvd_pow L (by omega)).trans (htB μ))
  have hLK : L ^ (k + 1) ≤ cellSide L m₀ m₁ (k + 1) := by
    unfold cellSide
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hLa : cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨hZ, hBM0⟩ := rootBlock_premises hC.Sp hm₀ b
  have hx₀R : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k b + tAz) :=
    hX₁R _ (by
      rw [← LocalCover.coe_nbhdF]
      exact Finset.mem_coe.2 (LocalCover.mem_nbhdF_self m₀ _))
  -- the width of the region and the margins
  have hbox : ∃ b₀, box b₀ (L * cellSide L m₀ m₁ (k + 1)) ⊆
      (↑(LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) : Set (CTorus d L N₁ m₁ (k + 1))) := by
    refine ⟨LocalCover.corner m₀ (LocalCover.blockSite k b) -
      natT (n := (N₁ * L ^ m₁) * L ^ (k + 1)) (fun _ => (L - 1) * cellSide L m₀ m₁ (k + 1)), ?_⟩
    rw [LocalCover.coe_nbhdF]
    exact box_mono _ (by nlinarith)
  obtain ⟨b₀, hb₀⟩ := hbox
  have hw0 := width_le_of_box_subset_inBox (n := (N₁ * L ^ m₁) * L ^ (k + 1)) hd
    (b := b₀ + tAz) (s := L * cellSide L m₀ m₁ (k + 1)) (r := R)
    (t := min (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)))
    (min_le_left _ _) (min_le_right _ _) (fun x hx => by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + tAz := ⟨x - tAz, by abel⟩
      exact hX₁R y (by
        rw [← LocalCover.coe_nbhdF]
        exact hb₀ ((mem_box_add_iff b₀ tAz y _).1 hx)))
  have hw : L * cellSide L m₀ m₁ (k + 1) ≤ 2 * R + 1 := by
    rcases min_choice (L * cellSide L m₀ m₁ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) with h | h
    · rwa [h] at hw0
    · rw [h] at hw0; omega
  obtain ⟨hnF, -, -, -⟩ := gapMargins_of_width hL hm₀ hm₁ hw hn20
  have hLa' : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have hnF1 : 2 * R + ((L - 1) * cellSide L m₀ m₁ (k + 1) + L * cellSide L m₀ m₁ (k + 1)) <
      (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨ΦT, ΦT', Rα, Rδ, Rψ, hBM, hRδ, hRψ, hΦA, hΦB, hΦ⟩ :=
    hfamΦ_blockEnergy_at (ρ := R) hk hN hN' (compWeight L a₁) ν (LocalCover.blockSite k b') hZ
      hBM0 (by omega) (by omega) zv hz hx₀R hbb hSA hSmA hSB hSmB
  have hcov := LocalCover.covSetup (m₀ := m₀) hGA hN (j := k) le_rfl (LocalCover.blockSite k b)
  have hX₁ := LocalCover.coe_nbhdF_eq_X1 (m₀ := m₀) hGA hN (j := k) le_rfl
    (LocalCover.blockSite k b)
  have hcov' := LocalCover.covSetup (m₀ := m₀) hGB hN' (j := k) le_rfl (LocalCover.blockSite k b')
  have hX₁' := LocalCover.coe_nbhdF_eq_X1 (m₀ := m₀) hGB hN' (j := k) le_rfl
    (LocalCover.blockSite k b')
  have hX' := nbhdF_recentred hN hN' tAz tBz htA htB hnF1 (LocalCover.blockSite k b)
    (LocalCover.blockSite k b') hbb hX₁R
  have h := evDec_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hN hN' tAz tBz htA htB rfl hX' rfl hcov hX₁ hcov' hX₁' hSA hSmA hSB hSmB
    ((blockEnergyFun_analytic _ _ _ _).mono (Set.subset_univ _))
    ((blockEnergyFun_analytic _ _ _ _).mono (Set.subset_univ _)) hΦA hΦB hBM hRδ hRψ hΦ
    (fun x hx => hX₁R x (by rw [← LocalCover.coe_nbhdF]; exact Finset.mem_coe.2 hx)) hYR hD hD'
    hraw hψh hψh' hhat hZm hum hd hL hm₀ hm₁ ⟨b₀, hb₀⟩ hn20 hn20'
  rw [LocalCover.jBlock_blockSite le_rfl, LocalCover.jBlock_blockSite le_rfl] at h
  exact h

set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ

/-- **The corrected mark of a block under the recentring map** (`decMarkCorr`, the first-order Taylor
remainder in the first mark of `decMarkG`): equal for the block `b` at the label `Y` and for the block
`b'` at `φ '' Y`, for corresponding block variables, masks, raw data and `‖um‖ · markedRad < δ₁`
(`markCorr_eq_of_eqOn` with `evDec_rootBlock_recentred` at the clamped hat variables). -/
theorem decMarkCorr_rootBlock_recentred
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ)
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
    {m₀ : ℕ} (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (zv : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ zv μ)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (b' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hbb : LocalCover.blockSite k b' + tBz = bm (LocalCover.blockSite k b + tAz))
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tAz) (rawOf D)) (symRaw (Equiv.addRight tBz) (rawOf D')))
    (hN2 : 2 ≤ N) (νS β p₁ δ : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c) (Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c)
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tAz) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tAz) - tBz)))
        ⟨unitPt (SB).hG' (bm (x + tAz) - tBz), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    {Zm : Finset (unitPts (GA))} {Zm' : Finset (unitPts (GB))}
    (hZm : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tAz) →
      (unitPt hGB (bm (y + tAz) - tBz) ∈ Zm' ↔ unitPt hGA y ∈ Zm))
    {um : ℂ} (hum : ‖um‖ * markedRad d L N k a₁ κ ρ cc < δ₁) :
    decMarkCorr (SB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b')) a₁ ν cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k b') Zm'
        ((fun x => bm (x + tAz) - tBz) '' Y) ρ hp' (rawOf D') um Φ' =
      decMarkCorr (SA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm Y ρ hp (rawOf D) um Φ := by
  unfold decMarkCorr decMarkG
  exact markCorr_eq_of_eqOn (M := markedRad d L N k a₁ κ ρ cc) hC.δ₁_pos
    (f := fun v t => evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b')) a₁ ν (SB).hG' cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k b') Zm' v t
        ((fun x => bm (x + tAz) - tBz) '' Y) (rawOf D', (SB).hatOf m₀ ρ hp' Φ'))
    (g := fun v t => evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν (SA).hG' cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) Zm v t Y (rawOf D, (SA).hatOf m₀ ρ hp Φ))
    (fun v t hvt => evDec_rootBlock_recentred hC hC' hk hGA hGB cc hρ.le hMX hmar hαK hsm hF₁ hF₁'
      hSol hSol' hd hL hm₀ hm₁ hN hN' zv hz b b' hbb hX₁R hYR hn20 hn20' hD hD' hraw
      (fun p => (SA).hatOf_mem m₀ hρ hp Φ p) (fun p => (SB).hatOf_mem m₀ hρ hp' Φ' p)
      (hatOf_rec hN2 hk νS β p₁ δ m₀ ρ hp hp' hΦ) hZm hvt) hum

end RootBlockRec

section MaskRec

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "τA" => (fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "τB" => (fun μ => ((((tB μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))

/-- The level-one block of the unit point of a translate is the translated block. -/
theorem unitBlock1_unitPt_add (hG : IsLevel (GA) (k + 1)) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ (k + 1) ∣ (t μ).val) (x : CTorus d L N₁ m₁ (k + 1)) :
    unitBlock1 ((unitPt hG (x + t) : unitPts (GA)) : UnitTorus d L N₁ m₁ k) =
      unitBlock1 ((unitPt hG x : unitPts (GA)) : UnitTorus d L N₁ m₁ k) +
        fun μ => ((((t μ).val / L ^ (k + 1) : ℕ)) : ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) := by
  show unitBlock1 (unitBlock (x + t)) = unitBlock1 (unitBlock x) + _
  rw [unitBlock1_unitBlock, unitBlock1_unitBlock]
  exact blockIndex_add_coarse t ht x

/-- **The root mask under the recentring map**: the unit point of `φ y` lies in the block of the root
`bc (z + τA) - τB` iff the unit point of `y` lies in the block of `z`, for `y + tA` in the box. -/
theorem rootMask_recentred (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ (k + 1) ∣ (tA μ).val) (htB : ∀ μ, L ^ (k + 1) ∣ (tB μ).val) {R rc : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA)) (hrc : L ^ (k + 1) * rc ≤ R)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    unitBlock1 ((unitPt hGB (bm (y + tA) - tB) : unitPts (GB)) : UnitTorus d L N₁' m₁ k) =
        bc (z + τA) - τB ↔
      unitBlock1 ((unitPt hGA y : unitPts (GA)) : UnitTorus d L N₁ m₁ k) = z := by
  have h := rootMask_bc (N₁' := N₁') hn hn' hGA hGB (z + τA) hz hrc hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hB := unitBlock1_unitPt_add hGB tB htB (bm (y + tA) - tB)
  have hA := unitBlock1_unitPt_add hGA tA htA y
  rw [sub_add_cancel] at hB
  rw [hB, hA] at h
  rw [← add_left_inj τB, sub_add_cancel, h, add_left_inj]

end MaskRec

end Balaban.Polymer.TwoTorusStep
