/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsEv
public import Balaban.Polymer.TwoTorusGapIdent
public import Balaban.Polymer.TwoTorusObsActivity

/-!
# The potential part of the activity of a label under the recentring map (item 24, blocker 7)

The block-energy term `evDec … (blockEnergyFun … k b) ∅ 1 0` of the block `b` of the first torus and
of the block `b'` of the second (`blockSite k b' + tB = bm (blockSite k b + tA)`) agree at the
recentred domain `φ '' Y` (`evDec_blockEnergy_recentred`); from it the ray terms of the blocks
(`vblockTerm_recentred`), and their sum over the blocks (`vpartTerm_recentred`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background
  Balaban.Localization.DecEquiv

section VRec

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

/-- **The block-energy term of a block under the recentring map.** -/
theorem evDec_blockEnergy_recentred
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
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (b' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hbb : LocalCover.blockSite k b' + (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) =
      bm (LocalCover.blockSite k b + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    {R : ℕ} (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D))
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D')))
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
      ∀ i, ψh' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
        fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = ψh (unitPt hGA y, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) :
    evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b')) a₁ ν hGB cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k b') ∅ 1 0
        ((fun x => bm (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) '' Y) (rawOf D', ψh') =
      evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν hGA cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) ∅ 1 0 Y (rawOf D, ψh) := by
  classical
  have hHA : IsLevel (HA) k := isLevel_levelGS hk (Nat.le_succ k)
  have hHB : IsLevel (HB) k := isLevel_levelGS hk (Nat.le_succ k)
  have hSA := LatSymm.ofTranslateLevel hGA (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)))
  have hSmA := LatSymm.ofTranslateLevel hHA (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)))
  have hSB := LatSymm.ofTranslateLevel hGB (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)))
  have hSmB := LatSymm.ofTranslateLevel hHB (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (fun μ => (pow_dvd_pow L (by omega)).trans (dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)))
  have hw := width_nbhd_recentred (m₀ := m₀) hd _ (LocalCover.blockSite k b) hX₁R hn20
  have hLK : L ^ (k + 1) ≤ cellSide L m₀ m₁ (k + 1) := by
    unfold cellSide
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hLa : cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨hZ, hBM0⟩ := rootBlock_premises hC.Sp hm₀ b
  have hx₀R : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (LocalCover.blockSite k b + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) :=
    hX₁R _ (by
      rw [← LocalCover.coe_nbhdF]
      exact Finset.mem_coe.2 (LocalCover.mem_nbhdF_self m₀ _))
  obtain ⟨ΦT, ΦT', Rα, Rδ, Rψ, hBM, hRδ, hRψ, hΦA, hΦB, hΦ⟩ :=
    hfamΦ_blockEnergy_at (ρ := R) hk hN hN' (compWeight L a₁) ν (LocalCover.blockSite k b') hZ
      hBM0 (by omega) (by omega) z hz hx₀R hbb hSA hSmA hSB hSmB
  have h := evDec_localCover_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hd hL hm₀ hm₁ hN hN' z hz (LocalCover.blockSite k b) (LocalCover.blockSite k b') hbb
    ((blockEnergyFun_analytic _ _ _ _).mono (Set.subset_univ _))
    ((blockEnergyFun_analytic _ _ _ _).mono (Set.subset_univ _)) hSA hSmA hSB hSmB hΦA hΦB hBM hRδ
    hRψ hΦ hX₁R hYR hn20 hn20' hD hD' hraw hψh hψh' hhat hrad
  rw [LocalCover.jBlock_blockSite le_rfl, LocalCover.jBlock_blockSite le_rfl] at h
  exact h

end VRec

end Balaban.Polymer.TwoTorusStep
