/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsBlocks

/-!
# The potential part of the activity of a label under the recentring map (item 24, blocker 7)

`vpartTerm_recentred`: the sum over the blocks of the potential terms at the domain of a label, on
two tori, at the recentred domain `φ '' Y` and at `Y`.  The blocks with the domain correspond by the
coarse recentring `b ↦ bc (b + τA) - τB`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section PartRec

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ R : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
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
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "τA" => (fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "τB" => (fun μ => ((((tB μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))

/-- **The block of a domain in the recentred box.**  If `Y` is a domain of the expansion of the block
`b` with its local cover and `Y` lies in the recentred box, the region of the block and the
translated coarse block lie in the box. -/
theorem block_recentred_data (hN : L ^ m₀ ∣ N₁) (tA : CTorus d L N₁ m₁ (k + 1))
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (htA : ∀ μ, L ^ (k + 1) ∣ (tA μ).val)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
      (LocalCover.fam m₀ (LocalCover.blockSite k b)))
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) ∧
      InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (b + τA) := by
  have hX : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) := fun x hx =>
    hYR x (nbhd_subset_of_mem_polyDom hN _ hY hx)
  refine ⟨hX, inBox_coarse_of_blockSite _ ?_⟩
  rw [blockSite_add_coarse tA htA]
  exact hX _ (cell_subset_nbhd _ (LocalCover.mem_cell m₀ _))

/-- **The domains of the blocks in recentred form.**  For the block `b` whose region lies in the
recentred box, `φ '' Y` is a domain of the block `ψ b = bc (b + τA) - τB` of the second torus iff `Y`
is a domain of the block `b` of the first. -/
theorem mem_polyDom_blockSite_recentred_iff (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    (hz : InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (b + τA))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    (fun x => bm (x + tA) - tB) '' Y ∈
        polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc (b + τA) - τB))) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k (bc (b + τA) - τB))) ↔
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) := by
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tA μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htA μ)
  have htB1 : ∀ μ, L ^ (k + 1) ∣ (tB μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htB μ)
  have hs : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by
    have := Nat.mul_pos (NeZero.pos L) (cellSide_pos (L := L) m₀ m₁ (k + 1))
    omega
  have hxs := blockSite_recentred (r := R) tA tB htA1 htB1 b hz (Nat.mul_div_le R _) hs
  exact mem_polyDom_site_recentred_iff hGA hGB hN hN' tA tB htA htB hnF hnF' _ _ hxs hX₁R hYR

/-- **The blocks of a recentred domain correspond.**  The blocks `b` with the domain `Y` and the blocks
`b'` of the second torus with the domain `φ '' Y` correspond by `b ↦ bc (b + τA) - τB`. -/
theorem blocks_recentred (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hL : 2 ≤ L) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1)) :
    (∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) →
      (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) ∧
      LocalCover.blockSite k (bc (b + τA) - τB) + tB = bm (LocalCover.blockSite k b + tA) ∧
      (fun x => bm (x + tA) - tB) '' Y ∈
        polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc (b + τA) - τB))) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k (bc (b + τA) - τB))) ) ∧
    (∀ b₁ b₂ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b₁)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b₁)) →
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b₂)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b₂)) →
      bc (b₁ + τA) - τB = bc (b₂ + τA) - τB → b₁ = b₂) ∧
    (∀ b' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      (fun x => bm (x + tA) - tB) '' Y ∈
        polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k b')) →
      ∃ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k b)) ∧ bc (b + τA) - τB = b') := by
  classical
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tA μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htA μ)
  have htB1 : ∀ μ, L ^ (k + 1) ∣ (tB μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htB μ)
  have hLK : L ^ (k + 1) ≤ cellSide L m₀ m₁ (k + 1) := by
    unfold cellSide
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hLa : cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hs : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hcA := coarse_margin (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (r := R) (by omega)
  have hcB := coarse_margin (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (r := R) (by omega)
  have hYR' : ∀ y' ∈ (fun x => bm (x + tA) - tB) '' Y,
      InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (y' + tB) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [sub_add_cancel]
    exact inBox_boxMap hsB (hYR y hy)
  refine ⟨fun b hb => ?_, fun b₁ b₂ h₁ h₂ h => ?_, fun b' hb' => ?_⟩
  · obtain ⟨hX₁R, hzc⟩ := block_recentred_data hN tA b htA1 hb hYR
    have hxs := blockSite_recentred (r := R) tA tB htA1 htB1 b hzc (Nat.mul_div_le R _) hs
    exact ⟨hX₁R, hxs, (mem_polyDom_blockSite_recentred_iff hGA hGB hN hN' tA tB htA htB hnF hnF' b
      hX₁R hzc hYR).2 hb⟩
  · obtain ⟨-, hz₁⟩ := block_recentred_data hN tA b₁ htA1 h₁ hYR
    obtain ⟨-, hz₂⟩ := block_recentred_data hN tA b₂ htA1 h₂ hYR
    have h' := sub_left_inj.1 h
    exact add_right_cancel (boxMap_inj (hm' := hcB) hz₁ hz₂ h')
  · obtain ⟨hX₁R', hzc'⟩ := block_recentred_data (N₁ := N₁') hN' tB b' htB1 hb' hYR'
    have hrt : bc (boxMap (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
        (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (b' + τB) - τA + τA) - τB = b' := by
      rw [sub_add_cancel, boxMap_boxMap hcA hzc', add_sub_cancel_right]
    have hYY : (fun x => bm' (x + tB) - tA) '' ((fun x => bm (x + tA) - tB) '' Y) = Y := by
      rw [Set.image_image]
      conv_rhs => rw [← Set.image_id Y]
      refine Set.image_congr (fun y hy => ?_)
      simp only [sub_add_cancel, id]
      rw [boxMap_boxMap hsB (hYR y hy)]
      exact add_sub_cancel_right _ _
    have hiff := mem_polyDom_blockSite_recentred_iff (N₁ := N₁') (N₁' := N₁) hGB hGA hN' hN tB tA
      htB htA hnF' hnF b' hX₁R' hzc' hYR'
    rw [hYY] at hiff
    exact ⟨boxMap (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
      (b' + τB) - τA, hiff.2 hb', hrt⟩

/-- **The potential part of the activity at a recentred domain**: the sum over the blocks of the
potential terms at the domain `φ '' Y` on the second torus equals the sum at `Y` on the first. -/
theorem vpartTerm_recentred_core
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htAz : tA = (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) (htBz : tB = (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
    (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y + tA))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight tA)
        (rawOf D))
      (symRaw (Equiv.addRight tB)
        (rawOf D')))
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + tA) →
      ∀ i, x₀' (unitPt hGB (bm (y + tA) -
        tB), i) = x₀ (unitPt hGA y, i))
    (hhw : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + tA) →
      ∀ i, w' (unitPt hGB (bm (y + tA) -
        tB), i) = w (unitPt hGA y, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) (ω : ℂ → ℂ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    (∑ b' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      if (fun x => bm (x + tA) -
          tB) '' Y ∈
          polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k b')) then
        rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k b')) a₁ ν hGB cc (F₁' b') (Sol' b')
          (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k b') ∅ 1 0
          ((fun x => bm (x + tA) -
            tB) '' Y)) w') ω x₀' σ
          (rawOf D')
      else 0) =
      ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k b)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν hGA cc (F₁ b) (Sol b)
            (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) ∅ 1 0 Y) w) ω x₀ σ (rawOf D)
        else 0 := by
  classical
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val := fun μ => by
    rw [htAz]; exact dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val := fun μ => by
    rw [htBz]; exact dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  obtain ⟨hmap, hinj, hsurj⟩ := blocks_recentred hGA hGB hL hN hN' tA tB htA htB hYR hn20 hn20'
    hnF hnF'
  refine sum_ite_bij _ _ _ _ (fun b => bc (b + τA) - τB) (fun b hb => ?_) hinj hsurj
  obtain ⟨hX₁R, hxs, hmem⟩ := hmap b hb
  generalize bc (b + τA) - τB = b'' at hxs hmem ⊢
  subst htAz htBz
  refine ⟨hmem, ?_⟩
  exact vblockTerm_recentred hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm (hF₁ b)
    (hF₁' b'') (hSol b) (hSol' b'') hd hL hm₀ hm₁ hN hN' z hz b
    b'' hxs hX₁R hYR hn20 hn20' hD hD' hraw hx₀ hw hx₀' hw' hρ₀ hhx hhw hrad ω hσ

/-- **The potential part of the activity at a recentred domain**: the sum over the blocks of the
potential terms at the domain `φ '' Y` on the second torus equals the sum at `Y` on the first. -/
theorem vpartTerm_recentred
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hd : 0 < d) (hL : 2 ≤ L) (hm₀ : 1 ≤ m₀) (hm₁ : 1 ≤ m₁)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
    (hn20 : 20 * R + 20 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn20' : 20 * R + 20 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {w | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) w}
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D))
      (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))
        (rawOf D')))
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
      ∀ i, x₀' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
        fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = x₀ (unitPt hGA y, i))
    (hhw : ∀ y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) →
      ∀ i, w' (unitPt hGB (bm (y + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
        fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))), i) = w (unitPt hGA y, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) (ω : ℂ → ℂ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    (∑ b' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      if (fun x => bm (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
          fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) '' Y ∈
          polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k b')) then
        rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k b')) a₁ ν hGB cc (F₁' b') (Sol' b')
          (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k b') ∅ 1 0
          ((fun x => bm (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
            fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))) '' Y)) w') ω x₀' σ
          (rawOf D')
      else 0) =
      ∑ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k b)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν hGA cc (F₁ b) (Sol b)
            (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) ∅ 1 0 Y) w) ω x₀ σ (rawOf D)
        else 0 := by
  exact vpartTerm_recentred_core hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' z hz _ _ rfl rfl hd hL hm₀ hm₁ hN hN' hYR hn20 hn20' hnF hnF' hD hD' hraw hx₀ hw hx₀' hw' hρ₀ hhx hhw hrad ω hσ

end PartRec

end Balaban.Polymer.TwoTorusStep
