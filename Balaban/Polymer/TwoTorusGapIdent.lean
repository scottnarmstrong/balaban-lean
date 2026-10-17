/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapIdentEnergy

/-!
# The block-energy term at the gap scale: translated functionals (item 24, blocker 7)

`hfamΦ` of `evDec_boxMap_of_diameter` asks, for every recentring vector `z`, for translated
functionals `ΦT`, `ΦT'` of the block functionals `Φ`, `Φ'` with corresponding reads.  For the block
energy of the step (`blockEnergyFun`, the class's energy functional at the step) these are the block
energies of the translated blocks (`blockEnergyFun_translate`), and the correspondence of the reads
is `blockEnergyFun_levelGS_boxMap`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Fam

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

/-- **The translated block functionals of the block energy** (`hfamΦ` of `evDec_boxMap_of_diameter`
for `Φ = blockEnergyFun` of the block of `x₀` and `Φ' = blockEnergyFun` of the block of `bm x₀`).
Let the sites read by the block energy of `x₀` lie in the read region `X₁f` (`hZ`), the block have the
margin against the cover (`hBM`), and let the recentring vector `z` (a multiple of the cell side
taking `X₁f ∪ Y` into the centred box of radius `ρ = Ds + (Ds + 1) / 4` as integer sums) be given.
Then the block energies of the translated blocks are translated functionals of `Φ`, `Φ'` whose
reads correspond under `bm`: multipliers and tangents on the translated block, fluctuation fields on
its read sites.  The margins `hnE`, `hnE'` are those of `blockEnergyFun_levelGS_boxMap`. -/
theorem hfamΦ_blockEnergy {m₀ Ds : ℕ} (hk : 1 ≤ k) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (a : ℕ → ℝ) (ν : ℝ) {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} {x₀ : CTorus d L N₁ m₁ (k + 1)}
    (hZ : readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) ⊆ ↑X₁f)
    (hBM : BlockMargin (GA) X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀)) :
        Set (CTorus d L N₁ m₁ (k + 1))))
    (hnE : 2 * ((Ds + (Ds + 1) / 4) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * ((Ds + (Ds + 1) / 4) + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : Fin d → ℤ) (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (hint : ∀ x ∈ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ∪ Y, ∀ μ,
      |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ))
    (SA : LatSymm (GA) (GA)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (SmA : LatSymm (HA) (HA)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))))
    (SB : LatSymm (GB) (GB)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))))
    (SmB : LatSymm (HB) (HB)
      (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1)))))) :
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
          (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) u) =
        blockEnergyFun (GA) (HA) a ν k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) bg δφ u) ∧
      (∀ (bg : ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)) δφ u,
        ΦT' (SB.fld bg.1, SB.mul bg.2) (SmB.fld δφ) (symU (Equiv.addRight
          (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) u) =
        blockEnergyFun (GB) (HB) a ν k (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀))
          bg δφ u) ∧
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
        ΦT' t'.1 t'.2.1 t'.2.2 = ΦT t.1 t.2.1 t.2.2) := by
  classical
  set tA : CTorus d L N₁ m₁ (k + 1) :=
    fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) with htAdef
  set tB : CTorus d L N₁' m₁ (k + 1) :=
    fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))) with htBdef
  have htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ)
  have htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val := fun μ =>
    dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tA μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htA μ)
  have htB1 : ∀ μ, L ^ (k + 1) ∣ (tB μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htB μ)
  have htA2 : ∀ μ, L ^ ((k + 1) + m₁) ∣ (tA μ).val := fun μ =>
    (pow_dvd_pow L (by omega)).trans (htA μ)
  have hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hGA : IsLevel (GA) (k + 1) := isLevel_levelGS (by omega) le_rfl
  have hx₀S : x₀ ∈ blockSites d L N₁ m₁ (k + 1) k
      (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hx₀X : x₀ ∈ X₁f := Finset.mem_coe.1 (hZ (readSites_of_blockSites hx₀S))
  have hx₀R : InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₀ + tA) :=
    inBox_add_intCast hnR x₀ z (hint x₀ (Or.inl (Finset.mem_coe.2 hx₀X)))
  have hφ : bm (x₀ + tA) - tB = bm x₀ := by
    have := boxMap_add_intCast (m' := (N₁' * L ^ m₁) * L ^ (k + 1)) hnR x₀ z
      (hint x₀ (Or.inl (Finset.mem_coe.2 hx₀X)))
    rw [this]; exact add_sub_cancel_right _ _
  have hφ' : bm x₀ + tB = bm (x₀ + tA) := by rw [← hφ]; abel
  refine ⟨blockEnergyFun (GA) (HA) a ν k
      (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (x₀ + tA)),
    blockEnergyFun (GB) (HB) a ν k (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm x₀ + tB)),
    ↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (x₀ + tA))),
    readSites (HA) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (x₀ + tA)),
    ↑(blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (x₀ + tA))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← image_blockSites_translate (le_refl (k + 1)) tA htA1 x₀]
    exact blockMargin_translate hGA tA htA2 hBM
  · intro w hw
    have h1 := hZ (sub_mem_readSites (le_refl (k + 1)) tA htA1 hw)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w - tA, Finset.mem_coe.1 h1, sub_add_cancel w tA⟩)
  · intro w hw
    have h1 := hZ (readSites_of_blockSites (sub_mem_blockSites (le_refl (k + 1)) tA htA1 hw))
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w - tA, Finset.mem_coe.1 h1, sub_add_cancel w tA⟩)
  · intro bg δφ u
    exact blockEnergyFun_translate (le_refl (k + 1)) tA htA1 SA SmA a ν x₀ bg δφ u
  · intro bg δφ u
    exact blockEnergyFun_translate (le_refl (k + 1)) tB htB1 SB SmB a ν (bm x₀) bg δφ u
  · intro t t' hα hδ hψ
    have h := blockEnergyFun_levelGS_boxMap hk hnE hnE' a ν hx₀R hα hδ hψ
    rw [hφ']
    exact h

end Fam

end Balaban.Polymer.TwoTorusStep
