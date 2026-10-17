/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsDom

/-!
# The domains of the local cover under the recentring vector (blocker 7)

`polyDom_recentred_of_vec` (`hmemV` of the gap-scale step with the label sets the domains of the
local cover): for a recentring vector `z` (a multiple of the cell side) taking the region of the
site `xs` into the box of radius `Ds + (Ds + 1) / 4`, `φ '' Z`, `φ x = bm (x + z) - z`, is a domain
of the local cover of `bm xs` on the second torus iff `Z` is a domain of the local cover of `xs`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Mem

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

/-- **`hmemV` for the domains of the local cover.** -/
theorem polyDom_recentred_of_vec
    (hGA : IsLevel (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl) (k + 1))
    (hGB : IsLevel (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) le_rfl) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {Ds : ℕ}
    (hDsa : L * cellSide L m₀ m₁ (k + 1) ≤ Ds + 1)
    (hn25 : 25 * Ds + 25 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn25' : 25 * Ds + 25 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (xs : CTorus d L N₁ m₁ (k + 1)) (z : Fin d → ℤ)
    (hz : ∀ μ, ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) ∣ z μ)
    (hint : ∀ x ∈ LocalCover.nbhd m₀ xs, ∀ μ,
      |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ))
    (Z : Set (CTorus d L N₁ m₁ (k + 1)))
    (hZ : ∀ x ∈ Z, InBox d (Ds + (Ds + 1) / 4) ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))))) :
    (fun x => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
        (x + (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))) -
        (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))) '' Z ∈
        polyDom (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
          (k + 1) le_rfl)
          (LocalCover.nbhdF m₀ (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
            ((N₁' * L ^ m₁) * L ^ (k + 1)) xs)) m₀ k
          (LocalCover.fam m₀ (boxMap ((N₁ * L ^ m₁) * L ^ (k + 1))
            ((N₁' * L ^ m₁) * L ^ (k + 1)) xs)) ↔
      Z ∈ polyDom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
          (k + 1) le_rfl) (LocalCover.nbhdF m₀ xs) m₀ k (LocalCover.fam m₀ xs) := by
  have hapos : 0 < cellSide L m₀ m₁ (k + 1) := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have : NeZero (cellSide L m₀ m₁ (k + 1)) := ⟨hapos.ne'⟩
  have hnR : 2 * (Ds + (Ds + 1) / 4) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hxsin : xs ∈ LocalCover.nbhd m₀ xs := by
    have := LocalCover.mem_nbhdF_self m₀ xs
    rwa [← Finset.mem_coe, LocalCover.coe_nbhdF] at this
  have hcs : cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) := cellSide_le_mul
  refine mem_polyDom_site_recentred_iff hGA hGB hN hN'
    (fun μ => ((z μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))))
    (fun μ => ((z μ : ℤ) : ZMod ((N₁' * L ^ m₁) * L ^ (k + 1))))
    (fun μ => dvd_val_intCast (cellSide_dvd hN le_rfl) (hz μ))
    (fun μ => dvd_val_intCast (cellSide_dvd hN' le_rfl) (hz μ)) (by omega) (by omega) xs _
    (boxMap_add_intCast hnR xs z (hint xs hxsin)).symm
    (fun x hx => inBox_add_intCast hnR x z (hint x hx)) hZ

end Mem

end Balaban.Polymer.TwoTorusStep
