/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.ComposeFieldTransport
public import Balaban.Polymer.TwoTorusDecBg

/-!
# The whole-lattice generating sets of two tori correspond under the box map

`gsCorr_levelGS`: the generating sets `levelGS j` of the tori `N₁` and `N₁'` correspond
(`GSCorr`) under `boxMap` on the box of radius `ρ`: every site is in `Ω₁`, none in the collar, the
layer is `j`, and the `j`-block of a site of the box is carried onto the `j`-block of its image.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField.Def6

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

/-- **`levelGS j` of two tori corresponds under `boxMap` on the box of radius `ρ`.** -/
theorem gsCorr_levelGS (hj1 : 1 ≤ j) (hj : j ≤ K) {ρ : ℕ}
    (hn : 2 * (ρ + L ^ j) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + L ^ j) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K) :
    GSCorr (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K))
      {z | InBox d ρ ((N₁ * L ^ m₁) * L ^ K) z} := by
  classical
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hΩ := fun z => levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj1 hj z
  have hΩ' := fun z => levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj1 hj z
  refine ⟨fun z _ => ⟨fun _ => hΩ z, fun _ => hΩ' _⟩, fun z _ => ?_, fun z hz => ?_⟩
  · exact ⟨fun h => absurd h (not_mem_collar_levelGS hj1 hj _),
      fun h => absurd h (not_mem_collar_levelGS hj1 hj _)⟩
  · have hl := layerIndex_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj1 hj z
    have hl' := layerIndex_levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj1 hj
      (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K) z)
    refine ⟨fun _ => hΩ' _, fun _ => by rw [hl, hl'], fun _ => ?_, fun _ => ?_⟩
    · rw [hl]
      have hbox : ∀ x ∈ box (cbase (L ^ j) z) (L ^ j),
          InBox d (ρ + L ^ j) ((N₁ * L ^ m₁) * L ^ K) x :=
        fun x hx => inBox_of_mem_cell (a := L ^ j) (by omega) hz hx
      have := blk_image (r := ρ + L ^ j) (j := j)
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) hj
        (by omega) z hbox
      exact_mod_cast this
    · rw [hl]
      intro a ha b hb hab
      have hbox : ∀ x ∈ box (cbase (L ^ j) z) (L ^ j),
          InBox d (ρ + L ^ j) ((N₁ * L ^ m₁) * L ^ K) x :=
        fun x hx => inBox_of_mem_cell (a := L ^ j) (by omega) hz hx
      have hbl : ∀ x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).blk
          j z, InBox d (ρ + L ^ j) ((N₁ * L ^ m₁) * L ^ K) x := by
        intro x hx
        refine hbox x ?_
        rw [← jBlock_eq_iff_mem_box hj]
        exact GeneratingSet.mem_blk.1 hx
      exact boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ j) + 1 < (N₁' * L ^ m₁) * L ^ K))
        (hbl a ha) (hbl b hb) hab

end Balaban.Polymer.TwoTorusStep
