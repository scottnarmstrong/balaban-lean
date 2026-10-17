/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsSym

/-!
# Translation covariance of the observable labels

The blocks of a translated set are the translated blocks (`blocksOf_image_sym`), the single-cube
label of the translated cube is the translated label, and the first-order labels of the marks
`(u, a)` and `(unitAct u, a)` correspond.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence

section Labels

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **The blocks of the image of a set under a paving symmetry** are the images of its blocks. -/
theorem blocksOf_image_sym (hN : L ^ m₀ ∣ N₁) {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    (Y : Set (CTorus d L N₁ m₁ K)) :
    blocksOf m₀ K Set.univ (σ '' Y) =
      (blocksOf m₀ K Set.univ Y).image (Balaban.Fluctuation.cubeMap σ) := by
  ext b
  rw [Finset.mem_image, mem_blocksOf]
  constructor
  · intro h
    refine ⟨Balaban.Fluctuation.cubeMap σ⁻¹ b, mem_blocksOf.2 ?_, ?_⟩
    · rw [box_cubeMap hN (inv_mem hσ)]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h hx
      have : σ⁻¹ x = y := by rw [← hyx]; simp
      rw [this]; exact hy
    · have := cubeMap_inv hN (inv_mem hσ) b
      rwa [inv_inv] at this
  · rintro ⟨b0, hb0, rfl⟩
    rw [box_cubeMap hN hσ]
    exact Set.image_mono (mem_blocksOf.1 hb0)

/-- A translation by a cell-aligned vector moves the base of a cube by the vector. -/
theorem cubeMap_translate_val (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val)
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :
    (Balaban.Fluctuation.cubeMap (Equiv.addRight t) c).1 = c.1 + t := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  rw [Balaban.Fluctuation.cubeMap_val]
  show cbase (cellSide L m₀ m₁ K) (c.1 + t) = c.1 + t
  rw [Balaban.Localization.DecEquiv.cbase_add_translate hdvd c.1 t (cellSide_dvd_translate (le_refl K) ht),
    cbase_eq_of_mem_box hdvd c.2.1 (mem_box_self _ (cellSide_pos m₀ m₁ K))]

/-- The single-cube label of the translated cube is the translated label. -/
theorem obsCubeLab_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val)
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :
    box (Balaban.Fluctuation.cubeMap (Equiv.addRight t) c).1 (L * cellSide L m₀ m₁ K) =
      (Equiv.addRight t) '' box c.1 (L * cellSide L m₀ m₁ K) := by
  rw [cubeMap_translate_val hN t ht, image_box_translate]

end Labels

end Balaban.Polymer.TwoTorusStep
