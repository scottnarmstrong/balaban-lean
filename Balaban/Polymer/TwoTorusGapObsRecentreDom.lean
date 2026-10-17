/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsRecentreMarks

/-!
# The domains of the observable under the recentring map

A translation by a multiple of the cell side preserves the domains `𝒟_j` (nonempty connected unions
of `π'_j`-cubes); the recentring map `φ x = bm (x + tA) - tB` carries domains of the box to domains,
and the blocks of the image are the images of the blocks under the recentred cube map.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited Balaban.Inhabited.LevelStep

section Dom

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **Translation preserves the domains `𝒟_K`** (translation by a multiple of the cell side). -/
theorem isDj_image_translate (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (K + m₀ + m₁) ∣ (t μ).val) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) : IsDj m₀ K ((Equiv.addRight t) '' Y) := by
  refine ⟨hY.1.image _, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb, hyb, hbY⟩ := hY.2.1 y hy
    refine ⟨b + t, (Balaban.Localization.DecEquiv.aligned_add_iff (cellSide_dvd hN (le_refl K)) b t
      (cellSide_dvd_translate (le_refl K) ht)).2 hb,
      (Balaban.Localization.DecEquiv.mem_box_add_iff b t y _).2 hyb, ?_⟩
    rw [← image_box_translate]
    exact Set.image_mono hbY
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    refine Relation.ReflTransGen.lift
      (p := fun u v => u ∈ (Equiv.addRight t) '' Y ∧ v ∈ (Equiv.addRight t) '' Y ∧ Nbr u v)
      (fun u : CTorus d L N₁ m₁ K => (Equiv.addRight t) u) (fun u v huv => ?_) x y
      (hY.2.2 x hx y hy)
    refine ⟨⟨u, huv.1, rfl⟩, ⟨v, huv.2.1, rfl⟩, ?_⟩
    obtain ⟨μ, hμ | hμ⟩ := huv.2.2
    · exact ⟨μ, Or.inl (by simp only [Equiv.coe_addRight, hμ]; abel)⟩
    · exact ⟨μ, Or.inr (by simp only [Equiv.coe_addRight, hμ]; abel)⟩

end Dom

end Balaban.Polymer.TwoTorusStep
