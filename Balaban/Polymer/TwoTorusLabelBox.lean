/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusE1Coef

/-!
# Domains whose blocks lie in a set of blocks of the box

`inBox_of_blocksOf_subset`: a domain whose blocks lie in a set `T` of blocks of the box lies in the
box.  `exists_preimage_label`: a domain of the second torus whose blocks lie in `cubeMap '' T` has a
preimage domain of the box whose blocks lie in `T`.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.Polymer Balaban.Multiscale

section LabelBox

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))

omit [NeZero N₁'] in
/-- **A domain whose blocks lie in a set `T` of blocks of the box lies in the box.** -/
theorem inBox_of_blocksOf_subset (hN : L ^ m₀ ∣ N₁) {R : ℕ}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hDj : IsDj m₀ (k + 1) Y)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L m₀ m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hY : blocksOf m₀ (k + 1) Set.univ Y ⊆ T) :
    ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  intro x hx
  have hs := sitesOf_blocksOf hN (le_refl (k + 1)) isPiUnion_univ_aux hDj.2.1
  have hx' : x ∈ sitesOf (blocksOf m₀ (k + 1) Set.univ Y) := by rw [hs]; exact ⟨hx, trivial⟩
  obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx'
  exact hT b (hY hb) x hxb

/-- **A domain of the second torus whose blocks lie in the image of `T` has a preimage domain of
the box with the blocks in `T`.** -/
theorem exists_preimage_label (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') {R : ℕ}
    (hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hr : 2 * R + L * cellSide L m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hc : 2 * R + cellSide L m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hc' : 2 * R + cellSide L m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L m₀ m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y' : Set (CTorus d L N₁' m₁ (k + 1))} (hDj' : IsDj m₀ (k + 1) Y')
    (hY' : blocksOf m₀ (k + 1) Set.univ Y' ⊆ T.image
      (cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1) hN hN'
        (le_refl (k + 1)))) :
    (∀ x ∈ bm' '' Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) ∧
      blocksOf m₀ (k + 1) Set.univ (bm' '' Y') ⊆ T ∧ bm '' (bm' '' Y') = Y' := by
  have hT' : ∀ x ∈ sitesOf T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
    exact hT b hb x hxb
  have hsT := sitesOf_image_cubeMap hN hN' (le_refl (k + 1)) (r := R) hr T hT'
  have hs' := sitesOf_blocksOf hN' (le_refl (k + 1)) isPiUnion_univ_aux hDj'.2.1
  have hy'R : ∀ x' ∈ Y', InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x' := by
    intro x' hx'
    have h1 : x' ∈ sitesOf (blocksOf m₀ (k + 1) Set.univ Y') := by
      rw [hs']; exact ⟨hx', trivial⟩
    obtain ⟨b', hb', hxb'⟩ := mem_sitesOf.1 h1
    have h2 : x' ∈ sitesOf (T.image
      (cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1) hN hN'
        (le_refl (k + 1)))) := mem_sitesOf.2 ⟨b', hY' hb', hxb'⟩
    rw [hsT] at h2
    obtain ⟨w, hw, rfl⟩ := h2
    exact inBox_boxMap hm' (hT' w hw)
  have hYR : ∀ x ∈ bm' '' Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨x', hx', rfl⟩
    exact inBox_boxMap hm (hy'R x' hx')
  have hYimg : bm '' (bm' '' Y') = Y' :=
    image_image_boxMap (n' := (N₁ * L ^ m₁) * L ^ (k + 1)) hm hy'R
  refine ⟨hYR, ?_, hYimg⟩
  intro b hb
  have hbimg : cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1) hN hN'
      (le_refl (k + 1)) b ∈ blocksOf m₀ (k + 1) Set.univ (bm '' (bm' '' Y')) := by
    rw [blocksOf_image_boxMap hN hN' hc hc' hYR]
    exact Finset.mem_image_of_mem _ hb
  rw [hYimg] at hbimg
  obtain ⟨b₂, hb₂, he⟩ := Finset.mem_image.1 (hY' hbimg)
  have hb₂R := hT b₂ hb₂ b₂.1 (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1)))
  have hbR := hYR b.1 ((mem_blocksOf.1 hb) (mem_box_self _ (cellSide_pos m₀ m₁ (k + 1))))
  have h1 := congrArg Subtype.val he
  rw [cubeMap_val, cubeMap_val] at h1
  have h2 : b₂ = b := Subtype.ext (boxMap_inj (hm' := hm') hb₂R hbR h1)
  exact h2 ▸ hb₂

end LabelBox

end Balaban.Polymer.TwoTorusStep
