/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsAct

/-!
# The marked geometry of the energy coefficient under the recentring map (blocker 7)

The marks of the energy coefficient of a root `z` are anchored at the bridge labels of `z`: the
bridges `bridge z Y` of the domains `Y` of the marked pairs `(b, Y)` (domains of the local covers of
the blocks `b`, nearest-neighbour thickening of `Y` meeting the fine block of `z`).  This file proves
the translation covariance of this geometry on one torus, for translations `t` by multiples of the
cell side (`τ = t / L^(k+1)` on the coarse torus), and composes it with the two-torus statements of
`TwoTorusCoef` and `TwoTorusE1Coef` into the recentred form, `φ x = bm (x + tA) - tB`,
`ψ b = bc (b + τA) - τB`.

* One torus: `blockIndex_add_coarse`, `fineBlock_add_coarse`, `adj_add_iff`, `psiThick_image_add`,
  `rootAct_addRight`, `rootCube_add_coarse`, `rootCube_mem_blocksOf_add`, `joinCubes_add`,
  `bridge_add`, `mem_markedIdx_add`, `mem_bridgeFamily_add_iff`.
* Recentred: `image_add_recentred`, `markedPair_recentred_iff` (with `markedPair_boxMap_iff`),
  `mem_bridgeFamily_recentred_iff` (with `mem_bridgeFamily_boxMap_iff`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale
  Balaban.Localization.DecEquiv

section Translate

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

set_option hygiene false in
local notation "τ" => (fun μ => ((((t μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))

/-- The block index of a translate by a multiple of the block side. -/
theorem blockIndex_add_coarse (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ (k + 1) ∣ (t μ).val)
    (x : CTorus d L N₁ m₁ (k + 1)) : blockIndex (x + t) = blockIndex x + τ :=
  jBlock_add_eq le_rfl t ht x

/-- The fine block of the translated coarse site is the translate of the fine block. -/
theorem fineBlock_add_coarse (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ (k + 1) ∣ (t μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    fineBlock (m₁ := m₁) (K := k + 1) (z + τ) = (Equiv.addRight t) '' fineBlock z := by
  ext x
  constructor
  · intro hx
    refine ⟨x - t, ?_, by simp⟩
    have h := blockIndex_add_coarse t ht (x - t)
    rw [sub_add_cancel, mem_fineBlock.1 hx] at h
    exact mem_fineBlock.2 (add_right_cancel h).symm
  · rintro ⟨y, hy, rfl⟩
    exact mem_fineBlock.2 (by rw [Equiv.coe_addRight, blockIndex_add_coarse t ht y,
      mem_fineBlock.1 hy])

omit [NeZero N₁] [NeZero L] in
/-- Translation preserves the nearest-neighbour relation. -/
theorem adj_add_iff (t x y : CTorus d L N₁ m₁ (k + 1)) : Adj (x + t) (y + t) ↔ Adj x y := by
  unfold Adj
  refine exists_congr fun μ => or_congr ?_ ?_
  · constructor
    · intro h; exact add_right_cancel (h.trans (by abel))
    · intro h; rw [h]; abel
  · constructor
    · intro h; exact add_right_cancel (h.trans (by abel))
    · intro h; rw [h]; abel

omit [NeZero N₁] [NeZero L] in
/-- The nearest-neighbour thickening of a translate is the translate of the thickening. -/
theorem psiThick_image_add (t : CTorus d L N₁ m₁ (k + 1)) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    psiThick ((Equiv.addRight t) '' Y) = (Equiv.addRight t) '' psiThick Y := by
  ext y
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + t := ⟨y - t, by abel⟩
  rw [show y + t = (Equiv.addRight t) y from rfl, (Equiv.addRight t).injective.mem_set_image]
  constructor
  · rintro (⟨x, hx, hxy⟩ | ⟨_, ⟨x, hx, rfl⟩, hxy⟩)
    · exact Or.inl ((Equiv.addRight t).injective hxy ▸ hx)
    · exact Or.inr ⟨x, hx, (adj_add_iff t x y).1 hxy⟩
  · rintro (hy | ⟨x, hx, hxy⟩)
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨x + t, ⟨x, hx, rfl⟩, (adj_add_iff t x y).2 hxy⟩

/-- The root of the translated coarse site is the root action of the translation. -/
theorem rootAct_addRight (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ (k + 1) ∣ (t μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    rootAct (Equiv.addRight t) z = z + τ := by
  show blockIndex (rootSite z + t) = z + τ
  rw [blockIndex_add_coarse t ht, blockIndex_rootSite]

/-- The root cube of the translated coarse site is the translate of the root cube. -/
theorem rootCube_add_coarse (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    (rootCube (m₀ := m₀) (z + τ)).1 = (rootCube (m₀ := m₀) z).1 + t := by
  have hr := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) t ht)
  have ht1 : ∀ μ, L ^ (k + 1) ∣ (t μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (ht μ)
  rw [← rootAct_addRight t ht1 z, rootCube_rootAct hN hr, cubeMap_translate_val hN t ht]

/-- The root cube is a cube of the translate iff it is a cube of the set. -/
theorem rootCube_mem_blocksOf_add (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    rootCube (m₀ := m₀) (z + τ) ∈ blocksOf m₀ (k + 1) Set.univ ((Equiv.addRight t) '' Y) ↔
      rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y := by
  rw [mem_blocksOf, mem_blocksOf, rootCube_add_coarse hN t ht z, ← image_box_translate]
  exact Set.image_subset_image_iff (Equiv.addRight t).injective

/-- The cubes joining the translate to the translated root are the translates of the joining cubes. -/
theorem joinCubes_add (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    joinCubes m₀ (z + τ) ((Equiv.addRight t) '' Y) =
      (joinCubes m₀ z Y).image (Equiv.addRight t) := by
  have hdv := cellSide_dvd (L := L) (m₁ := m₁) (K := k + 1) hN (le_refl (k + 1))
  have hts : ∀ μ, cellSide L m₀ m₁ (k + 1) ∣ (t μ).val := cellSide_dvd_translate (le_refl _) ht
  ext p
  obtain ⟨p, rfl⟩ : ∃ p', p = p' + t := ⟨p - t, by abel⟩
  rw [show p + t = (Equiv.addRight t) p from rfl,
    (Equiv.addRight t).injective.mem_finset_image]
  simp only [joinCubes, rootCubes, Finset.mem_filter, Finset.mem_univ, true_and,
    rootCube_add_coarse hN t ht z, Equiv.coe_addRight]
  constructor
  · rintro ⟨⟨hal, hr⟩, t', htal, ht'⟩
    refine ⟨⟨(aligned_add_iff hdv p t hts).1 hal, (mem_box_add_iff _ _ _ _).1 hr⟩, t' - t,
      (aligned_add_iff hdv (t' - t) t hts).1 (by rwa [sub_add_cancel]), fun x hx => ?_⟩
    have hx' : x + t ∈ box t' (cellSide L m₀ m₁ (k + 1)) := by
      have := (mem_box_add_iff (t' - t) t x _).2 hx
      rwa [sub_add_cancel] at this
    obtain ⟨⟨y, hy, hyx⟩, hb⟩ := ht' hx'
    have hyx' : y = x := add_right_cancel hyx
    exact ⟨hyx' ▸ hy, (mem_box_add_iff _ _ _ _).1 hb⟩
  · rintro ⟨⟨hal, hr⟩, t₀, htal, ht₀⟩
    refine ⟨⟨(aligned_add_iff hdv p t hts).2 hal, (mem_box_add_iff _ _ _ _).2 hr⟩, t₀ + t,
      (aligned_add_iff hdv t₀ t hts).2 htal, fun x' hx' => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x, x' = x + t := ⟨x' - t, by abel⟩
    obtain ⟨hxY, hxp⟩ := ht₀ ((mem_box_add_iff _ _ _ _).1 hx')
    exact ⟨⟨x, hxY, rfl⟩, (mem_box_add_iff _ _ _ _).2 hxp⟩

/-- **The bridge of a translate to the translated root** is the translate of the bridge. -/
theorem bridge_add (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    bridge m₀ (z + τ) ((Equiv.addRight t) '' Y) = (Equiv.addRight t) '' bridge m₀ z Y := by
  have hiff := rootCube_mem_blocksOf_add hN t ht z Y
  unfold bridge
  by_cases h : rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y
  · simp only [hiff.2 h, h, ↓reduceIte]
  · have h' : rootCube (m₀ := m₀) (z + τ) ∉ blocksOf m₀ (k + 1) Set.univ ((Equiv.addRight t) '' Y) :=
      fun h' => h (hiff.1 h')
    simp only [h, h', ↓reduceIte]
    rw [joinCubes_add hN t ht z Y, Set.image_union,
      Set.image_iUnion₂, Finset.set_biUnion_finset_image]
    congr 1
    exact Set.iUnion₂_congr fun p _ => (image_box_translate p t _).symm

end Translate

section MarkedTranslate

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ} {ϱ : ℝ}

set_option hygiene false in
local notation "τ" => (fun μ => ((((t μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "domA" => fun b : TA => polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))

/-- **The marked pairs of a translated root**: `(b + τ, Y + t)` is a marked pair of the root `z + τ`
iff `(b, Y)` is a marked pair of `z` (domains of the local covers of the blocks, all blocks read). -/
theorem mem_markedIdx_add (hGA : IsLevel (GA) (k + 1)) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (z b : TA) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    (b + τ, (Equiv.addRight t) '' Y) ∈ markedIdx (fun _ : TA =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) (z + τ) ↔
      (b, Y) ∈ markedIdx (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) z := by
  have ht1 : ∀ μ, L ^ (k + 1) ∣ (t μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (ht μ)
  have hdom : (Equiv.addRight t) '' Y ∈ polyDom (GA)
      (LocalCover.nbhdF m₀ (LocalCover.blockSite k (b + τ))) m₀ k
      (LocalCover.fam m₀ (LocalCover.blockSite k (b + τ))) ↔
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) := by
    rw [blockSite_add_coarse t ht1 b, fam_translate hN t ht]
    exact polyDom_translate hGA hN t ht
      (LocalCover.covSetup (m₀ := m₀) hGA hN (j := k) le_rfl (LocalCover.blockSite k b))
      (nbhdF_translate hN t ht _) Y
  have hreads : ∀ w : TA, ((Set.univ : Set (CTorus d L N₁ m₁ (k + 1))) ∩
      fineBlock (m₁ := m₁) (K := k + 1) w).Nonempty :=
    fun w => ⟨rootSite w, trivial, rootSite_mem_fineBlock w⟩
  have hthick : (psiThick ((Equiv.addRight t) '' Y) ∩ fineBlock (m₁ := m₁) (K := k + 1) (z + τ)).Nonempty
      ↔ (psiThick Y ∩ fineBlock (m₁ := m₁) (K := k + 1) z).Nonempty := by
    rw [psiThick_image_add, fineBlock_add_coarse t ht1, ← Set.image_inter (Equiv.addRight t).injective,
      Set.image_nonempty]
  rw [mem_markedIdx, mem_markedIdx]
  simp only [hreads, true_and]
  rw [hdom, hthick]

/-- **The bridge labels of a translated root** are the translates of the bridge labels. -/
theorem mem_bridgeFamily_add_iff (hGA : IsLevel (GA) (k + 1)) (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (z : TA) (Y' : Set (CTorus d L N₁ m₁ (k + 1))) :
    (Equiv.addRight t) '' Y' ∈ bridgeFamily m₀ (fun _ : TA =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) (z + τ) ↔
      Y' ∈ bridgeFamily m₀ (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) z := by
  have hinj := Set.image_injective.2 (Equiv.addRight t).injective
  rw [mem_bridgeFamily_iff_pair, mem_bridgeFamily_iff_pair]
  constructor
  · rintro ⟨b', Y, hq, hbr⟩
    obtain ⟨Y₀, rfl⟩ : ∃ Y₀, Y = (Equiv.addRight t) '' Y₀ :=
      ⟨(Equiv.addRight t).symm '' Y, by rw [Equiv.image_symm_image]⟩
    obtain ⟨b, rfl⟩ : ∃ b, b' = b + τ := ⟨b' - τ, by abel⟩
    refine ⟨b, Y₀, (mem_markedIdx_add hGA hN t ht z b Y₀).1 hq, hinj ?_⟩
    rw [← bridge_add hN t ht z Y₀, hbr]
  · rintro ⟨b, Y, hq, hbr⟩
    exact ⟨b + τ, (Equiv.addRight t) '' Y, (mem_markedIdx_add hGA hN t ht z b Y).2 hq,
      by rw [bridge_add hN t ht z Y, hbr]⟩

end MarkedTranslate

section MarkedRec

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "domA" => fun b : TA => polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))
set_option hygiene false in
local notation "domB" => fun b : TB => polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k b))
  m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k b))
set_option hygiene false in
local notation "τA" => (fun μ => ((((tA μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "τB" => (fun μ => ((((tB μ).val / L ^ (k + 1) : ℕ)) :
  ZMod (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))))
set_option hygiene false in
local notation "φ" => fun x : CTorus d L N₁ m₁ (k + 1) => bm (x + tA) - tB

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The translate by `tB` of a recentred set is the box-map image of the translate by `tA`. -/
theorem image_add_recentred (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (W : Set (CTorus d L N₁ m₁ (k + 1))) :
    (Equiv.addRight tB) '' ((fun x => bm (x + tA) - tB) '' W) = bm '' ((Equiv.addRight tA) '' W) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => by simp

/-- **The marked pairs of a label under the recentring map.**  For a root `z` and a block `b` of the
first torus whose root cell, region and domain `Y` and label `Y'` lie, after the translation by `tA`,
in the box of radius `R`, `(ψ b, φ '' Y)` is a marked pair of the root `ψ z` with bridge `φ '' Y'`
iff `(b, Y)` is a marked pair of `z` with bridge `Y'`, `φ x = bm (x + tA) - tB`,
`ψ b = bc (b + τA) - τB`: the translation covariance on each torus (`mem_markedIdx_add`,
`bridge_add`) composed with `markedPair_boxMap_iff`. -/
theorem markedPair_recentred_iff (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val) {R rc : ℕ}
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (R + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (R + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : TA) (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA))
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY'R : ∀ y ∈ Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (b : TA) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (hbR : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    ((bc (b + τA) - τB, (φ) '' Y) ∈ markedIdx (fun _ : TB =>
        (Set.univ : Set (CTorus d L N₁' m₁ (k + 1)))) (domB) (bc (z + τA) - τB) ∧
        bridge m₀ (bc (z + τA) - τB) ((φ) '' Y) = (φ) '' Y') ↔
      ((b, Y) ∈ markedIdx (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) z ∧
        bridge m₀ z Y = Y') := by
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tA μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)
  have hσA := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hinjA := Set.image_injective.2 (Equiv.addRight tA).injective
  have hinjB := Set.image_injective.2 (Equiv.addRight tB).injective
  have hB1 := mem_markedIdx_add (ϱ := ϱ) hGB hN' tB htB (bc (z + τA) - τB) (bc (b + τA) - τB)
    ((φ) '' Y)
  rw [sub_add_cancel, sub_add_cancel, image_add_recentred] at hB1
  have hB2 := bridge_add hN' tB htB (bc (z + τA) - τB) ((φ) '' Y)
  rw [sub_add_cancel, image_add_recentred] at hB2
  rw [← hB1, ← hinjB.eq_iff, ← hB2, image_add_recentred,
    ← (mem_markedIdx_add (ϱ := ϱ) hGA hN tA htA z b Y), ← hinjA.eq_iff, ← bridge_add hN tA htA z Y]
  refine markedPair_boxMap_iff (ϱ := ϱ) hN hN' hn hn' hnF hnF' hnH hnH' (z + τA) hz hrc ?_ ?_
    (b + τA) ((Equiv.addRight tA) '' Y) ?_ ?_
  · rw [← rootAct_addRight tA htA1 z, rootSet_rootAct hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    exact hroot x hx
  · rintro _ ⟨y, hy, rfl⟩
    exact hY'R y hy
  · rintro _ ⟨y, hy, rfl⟩
    exact hYR y hy
  · rw [blockSite_add_coarse tA htA1 b, nbhd_translate hN tA htA]
    rintro _ ⟨x, hx, rfl⟩
    exact hbR x hx

/-- **The bridge labels of a root under the recentring map**: `φ '' Y'` is a bridge label of the root
`ψ z` iff `Y'` is a bridge label of `z`, for a label and a root cell of the recentred box. -/
theorem mem_bridgeFamily_recentred_iff (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val) {R rc : ℕ}
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (R + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (R + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : TA) (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (z + τA))
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY'R : ∀ y ∈ Y', InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    (φ) '' Y' ∈ bridgeFamily m₀ (fun _ : TB => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
        (domB) (bc (z + τA) - τB) ↔
      Y' ∈ bridgeFamily m₀ (fun _ : TA => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (domA) z := by
  have htA1 : ∀ μ, L ^ (k + 1) ∣ (tA μ).val := fun μ => (pow_dvd_pow L (by omega)).trans (htA μ)
  have hσA := genSymm_mem_pavingSymGroup (GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hB := mem_bridgeFamily_add_iff (ϱ := ϱ) hGB hN' tB htB (bc (z + τA) - τB) ((φ) '' Y')
  rw [sub_add_cancel, image_add_recentred] at hB
  rw [← hB, ← mem_bridgeFamily_add_iff (ϱ := ϱ) hGA hN tA htA z Y']
  refine mem_bridgeFamily_boxMap_iff (ϱ := ϱ) hN hN' hn hn' hnF hnF' hnH hnH' (z + τA) hz hrc ?_ ?_
  · rw [← rootAct_addRight tA htA1 z, rootSet_rootAct hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    exact hroot x hx
  · rintro _ ⟨y, hy, rfl⟩
    exact hY'R y hy

end MarkedRec

end Balaban.Polymer.TwoTorusStep
