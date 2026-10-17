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

section DomRec

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L]

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "σAc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tA)
set_option hygiene false in
local notation "σBi" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tB)⁻¹
set_option hygiene false in
local notation "σBc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tB)

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The recentring map is the composite of the translation, the box map and the inverse
translation. -/
theorem image_recentred (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    (fun x => bm (x + tA) - tB) '' Y =
      (Equiv.addRight tB).symm '' (bm '' ((Equiv.addRight tA) '' Y)) := by
  ext z
  simp only [Set.mem_image, Equiv.coe_addRight, Equiv.coe_addRight, exists_exists_and_eq_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [sub_eq_add_neg]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simp [sub_eq_add_neg]⟩

/-- **The blocks of a recentred set** are the images of its blocks under the recentred cube map. -/
theorem blocksOf_recentred {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnc : 2 * R + aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnc' : 2 * R + aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) :
    blocksOf m₀ (k + 1) Set.univ ((fun x => bm (x + tA) - tB) '' Y) =
      (blocksOf m₀ (k + 1) Set.univ Y).image (fun b => σBi (σc (σAc b))) := by
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hbox : ∀ x ∈ (Equiv.addRight tA) '' Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rintro _ ⟨y, hy, rfl⟩
    exact hY y hy
  rw [image_recentred]
  have h1 : (Equiv.addRight tB).symm = (Equiv.addRight tB)⁻¹ := rfl
  rw [h1, blocksOf_image_sym hN' (inv_mem hσB), blocksOf_image_boxMap hN hN' hnc hnc' hbox,
    blocksOf_image_sym hN hσA, Finset.image_image, Finset.image_image]
  rfl

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- A set lies in the image family of `𝒴` under `Z ↦ e '' Z` iff its preimage lies in `𝒴`. -/
theorem mem_image_image_iff {α : Type*} (e : Equiv.Perm α) (𝒴 : Finset (Set α)) (Y : Set α) :
    Y ∈ 𝒴.image (fun Z => e '' Z) ↔ e.symm '' Y ∈ 𝒴 := by
  classical
  rw [Finset.mem_image]
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    rwa [Equiv.symm_image_image]
  · intro h
    exact ⟨_, h, Equiv.image_symm_image _ _⟩

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- The coordinates of the preimage under the translation: if `y ∈ e.symm '' Y` with `e = + tA`
then `y + tA ∈ Y`. -/
theorem add_mem_of_mem_symm_image {tA : CTorus d L N₁ m₁ (k + 1)}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} {y : CTorus d L N₁ m₁ (k + 1)}
    (hy : y ∈ (Equiv.addRight tA).symm '' Y) : y + tA ∈ Y := by
  obtain ⟨z, hz, rfl⟩ := hy
  simpa using hz

/-- **The kernels under the recentring map.**  Let the domain families `𝒴`, `𝒴'` of disjoint
domains correspond under `φ x = bm (x + tA) - tB` on the domains whose translate lies in the box, the
coefficients agree on corresponding domains, and `T₁` be a set of cubes whose translates lie in the
box.  Then the kernels at the recentred cubes and at `T₁` agree. -/
theorem obsHker_rec {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) →
      ((fun x => bm (x + tA) - tB) '' Y ∈ 𝒴' ↔ Y ∈ 𝒴))
    (c : Set (CTorus d L N₁ m₁ (k + 1)) → ℂ) (c' : Set (CTorus d L N₁' m₁ (k + 1)) → ℂ)
    (hc : ∀ Y ∈ 𝒴, (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) →
      c' ((fun x => bm (x + tA) - tB) '' Y) = c Y)
    (T₁ : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hT₁ : ∀ b ∈ T₁, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    obsHker 𝒴' c' m₀ (T₁.image (fun b => σBi (σc (σAc b)))) = obsHker 𝒴 c m₀ T₁ := by
  classical
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hinjA := (Equiv.addRight tA).injective.image_injective
  have hinjB := (Equiv.addRight tB).injective.image_injective
  -- the translated families
  set 𝒴At : Finset (Set (CTorus d L N₁ m₁ (k + 1))) := 𝒴.image (fun Y => (Equiv.addRight tA) '' Y)
    with h𝒴At
  set 𝒴Bt : Finset (Set (CTorus d L N₁' m₁ (k + 1))) :=
    𝒴'.image (fun Y => (Equiv.addRight tB) '' Y) with h𝒴Bt
  have stepA := obsHker_sym hN hσA (𝒴 := 𝒴) (𝒴' := 𝒴At)
    (fun Y => by simp only [h𝒴At, Finset.mem_image]; exact ⟨fun ⟨Z, hZ, h⟩ => by
      rwa [← hinjA h], fun h => ⟨Y, h, rfl⟩⟩)
    (c := c) (c' := fun Y' => c ((Equiv.addRight tA).symm '' Y'))
    (fun Y _ => by rw [Equiv.symm_image_image]) T₁
  have stepB := obsHker_sym hN' hσB (𝒴 := 𝒴') (𝒴' := 𝒴Bt)
    (fun Y => by simp only [h𝒴Bt, Finset.mem_image]; exact ⟨fun ⟨Z, hZ, h⟩ => by
      rwa [← hinjB h], fun h => ⟨Y, h, rfl⟩⟩)
    (c := c') (c' := fun Y' => c' ((Equiv.addRight tB).symm '' Y'))
    (fun Y _ => by rw [Equiv.symm_image_image]) (T₁.image (fun b => σBi (σc (σAc b))))
  have hcomp : (T₁.image (fun b => σBi (σc (σAc b)))).image σBc = (T₁.image σAc).image σc := by
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr (fun b _ => cubeMap_cubeMap_inv_sym hN' tB htB _)
  have hT1 : ∀ b ∈ T₁.image σAc, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro b hb x hx
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    rw [cubeMap_translate_val hN tA htA] at hx
    have hx' : x - tA ∈ box b0.1 aK :=
      (Balaban.Localization.DecEquiv.mem_box_add_iff _ tA (x - tA) _).1 (by simpa using hx)
    simpa using hT₁ b0 hb0 (x - tA) hx'
  have hdjA : ∀ Y ∈ 𝒴At, IsDj m₀ (k + 1) Y := by
    intro Y hY
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hY
    exact isDj_image_translate hN tA htA (hdj Z hZ)
  have hdjB : ∀ Y ∈ 𝒴Bt, IsDj m₀ (k + 1) Y := by
    intro Y hY
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hY
    exact isDj_image_translate hN' tB htB (hdj' Z hZ)
  have hsymA : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (Equiv.addRight tA) '' ((Equiv.addRight tA).symm '' Y) = Y := fun Y => by
    rw [← Set.image_comp]; simp
  have mid := obsHker_twoTorus_of_mem hN hN' hnF hnF' hdjA hdjB
    (𝒴 := 𝒴At) (𝒴' := 𝒴Bt)
    (fun Y hYR => by
      have hbx : ∀ y ∈ (Equiv.addRight tA).symm '' Y,
          InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) := fun y hy =>
        hYR _ (add_mem_of_mem_symm_image hy)
      have h1 := hmem _ hbx
      rw [image_recentred, hsymA] at h1
      rw [h𝒴Bt, h𝒴At, mem_image_image_iff, mem_image_image_iff]
      exact h1)
    (fun Y' => c ((Equiv.addRight tA).symm '' Y')) (fun Y' => c' ((Equiv.addRight tB).symm '' Y'))
    (fun Y hY hYR => by
      have hY0 : (Equiv.addRight tA).symm '' Y ∈ 𝒴 := (mem_image_image_iff _ _ _).1 hY
      have hbx : ∀ y ∈ (Equiv.addRight tA).symm '' Y,
          InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) := fun y hy =>
        hYR _ (add_mem_of_mem_symm_image hy)
      have h1 := hc _ hY0 hbx
      rw [image_recentred, hsymA] at h1
      exact h1) (T₁.image σAc) hT1
  rw [← stepB, hcomp, mid, stepA]

set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- **The recentring map is injective on the sets of the box.** -/
theorem image_recentred_inj {R : ℕ}
    (hn' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    {Y₁ Y₂ : Set (CTorus d L N₁ m₁ (k + 1))}
    (h₁ : ∀ y ∈ Y₁, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (h₂ : ∀ y ∈ Y₂, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA))
    (h : (fun x => bm (x + tA) - tB) '' Y₁ = (fun x => bm (x + tA) - tB) '' Y₂) : Y₁ = Y₂ := by
  rw [image_recentred, image_recentred] at h
  have h1 := (Equiv.addRight tB).symm.injective.image_injective h
  have hbx : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))),
      (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) →
      ∀ x ∈ (Equiv.addRight tA) '' Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rintro Y hY _ ⟨y, hy, rfl⟩
    exact hY y hy
  have h2 := image_boxMap_inj hn' (hbx _ h₁) (hbx _ h₂) h1
  exact (Equiv.addRight tA).injective.image_injective h2

/-- **Preimages of the sets with blocks in the recentred cubes.**  For a set `T` of cubes whose
translates lie in the box and a domain `Y'` of the second torus whose blocks lie in the image of `T`
under the recentred cube map, there is a set `Y` whose translate lies in the box, with
`φ '' Y = Y'` and blocks in `T`. -/
theorem preimage_recentred {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y' : Set (CTorus d L N₁' m₁ (k + 1))} (hY' : IsDj m₀ (k + 1) Y')
    (hY'T : blocksOf m₀ (k + 1) Set.univ Y' ⊆ T.image (fun b => σBi (σc (σAc b)))) :
    ∃ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) ∧
      (fun x => bm (x + tA) - tB) '' Y = Y' ∧ blocksOf m₀ (k + 1) Set.univ Y ⊆ T := by
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hinjA := cubeMap_injective_sym hN hσA
  have hT1 : ∀ b ∈ T.image σAc, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro b hb x hx
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    rw [cubeMap_translate_val hN tA htA] at hx
    have hx' : x - tA ∈ box b0.1 aK :=
      (Balaban.Localization.DecEquiv.mem_box_add_iff _ tA (x - tA) _).1 (by simpa using hx)
    simpa using hT b0 hb0 (x - tA) hx'
  have hD : IsDj m₀ (k + 1) ((Equiv.addRight tB) '' Y') := isDj_image_translate hN' tB htB hY'
  have hcomp : (T.image (fun b => σBi (σc (σAc b)))).image σBc = (T.image σAc).image σc := by
    rw [Finset.image_image, Finset.image_image]
    exact Finset.image_congr (fun b _ => cubeMap_cubeMap_inv_sym hN' tB htB _)
  have hsub : blocksOf m₀ (k + 1) Set.univ ((Equiv.addRight tB) '' Y') ⊆
      (T.image σAc).image σc := by
    rw [← hcomp, blocksOf_image_sym hN' hσB]
    exact Finset.image_subset_image hY'T
  obtain ⟨-, hZR, hZimg, hZT⟩ := preimage_of_blocksOf_subset_image hN hN' hnL hnL' hT1 hD hsub
  refine ⟨(Equiv.addRight tA).symm '' (bm' '' ((Equiv.addRight tB) '' Y')), ?_, ?_, ?_⟩
  · intro y hy
    exact hZR _ (add_mem_of_mem_symm_image hy)
  · rw [image_recentred, Equiv.image_symm_image, hZimg, Equiv.symm_image_image]
  · have h1 := blocksOf_image_sym hN hσA ((Equiv.addRight tA).symm '' (bm' '' ((Equiv.addRight tB) '' Y')))
    rw [Equiv.image_symm_image] at h1
    intro b hb
    have : σAc b ∈ T.image σAc := hZT (by rw [h1]; exact Finset.mem_image_of_mem _ hb)
    obtain ⟨b1, hb1, he⟩ := Finset.mem_image.1 this
    rwa [← hinjA he]

end DomRec

end Balaban.Polymer.TwoTorusStep
