/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsRecentreIdx

/-!
# The marks of the observable under the recentring map

The correspondence `(u, a) ↦ (ι u, a)` of the first-order marks, `ι = unitAct_B⁻¹ ∘ ιu ∘ unitAct_A`:
injective, onto the marks with label blocks in the recentred cubes, and carrying the first-order marks
(`blockMarkC`) and the unit vectors of the marks to each other.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited Balaban.Inhabited.LevelStep

section RecentreMarks

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : (SB).U)
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
set_option hygiene false in
local notation "ιr" u:max => (unitAct (SB).G' SSB hUB).symm (ιu (unitAct (SA).G' SSA hUA u))

/-- A domain whose cube label lies in a set `T` of cubes whose translates lie in the box lies,
translated, in the box. -/
theorem inBox_rec_of_blocksOf_subset {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (tA : CTorus d L N₁ m₁ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : IsDj m₀ (k + 1) Y)
    (hYT : blocksOf m₀ (k + 1) Set.univ Y ⊆ T) :
    ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) := by
  intro x hx
  have hs := sitesOf_blocksOf hN (le_refl (k + 1)) isPiUnion_univ_aux hY.2.1
  have hx' : x ∈ sitesOf (blocksOf m₀ (k + 1) Set.univ Y) := by rw [hs]; exact ⟨hx, trivial⟩
  obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx'
  exact hT b (hYT hb) x hxb

/-- **The first-order label of a mark with blocks in `T`, recentred.** -/
theorem obsY1_label_rec_inBox (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (tA : CTorus d L N₁ m₁ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Lb₀ : Type} (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ Lb₀)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y)
    (i : ObsMarkIdx (SA))
    (hi : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i)) ⊆ T) :
    (∀ x ∈ box ((SA).cellOf m₀ i.1).1 (L * aK), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) ∧
      ∃ x₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₀ + tA) ∧ unitPt (SA).hG' x₀ = i.1 := by
  have h1 := inBox_rec_of_blocksOf_subset hN tA hT ((obsLab Lab₀ hdj).isDj _) hi
  refine ⟨h1, ?_⟩
  obtain ⟨x, hxu, hxb⟩ := exists_site_of_unitPt (SA) m₀ i.1
  exact ⟨x, h1 x (box_mono _ cellSide_le_mul hxb), Subtype.ext hxu⟩

set_option hygiene false in
local notation "ιv" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) :
    unitPts (GB))

/-- `ι` is injective on the unit points of the sites whose translate lies in the box. -/
theorem unitPt_eq_of_rec_eq {R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {tA : CTorus d L N₁ m₁ (k + 1)} {tB : CTorus d L N₁' m₁ (k + 1)}
    (SSA : LatSymm (GA) (GA) (Equiv.addRight tA)) (hUA : UnitBlockPres (Equiv.addRight tA))
    (SSB : LatSymm (GB) (GB) (Equiv.addRight tB)) (hUB : UnitBlockPres (Equiv.addRight tB))
    {x₁ x₂ : CTorus d L N₁ m₁ (k + 1)}
    (hx₁ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₁ + tA))
    (hx₂ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₂ + tA))
    (h : (unitAct (GB) SSB hUB).symm (ιv (unitAct (GA) SSA hUA (unitPt hGA x₁))) =
      (unitAct (GB) SSB hUB).symm (ιv (unitAct (GA) SSA hUA (unitPt hGA x₂)))) :
    unitPt hGA x₁ = unitPt hGA x₂ := by
  have h1v : bU (↑(unitAct (GA) SSA hUA (unitPt hGA x₁)) : UnitTorus d L N₁ m₁ k) =
      bU (↑(unitAct (GA) SSA hUA (unitPt hGA x₂)) : UnitTorus d L N₁ m₁ k) :=
    congrArg Subtype.val ((unitAct (GB) SSB hUB).symm.injective h)
  rw [unitPt_sym hGA SSA hUA, unitPt_sym hGA SSA hUA] at h1v
  have h2 := unitPt_eq_of_unitImage_eq hn hn' hGA hGB hx₁ hx₂ (Subtype.ext h1v)
  exact (unitAct (GA) SSA hUA).injective
    (((unitPt_sym hGA SSA hUA x₁).trans h2).trans (unitPt_sym hGA SSA hUA x₂).symm)

/-- **The correspondence of the first-order marks under the recentring map.**  For a set `T` of
cubes whose translates by `tA` lie in the box of radius `R`, the map `(u, a) ↦ (ι u, a)` on the marks
with label blocks in `T` carries the label blocks along the recentred cube map, is injective, and
reaches every mark of the second step with label blocks in the image of `T`. -/
theorem obsMarkLabels_rec (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (SSA : LatSymm (SA).G' (SA).G' (Equiv.addRight tA)) (hUA : UnitBlockPres (Equiv.addRight tA))
    (SSB : LatSymm (SB).G' (SB).G' (Equiv.addRight tB)) (hUB : UnitBlockPres (Equiv.addRight tB))
    (hn2 : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn2' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Lb₀ Lb₀' : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y) :
    (∀ (i : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i)) ⊆ T),
      blocksOf m₀ (k + 1) Set.univ
          ((obsLab Lab₀' hdj').ysite (obsY1 m₀ (SB) Lb₀' 𝒴' (ιr i.1, i.2))) =
        (blocksOf m₀ (k + 1) Set.univ
          ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i))).image
          (fun b => σBi (σc (σAc b)))) ∧
    (∀ (i₁ : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i₁)) ⊆ T)
      (i₂ : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i₂)) ⊆ T),
      ((ιr i₁.1, i₁.2) : ObsMarkIdx (SB)) = (ιr i₂.1, i₂.2) → i₁ = i₂) ∧
    (∀ i' : ObsMarkIdx (SB),
      blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite (obsY1 m₀ (SB) Lb₀' 𝒴' i')) ⊆
        T.image (fun b => σBi (σc (σAc b))) →
      ∃ (i : ObsMarkIdx (SA))
        (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i)) ⊆ T),
        ((ιr i.1, i.2) : ObsMarkIdx (SB)) = i') := by
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hinjA := cubeMap_injective_sym hN hσA
  refine ⟨fun i hi => ?_, fun i₁ hi₁ i₂ hi₂ h => ?_, fun i' hi' => ?_⟩
  · obtain ⟨hbox, -⟩ := obsY1_label_rec_inBox hN2 hk νS β p₁ δ hN tA hT Lab₀ hdj i hi
    exact blocksOf_obsY1_rec hN2 hk νS β p₁ δ hN hN' tA tB htA htB SSA hUA SSB hUB hn2 hnL hnL'
      Lab₀ Lab₀' hdj hdj' i _ (by simp) hbox
  · obtain ⟨-, x₁, hx₁R, hx₁⟩ := obsY1_label_rec_inBox hN2 hk νS β p₁ δ hN tA hT Lab₀ hdj i₁ hi₁
    obtain ⟨-, x₂, hx₂R, hx₂⟩ := obsY1_label_rec_inBox hN2 hk νS β p₁ δ hN tA hT Lab₀ hdj i₂ hi₂
    rw [Prod.mk.injEq] at h
    refine Prod.ext ?_ h.2
    rw [← hx₁, ← hx₂] at h
    rw [← hx₁, ← hx₂]
    exact unitPt_eq_of_rec_eq hn2 hn2' (SA).hG' (SB).hG' SSA hUA SSB hUB hx₁R hx₂R h.1
  · have hσB := genSymm_mem_pavingSymGroup
      (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
    -- the translated cubes lie in the box
    have hT1 : ∀ b ∈ T.image σAc, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      intro b hb x hx
      obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
      rw [cubeMap_translate_val hN tA htA] at hx
      have hx' : x - tA ∈ box b0.1 aK :=
        (Balaban.Localization.DecEquiv.mem_box_add_iff _ tA (x - tA) _).1 (by simpa using hx)
      simpa using hT b0 hb0 (x - tA) hx'
    obtain ⟨w, a⟩ := i'
    have e3 := blocksOf_obsY1_sym (SB) hN' tB htB SSB hUB Lab₀' Lab₀' hdj' hdj' (𝒴' := 𝒴')
      ((w, a) : ObsMarkIdx (SB))
    have hcomp : (T.image (fun b => σBi (σc (σAc b)))).image σBc = (T.image σAc).image σc := by
      rw [Finset.image_image, Finset.image_image]
      exact Finset.image_congr (fun b _ => cubeMap_cubeMap_inv_sym hN' tB htB _)
    have hsub : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite
        (obsY1 m₀ (SB) Lb₀' 𝒴' (unitAct (SB).G' SSB hUB w, a))) ⊆ (T.image σAc).image σc := by
      rw [← hcomp]
      refine e3.trans_subset ?_
      exact Finset.image_subset_image hi'
    obtain ⟨x₀, hx₀R, hux, hblk⟩ := obsY1_unitImage_surj hN2 hk νS β p₁ δ hN hN' hn2 hnL hnL'
      hT1 Lab₀ Lab₀' hdj hdj'
      ((unitAct (SB).G' SSB hUB w, a) : ObsMarkIdx (SB)) hsub
    have hu : unitAct (SA).G' SSA hUA ((unitAct (SA).G' SSA hUA).symm (unitPt (SA).hG' x₀)) =
        unitPt (SA).hG' x₀ := Equiv.apply_symm_apply _ _
    have e1 := blocksOf_obsY1_sym (SA) hN tA htA SSA hUA Lab₀ Lab₀ hdj hdj (𝒴' := 𝒴)
      (((unitAct (SA).G' SSA hUA).symm (unitPt (SA).hG' x₀), a) : ObsMarkIdx (SA))
    have e1' := (congrArg (fun m : (SA).U => blocksOf m₀ (k + 1) Set.univ
      ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 (m, a)))) hu).symm.trans e1
    refine ⟨((unitAct (SA).G' SSA hUA).symm (unitPt (SA).hG' x₀), a), ?_, ?_⟩
    · intro b hb
      have h1 : σAc b ∈ T.image σAc := hblk (by rw [e1']; exact Finset.mem_image_of_mem _ hb)
      obtain ⟨b1, hb1, he⟩ := Finset.mem_image.1 h1
      rwa [← hinjA he]
    · have h1 : ιu (unitAct (SA).G' SSA hUA
          ((unitAct (SA).G' SSA hUA).symm (unitPt (SA).hG' x₀))) = unitAct (SB).G' SSB hUB w :=
        (congrArg (fun m : (SA).U => ιu m) hu).trans hux
      exact Prod.ext ((congrArg (unitAct (SB).G' SSB hUB).symm h1).trans
        (Equiv.symm_apply_apply _ _)) rfl

/-- The hat variables correspond under the recentring map. -/
theorem hatOf_rec (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) (m₀ : ℕ) (ρ : ℝ)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁) {R : ℕ}
    {tA : CTorus d L N₁ m₁ (k + 1)} {tB : CTorus d L N₁' m₁ (k + 1)}
    {Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c} {Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c}
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
        ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) :
    ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) → ∀ i,
      (SB).hatOf m₀ ρ hp' Φ' (unitPt (SB).hG' (bm (x + tA) - tB), i) =
        (SA).hatOf m₀ ρ hp Φ (unitPt (SA).hG' x, i) := by
  intro x hx i
  simp only [StepSetting.hatOf]
  rw [hΦ x hx]

/-- **The first-order marks under the recentring map.** -/
theorem blockMarkC_rec (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {tA : CTorus d L N₁ m₁ (k + 1)} {tB : CTorus d L N₁' m₁ (k + 1)}
    {Φ : ∀ c, ((SA).blockSplit m₀ hp).Ωb c} {Φ' : ∀ c, ((SB).blockSplit m₀ hp').Ωb c}
    (hΦ : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
        ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₀ + tA))
    (a : Fin N) :
    blockMarkC (SB) m₀ hp' (unitPt (SB).hG' (bm (x₀ + tA) - tB)) a Φ' =
      blockMarkC (SA) m₀ hp (unitPt (SA).hG' x₀) a Φ :=
  hatOf_rec hN2 hk νS β p₁ δ m₀ (SA).p₁ hp hp' hΦ x₀ hx₀ a

/-- The unit vectors of corresponding marks correspond under the recentring map. -/
theorem obsUnitVec_rec (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {R : ℕ}
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {tA : CTorus d L N₁ m₁ (k + 1)} {tB : CTorus d L N₁' m₁ (k + 1)}
    (SSA : LatSymm (SA).G' (SA).G' (Equiv.addRight tA)) (hUA : UnitBlockPres (Equiv.addRight tA))
    (SSB : LatSymm (SB).G' (SB).G' (Equiv.addRight tB)) (hUB : UnitBlockPres (Equiv.addRight tB))
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₀ + tA))
    (a : Fin N) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) (i : Fin N) :
    obsUnitVec (SB) (unitPt (SB).hG' (bm (x₀ + tA) - tB), a)
        (unitPt (SB).hG' (bm (x + tA) - tB), i) =
      obsUnitVec (SA) (unitPt (SA).hG' x₀, a) (unitPt (SA).hG' x, i) := by
  have e0 := unitPt_recentred (R := R) hn (SA).hG' (SB).hG' SSA hUA SSB hUB hx₀
  have e1 := unitPt_recentred (R := R) hn (SA).hG' (SB).hG' SSA hUA SSB hUB hx
  unfold obsUnitVec
  by_cases h : (unitPt (SA).hG' x, i) = (unitPt (SA).hG' x₀, a)
  · rw [Prod.mk.injEq] at h
    have h2 : unitPt (SB).hG' (bm (x + tA) - tB) = unitPt (SB).hG' (bm (x₀ + tA) - tB) :=
      e1.trans ((congrArg (fun u : (SA).U => (unitAct (SB).G' SSB hUB).symm
        (ιu (unitAct (SA).G' SSA hUA u))) h.1).trans e0.symm)
    rw [h2, h.1, h.2, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    rw [Prod.mk.injEq] at h'
    have h1 : (unitAct (SB).G' SSB hUB).symm (ιu (unitAct (SA).G' SSA hUA (unitPt (SA).hG' x))) =
        (unitAct (SB).G' SSB hUB).symm (ιu (unitAct (SA).G' SSA hUA (unitPt (SA).hG' x₀))) :=
      e1.symm.trans (h'.1.trans e0)
    exact h (Prod.ext (unitPt_eq_of_rec_eq hn hn' (SA).hG' (SB).hG' SSA hUA SSB hUB hx hx₀ h1)
      h'.2)

end RecentreMarks

end Balaban.Polymer.TwoTorusStep
