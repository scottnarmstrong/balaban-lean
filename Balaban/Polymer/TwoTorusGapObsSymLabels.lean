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

/-- The cube map of a paving symmetry is injective. -/
theorem cubeMap_injective_sym (hN : L ^ m₀ ∣ N₁) {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K) :
    Function.Injective (Balaban.Fluctuation.cubeMap (m₀ := m₀) σ) := fun a b h => by
  rw [← cubeMap_inv hN hσ a, h, cubeMap_inv hN hσ b]

/-- **The kernel under a paving symmetry.**  Let the domain families `𝒴`, `𝒴'` correspond under
`Y ↦ σ '' Y` and let the coefficients agree on corresponding domains.  Then the kernels at the image
of a set of cubes and at the set agree. -/
theorem obsHker_sym (hN : L ^ m₀ ∣ N₁) {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (hσ : σ ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := K) (d := d) L m₀ K)
    {𝒴 𝒴' : Finset (Set (CTorus d L N₁ m₁ K))}
    (hmem : ∀ Y, σ '' Y ∈ 𝒴' ↔ Y ∈ 𝒴)
    {c c' : Set (CTorus d L N₁ m₁ K) → ℂ} (hc : ∀ Y ∈ 𝒴, c' (σ '' Y) = c Y)
    (T₁ : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ)) :
    obsHker 𝒴' c' m₀ (T₁.image (Balaban.Fluctuation.cubeMap σ)) = obsHker 𝒴 c m₀ T₁ := by
  classical
  have hinj := cubeMap_injective_sym hN hσ
  have hiff : ∀ Y, obsRowLabel m₀ K (σ '' Y) = T₁.image (Balaban.Fluctuation.cubeMap σ) ↔
      obsRowLabel m₀ K Y = T₁ := fun Y => by
    rw [obsRowLabel_def, obsRowLabel_def, blocksOf_image_sym hN hσ]
    exact (Finset.image_injective hinj).eq_iff
  refine obsHker_congr_bij (fun Y => σ '' Y) (fun Y' => σ.symm '' Y') c c' T₁
    (T₁.image (Balaban.Fluctuation.cubeMap σ)) (fun Y hY hl => ⟨(hmem Y).2 hY, (hiff Y).2 hl⟩)
    (fun Y' hY' hl => ?_) (fun Y hY hl => Equiv.symm_image_image _ _)
    (fun Y' hY' hl => Equiv.image_symm_image _ _) (fun Y hY hl => hc Y hY)
  have h1 : σ '' (σ.symm '' Y') = Y' := Equiv.image_symm_image _ _
  exact ⟨(hmem _).1 (by rw [h1]; exact hY'), (hiff _).1 (by rw [h1]; exact hl)⟩

end Labels

section StepLabels

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ}

/-- **The first-order labels of the marks `(u, a)` and `(unitAct u, a)` correspond**: the blocks of the
second are the translates of the blocks of the first. -/
theorem blocksOf_obsY1_sym (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (SS : LatSymm S.G' S.G' (Equiv.addRight t)) (hU : UnitBlockPres (Equiv.addRight t))
    {Lb₀ Lb₀' : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    {𝒴 𝒴' : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (i : ObsMarkIdx S) :
    blocksOf m₀ (k + 1) Set.univ
        ((obsLab Lab₀' hdj').ysite (obsY1 m₀ S Lb₀' 𝒴' (unitAct S.G' SS hU i.1, i.2))) =
      (blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ S Lb₀ 𝒴 i))).image
        (Balaban.Fluctuation.cubeMap (Equiv.addRight t)) := by
  have hσ := genSymm_mem_pavingSymGroup (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) t ht)
  show blocksOf m₀ (k + 1) Set.univ (obsCubeLab m₀ (S.cellOf m₀ (unitAct S.G' SS hU i.1))).1 =
    (blocksOf m₀ (k + 1) Set.univ (obsCubeLab m₀ (S.cellOf m₀ i.1)).1).image _
  rw [cellOf_unitAct S SS hU hN hσ]
  show blocksOf m₀ (k + 1) Set.univ
      (box (Balaban.Fluctuation.cubeMap (Equiv.addRight t) (S.cellOf m₀ i.1)).1
        (L * cellSide L m₀ m₁ (k + 1))) = _
  rw [obsCubeLab_translate hN t ht, blocksOf_image_sym hN hσ]
  rfl

end StepLabels

end Balaban.Polymer.TwoTorusStep
