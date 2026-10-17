/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsRecentre

/-!
# The labels of the observable under the recentring map

The first-order label of the mark `(u, a)` of the first torus and of the mark `(ι u, a)` of the
second torus, `ι = unitAct_B⁻¹ ∘ ιu ∘ unitAct_A`, correspond along the recentred cube map
`rc = cubeMap σ_B⁻¹ ∘ cubeMap bm ∘ cubeMap σ_A`.  Each statement is the composition of the translation
statement of `TwoTorusGapObsSymLabels` on each torus with the landed two-torus statement.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited Balaban.Inhabited.LevelStep

section RecentreIdx

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

/-- The cube map of the inverse translation undoes the cube map of the translation. -/
theorem cubeMap_cubeMap_inv_sym {m₀ : ℕ} (hN' : L ^ m₀ ∣ N₁') (tB : CTorus d L N₁' m₁ (k + 1))
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (b : CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    Balaban.Fluctuation.cubeMap (Equiv.addRight tB) (Balaban.Fluctuation.cubeMap (Equiv.addRight tB)⁻¹ b) = b := by
  have hσ := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have := cubeMap_inv hN' (inv_mem hσ) b
  rwa [inv_inv] at this

/-- The first-order label correspondence under the recentring map. -/
theorem blocksOf_obsY1_rec (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (SSA : LatSymm (SA).G' (SA).G' (Equiv.addRight tA)) (hUA : UnitBlockPres (Equiv.addRight tA))
    (SSB : LatSymm (SB).G' (SB).G' (Equiv.addRight tB)) (hUB : UnitBlockPres (Equiv.addRight tB))
    (hn2 : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Lb₀ Lb₀' : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (i : ObsMarkIdx (SA)) (w : (SB).U)
    (hw : ((unitAct (SB).G' SSB hUB w : (SB).U) : UnitTorus d L N₁' m₁ k) =
      bU ((unitAct (SA).G' SSA hUA i.1 : (SA).U) : UnitTorus d L N₁ m₁ k))
    (hi : ∀ x ∈ box ((SA).cellOf m₀ i.1).1 (L * aK),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) :
    blocksOf m₀ (k + 1) Set.univ
        ((obsLab Lab₀' hdj').ysite (obsY1 m₀ (SB) Lb₀' 𝒴' (w, i.2))) =
      (blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i))).image
        (fun b => σBi (σc (σAc b))) := by
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hinjB := cubeMap_injective_sym hN' hσB
  -- the label box of the translated mark lies in the box
  have hi1 : ∀ x ∈ box ((SA).cellOf m₀ (unitAct (SA).G' SSA hUA i.1)).1 (L * aK),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    rw [cellOf_unitAct (SA) SSA hUA hN hσA, cubeMap_translate_val hN tA htA] at hx
    have hx' : x - tA ∈ box ((SA).cellOf m₀ i.1).1 (L * aK) :=
      (Balaban.Localization.DecEquiv.mem_box_add_iff _ tA (x - tA) _).1 (by simpa using hx)
    simpa using hi (x - tA) hx'
  have e1 := blocksOf_obsY1_sym (SA) hN tA htA SSA hUA Lab₀ Lab₀ hdj hdj (𝒴' := 𝒴) i
  have e2 := blocksOf_obsY1_unitImage hN2 hk νS β p₁ δ hN hN' hn2 hnL hnL' Lab₀ Lab₀' hdj hdj'
    ((unitAct (SA).G' SSA hUA i.1, i.2) : ObsMarkIdx (SA)) hi1
  have e3 := blocksOf_obsY1_sym (SB) hN' tB htB SSB hUB Lab₀' Lab₀' hdj' hdj' (𝒴' := 𝒴')
    ((w, i.2) : ObsMarkIdx (SB))
  have heq : unitAct (SB).G' SSB hUB w = ιu (unitAct (SA).G' SSA hUA i.1) := Subtype.ext hw
  have e4 : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite
      (obsY1 m₀ (SB) Lb₀' 𝒴' (unitAct (SB).G' SSB hUB w, i.2))) =
      ((blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i))).image
        σAc).image σc :=
    (congrArg (fun m : (SB).U => blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite
      (obsY1 m₀ (SB) Lb₀' 𝒴' (m, i.2)))) heq).trans (e2.trans (congrArg (Finset.image σc) e1))
  have hX : ∀ X : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀
      (k + 1) Set.univ), X = (X.image σBc).image σBi := fun X => by
    ext b
    simp only [Finset.mem_image]
    constructor
    · intro h
      exact ⟨σBc b, ⟨b, h, rfl⟩, cubeMap_inv hN' hσB b⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      rwa [cubeMap_inv hN' hσB c]
  refine (hX _).trans ?_
  have e5 := e3.symm.trans e4
  rw [e5, Finset.image_image, Finset.image_image]
  rfl

end RecentreIdx

end Balaban.Polymer.TwoTorusStep
