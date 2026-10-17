/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsRecentreDom

/-!
# The coefficient of the observable under the recentring map (item 24, blocker 7)

`obsCoeffParam_recentred`: the coefficient of the observable of the second step at the recentred
cubes equals that of the first step, `φ x = bm (x + tA) - tB`: `obsCoeffParam_transport` for the block
measures of the two steps, the recentred cube map and the relation "block variables agree at the
corresponding unit points of the sites whose translate lies in the box".  The correspondences of the
first-order labels, marks, kernel and remainder marks are proved in
`TwoTorusGapObsRecentre{Idx,Marks,Dom}`; as in `obsCoeffParam_twoTorus_of_activities`, the correspondence
of the domain families (`hmem`), of the terms `Ev` (`hEvT`) and of the activities (`hA`) are hypotheses.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited Balaban.Inhabited.LevelStep

section RecCoef

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
set_option hygiene false in
local notation "φr" => fun x => bm (x + tA) - tB

/-- **The coefficient of the observable under the recentring map.** -/
theorem obsCoeffParam_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
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
    (hnF : 2 * R + 5 * (L * aK) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * aK) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) →
      ((fun x => bm (x + tA) - tB) '' Y ∈ 𝒴' ↔ Y ∈ 𝒴))
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × ((SA).U × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × ((SB).U × Fin N → ℂ) → ℂ}
    {cψ : ℝ} (hcψ : 0 < cψ) (hq : (SA).p₁ / cψ ≤ 1 / 4)
    {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    {A' : Set (RawData d L (N₁' * L ^ m₁) (k + 1) N)}
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈ A')
    (hdEv : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : (SA).U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : (SA).U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      AgHatDir (SA).hG' Y u u' → Ev Y u = Ev Y u')
    (hEvT : ∀ Y ∈ 𝒴, (∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA)) →
      ∀ (ψh : (SA).U × Fin N → ℂ) (ψh' : (SB).U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) →
      (∀ q, ‖ψh' q‖ ≤ cψ) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        ∀ i, ψh' (unitPt (SB).hG' (bm (x + tA) - tB), i) = ψh (unitPt (SA).hG' x, i)) →
      Ev' ((fun x => bm (x + tA) - tB) '' Y)
          ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), ψh') =
        Ev Y ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Lb₀ Lb₀' : Type} [Fintype Lb₀] [Fintype Lb₀']
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    (bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    (bx' : CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (Aact : physParam N (SA) → ℂ → ℂ →
      LabelAct (obsLab Lab₀ hdj) ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (Aact' : physParam N (SB) → ℂ → ℂ →
      LabelAct (obsLab Lab₀' hdj') ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    (P : ObsLb Lb₀ m₀ 𝒴 → Prop) (P' : ObsLb Lb₀' m₀ 𝒴' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l, ¬ P l → ∀ Φ, (Aact θ (s : ℂ) 1).H l Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l', ¬ P' l' → ∀ Φ',
      (Aact' θ' (s : ℂ) 1).H l' Φ' = 0)
    (ψ : ∀ l, P l → blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite l) ⊆ T →
      ObsLb Lb₀' m₀ 𝒴')
    (hψP : ∀ l hP hl, P' (ψ l hP hl))
    (hψb : ∀ l hP hl, blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite (ψ l hP hl)) =
      (blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite l)).image
        (fun b => σBi (σc (σAc b))))
    (hψinj : ∀ l₁ hP₁ hl₁ l₂ hP₂ hl₂, ψ l₁ hP₁ hl₁ = ψ l₂ hP₂ hl₂ → l₁ = l₂)
    (hψsurj : ∀ l', P' l' → blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite l') ⊆
      T.image (fun b => σBi (σc (σAc b))) → ∃ l hP hl, ψ l hP hl = l')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l hP hl, ∀ Φ Φ',
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
          ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (Aact' θ' (s : ℂ) 1).H (ψ l hP hl) Φ' = (Aact θ (s : ℂ) 1).H l Φ) :
    obsCoeffParam ((SB).blockSplit m₀ hp').μ Aact' (fun m => obsY1 m₀ (SB) Lb₀' 𝒴' m)
        (fun m => blockMarkC (SB) m₀ hp' m.1 m.2)
        (fun θ m T'' => obsHker 𝒴' (fun Y => hatCoeff (Ev' Y)
          (θ.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) (obsUnitVec (SB) m)) m₀ T'')
        (obsRemLab 𝒴' (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀' 𝒴' bx'))
        (fun θ => obsGrFam (SB) m₀ hp' Ev' 𝒴' A' θ) θ' (T.image (fun b => σBi (σc (σAc b)))) =
      obsCoeffParam ((SA).blockSplit m₀ hp).μ Aact (fun m => obsY1 m₀ (SA) Lb₀ 𝒴 m)
        (fun m => blockMarkC (SA) m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker 𝒴 (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec (SA) m)) m₀ T'')
        (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx))
        (fun θ => obsGrFam (SA) m₀ hp Ev 𝒴 A θ) θ T := by
  classical
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hσB := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hinjA := cubeMap_injective_sym hN hσA
  have hinjBi := cubeMap_injective_sym hN' (inv_mem hσB)
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hnc : 2 * R + aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnc' : 2 * R + aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hT1 : ∀ b ∈ T.image σAc, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro b hb x hx
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    rw [cubeMap_translate_val hN tA htA] at hx
    have hx' : x - tA ∈ box b0.1 aK :=
      (Balaban.Localization.DecEquiv.mem_box_add_iff _ tA (x - tA) _).1 (by simpa using hx)
    simpa using hT b0 hb0 (x - tA) hx'
  have hσT : Set.InjOn (fun b => σBi (σc (σAc b))) (T : Set _) := by
    intro b₁ hb₁ b₂ hb₂ h
    have h1 := hinjBi h
    have hS : ∀ b ∈ T.image σAc, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) b.1 :=
      fun b hb => hT1 b hb b.1 (mem_box_self _ ha)
    exact hinjA (cubeMap_injOn_box hN hN' hm' hS
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb₁)))
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb₂))) h1)
  obtain ⟨hκ1b, hκ1inj, hκ1surj⟩ := obsMarkLabels_rec hN2 hk νS β p₁ δ hN hN' tA tB htA htB SSA
    hUA SSB hUB hn2 hn2' hnL hnL' hT Lab₀ Lab₀' hdj hdj'
  have hmark : ∀ (i : ObsMarkIdx (SA))
      (_ : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i)) ⊆ T),
      ∃ x₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₀ + tA) ∧ unitPt (SA).hG' x₀ = i.1 :=
    fun i hi => (obsY1_label_rec_inBox hN2 hk νS β p₁ δ hN tA hT Lab₀ hdj i hi).2
  have hboxY : ∀ Y : {Y // Y ∈ 𝒴},
      blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite
        (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx) (some Y))) ⊆ T →
      ∀ y ∈ Y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (y + tA) :=
    fun Y hi => inBox_rec_of_blocksOf_subset hN tA hT (hdj Y.1 Y.2) hi
  refine obsCoeffParam_transport _ _ Aact Aact' _ _ _ _ _ _ _ _ _ _ θ θ'
    (fun b => σBi (σc (σAc b))) T hσT
    (fun Φ Φ' => ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
      Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB)))
        ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
        Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩)
    (fun Z hZ F F' hF hFF => integral_blockSplit_recentred hN2 hk νS β p₁ δ hn2 hn2' (SA).hG'
      (SB).hG' hp hp' SSA hUA SSB hUB Z (fun b hb => hT b (hZ hb)) hF hFF)
    P P' hA0 hA0' ψ hψP hψb hψinj hψsurj hA
    (fun i => depOn_blockMarkC i.1 i.2 (obsCubeLab_mem m₀ ((SA).cellOf m₀ i.1)))
    (fun i _ => ((ιr i.1, i.2) : ObsMarkIdx (SB))) hκ1b hκ1inj hκ1surj ?_ ?_
    (fun i => i ≠ none) (fun i => i ≠ none) ?_ ?_
    (fun i u => depOn_obsGrFam_all hN hcψ hq hdj hdEv (obsLab Lab₀ hdj)
      (fun Y => Sum.inl (Sum.inr Y)) _ (fun _ => rfl) θ i u)
    (fun i hQ hi => match i, hQ, hi with
      | some Y, _, hi => some ⟨(fun x => bm (x + tA) - tB) '' Y.1, (hmem Y.1 (hboxY Y hi)).2 Y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- the first-order marks
    intro i hi Φ Φ' hΦ
    obtain ⟨x₀, hx₀, hu⟩ := hmark i hi
    obtain ⟨u, a⟩ := i
    simp only at hu
    subst hu
    exact (congrArg (fun w : (SB).U => blockMarkC (SB) m₀ hp' w a Φ')
      (unitPt_recentred hn2 (SA).hG' (SB).hG' SSA hUA SSB hUB hx₀).symm).trans
      (blockMarkC_rec hN2 hk νS β p₁ δ hp hp' hΦ hx₀ a)
  · -- the kernels
    intro i hi T₁ hT₁
    obtain ⟨x₀, hx₀, hu⟩ := hmark i hi
    obtain ⟨u, a⟩ := i
    simp only at hu
    subst hu
    have hfun : (fun Y => hatCoeff (Ev' Y) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
          (obsUnitVec (SB) (ιr (unitPt (SA).hG' x₀), a))) =
        fun Y => hatCoeff (Ev' Y) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N)
          (obsUnitVec (SB) (unitPt (SB).hG' (bm (x₀ + tA) - tB), a)) :=
      funext fun Y => congrArg (fun w : (SB).U => hatCoeff (Ev' Y)
        (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) (obsUnitVec (SB) (w, a)))
        (unitPt_recentred hn2 (SA).hG' (SB).hG' SSA hUA SSB hUB hx₀).symm
    exact (congrArg (fun f => obsHker 𝒴' f m₀ (T₁.image (fun b => σBi (σc (σAc b))))) hfun).trans
      (obsHker_rec hN hN' tA tB htA htB hnF hnF' hdj hdj' hmem _ _
        (fun Y hY hbx => hatCoeff_obsUnitVec_rec hN2 hk νS β p₁ δ hn2 hn2' SSA hUA SSB hUB hcψ
          (fun ψh ψh' h1 h2 h3 => hEvT Y hY hbx ψh ψh' h1 h2 h3) hx₀ a) T₁
        (fun b hb => hT b (hT₁ hb)))
  · intro i hi s _
    have hi' : i = none := not_not.1 hi
    subst hi'
    funext Φ
    rw [obsGrFam_of_mem hθ]
    rfl
  · intro i hi s _
    have hi' : i = none := not_not.1 hi
    subst hi'
    funext Φ
    rw [obsGrFam_of_mem hθ']
    rfl
  · intro i hQ hi
    rcases i with _ | Y
    · exact absurd rfl hQ
    · exact Option.some_ne_none _
  · intro i hQ hi
    rcases i with _ | Y
    · exact absurd rfl hQ
    · exact blocksOf_recentred hN hN' tA tB htA htB hnc hnc' (hboxY Y hi)
  · intro i₁ hQ₁ hi₁ i₂ hQ₂ hi₂ h
    rcases i₁ with _ | Y₁
    · exact absurd rfl hQ₁
    rcases i₂ with _ | Y₂
    · exact absurd rfl hQ₂
    injection h with h'
    injection h' with h1
    exact congrArg some (Subtype.ext (image_recentred_inj hm' tA tB (hboxY Y₁ hi₁) (hboxY Y₂ hi₂) h1))
  · intro i' hQ' hi'
    rcases i' with _ | Y'
    · exact absurd rfl hQ'
    obtain ⟨Y, hYR, hYimg, hYT⟩ := preimage_recentred hN hN' tA tB htA htB hnL hnL' hT
      (hdj' Y'.1 Y'.2) hi'
    have hY : Y ∈ 𝒴 := (hmem Y hYR).1 (by rw [hYimg]; exact Y'.2)
    exact ⟨some ⟨Y, hY⟩, Option.some_ne_none _, hYT, congrArg some (Subtype.ext hYimg)⟩
  · intro s _ i hQ hi Φ Φ' hΦ
    rcases i with _ | Y
    · exact absurd rfl hQ
    rw [obsGrFam_of_mem hθ', obsGrFam_of_mem hθ]
    exact obsGrRawC_rec hN2 hk νS β p₁ δ hp hp' Y _ hcψ hq
      (fun ψh ψh' h1 h2 h3 => hEvT Y.1 Y.2 (hboxY Y hi) ψh ψh' h1 h2 h3) hΦ s

end RecCoef

end Balaban.Polymer.TwoTorusStep
