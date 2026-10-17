/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapStepObsPart
public import Balaban.Polymer.TwoTorusGapObsRecentreCoef
public import Balaban.Polymer.TwoTorusObsActivity

/-!
# The activities of the observable under the recentring map

The label map of two activity systems whose domains correspond under `φ x = bm (x + tA) - tB`, and
the activity hypotheses of `obsCoeffParam_recentred` for `tiltActObs`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric

section TiltRec

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "σAc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tA)
set_option hygiene false in
local notation "σBi" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight tB)⁻¹

/-- **The label map of two label systems whose domains correspond under the recentring map.** -/
theorem labelMap_recentred {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Lb Lb' : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) → ((fun x => bm (x + tA) - tB) '' Y ∈ 𝒴' ↔ Y ∈ 𝒴)) :
    ∃ lm : ∀ l : Lb, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T → Lb',
      (∀ l (_ : blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T),
        ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) ∧
      (∀ l hl, Lab'.ysite (lm l hl) = (fun x => bm (x + tA) - tB) '' Lab.ysite l) ∧
      (∀ l₁ hl₁ l₂ hl₂, lm l₁ hl₁ = lm l₂ hl₂ → l₁ = l₂) ∧
      (∀ l', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite l') ⊆ T.image (fun b => σBi (σc (σAc b))) →
        ∃ l hl, lm l hl = l') := by
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hR : ∀ l, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T →
      ∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) :=
    fun l hl => inBox_rec_of_blocksOf_subset hN tA hT (Lab.isDj l) hl
  have hR' : ∀ l, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T →
      ∀ x ∈ (ys l).1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) :=
    fun l hl => by rw [← hys]; exact hR l hl
  have hm : ∀ l (hl : blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T), (fun x => bm (x + tA) - tB) '' (ys l).1 ∈ 𝒴' :=
    fun l hl => (hmem _ (hR' l hl)).2 (ys l).2
  refine ⟨fun l hl => ys'.symm ⟨(fun x => bm (x + tA) - tB) '' (ys l).1, hm l hl⟩, hR, fun l hl => ?_,
    fun l₁ hl₁ l₂ hl₂ h => ?_, fun l' hl' => ?_⟩
  · rw [hys', Equiv.apply_symm_apply, hys]
  · have h1 : (fun x => bm (x + tA) - tB) '' (ys l₁).1 = (fun x => bm (x + tA) - tB) '' (ys l₂).1 := by
      have := congrArg (fun l' => (ys' l').1) h
      simpa only [Equiv.apply_symm_apply] using this
    exact ys.injective (Subtype.ext (image_recentred_inj hm' tA tB (hR' l₁ hl₁)
      (hR' l₂ hl₂) h1))
  · rw [hys'] at hl'
    have hDj : IsDj m₀ (k + 1) (ys' l').1 := hys' l' ▸ Lab'.isDj l'
    obtain ⟨Y, hYR, hYimg, hYT⟩ := preimage_recentred hN hN' tA tB htA htB hnL hnL' hT hDj hl'
    have hZmem : Y ∈ 𝒴 := (hmem _ hYR).1 (by rw [hYimg]; exact (ys' l').2)
    refine ⟨ys.symm ⟨Y, hZmem⟩, by rw [hys, Equiv.apply_symm_apply]; exact hYT, ?_⟩
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    show (fun x => bm (x + tA) - tB) '' (ys (ys.symm ⟨Y, hZmem⟩)).1 = (ys' l').1
    rw [Equiv.apply_symm_apply]
    exact hYimg


/-- **The activities of the observable under the recentring map**, in the hypotheses of
`obsCoeffParam_recentred`. -/
theorem tiltActObs_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    {Lb Lb' : Type} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴v : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    {𝒴v' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴v}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴v'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) → ((fun x => bm (x + tA) - tB) '' Y ∈ 𝒴v' ↔ Y ∈ 𝒴v))
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N (SA) → ℂ → LabelAct Lab ((SA).blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N (SB) → ℂ → LabelAct Lab' ((SB).blockSplit m₀ hp').Ωb εH' κH' κ0' Kco')
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0' : aEnt d L + 1 ≤ κ0') (hεH : 0 ≤ εH) (hεH' : 0 ≤ εH')
    {Kobs Kobs' : ℝ} (hK : Kco + Kco + K0 d L κ0 + K0 d L κ0 ≤ Kobs)
    (hK' : Kco' + Kco' + K0 d L κ0' + K0 d L κ0' ≤ Kobs')
    (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ)
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hAeq : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) →
      Lab'.ysite l' = (fun x => bm (x + tA) - tB) '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB))) ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' ((θ'.1, 0) : physParam N (SB)) σ).H l' Φ' = (A ((θ.1, 0) : physParam N (SA)) σ).H l Φ)
    (hAeqθ : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      (∀ x ∈ Lab.ysite l, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA)) →
      Lab'.ysite l' = (fun x => bm (x + tA) - tB) '' Lab.ysite l →
      ∀ (Φ : ∀ b, ((SA).blockSplit m₀ hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit m₀ hp').Ωb b),
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
        Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB))) ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
          Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (A' θ' σ).H l' Φ' = (A θ σ).H l Φ) :
    ∃ (P : ObsLb (Lb ⊕ Lb) m₀ 𝒴 → Prop) (P' : ObsLb (Lb' ⊕ Lb') m₀ 𝒴' → Prop)
      (ψ : ∀ l, P l → blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite l) ⊆ T →
        ObsLb (Lb' ⊕ Lb') m₀ 𝒴'),
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l, ¬ P l → ∀ Φ,
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H l Φ = 0) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l', ¬ P' l' → ∀ Φ',
        (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H l' Φ' = 0) ∧
      (∀ l hP hl, P' (ψ l hP hl)) ∧
      (∀ l hP hl, blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab'.sum Lab') hdj').ysite (ψ l hP hl)) =
        (blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite l)).image (fun b => σBi (σc (σAc b)))) ∧
      (∀ l₁ hP₁ hl₁ l₂ hP₂ hl₂, ψ l₁ hP₁ hl₁ = ψ l₂ hP₂ hl₂ → l₁ = l₂) ∧
      (∀ l', P' l' → blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab'.sum Lab') hdj').ysite l') ⊆
        T.image (fun b => σBi (σc (σAc b))) → ∃ l hP hl, ψ l hP hl = l') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l hP hl, ∀ Φ Φ',
        (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA) →
          Φ' ((SB).cellOf m₀ (unitPt (SB).hG' (bm (x + tA) - tB))) ⟨unitPt (SB).hG' (bm (x + tA) - tB), rfl⟩ =
            Φ ((SA).cellOf m₀ (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H (ψ l hP hl) Φ' =
          (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H l Φ) := by
  have ha := cellSide_pos (L := L) m₀ m₁ (k + 1)
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hnc : 2 * R + aK < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hnc' : 2 * R + aK < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨lm, hlmR, hlmy, hlminj, hlmsurj⟩ := labelMap_recentred hN hN' tA tB htA htB hnL hnL' hT Lab Lab' ys ys'
    hys hys' hmem
  have hP0 : ∀ (Y : {Y // Y ∈ 𝒴}), ¬ ∃ w : Lb ⊕ Lb,
      (Sum.inl (Sum.inr Y) : ObsLb (Lb ⊕ Lb) m₀ 𝒴) = Sum.inl (Sum.inl w) := by
    intro Y ⟨w, h⟩
    simp at h
  have hP1 : ∀ (Z : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (m₀ := m₀) (k + 1)}), ¬ ∃ w : Lb ⊕ Lb,
      (Sum.inr Z : ObsLb (Lb ⊕ Lb) m₀ 𝒴) = Sum.inl (Sum.inl w) := by
    intro Z ⟨w, h⟩
    simp at h
  refine ⟨fun l => ∃ w, l = Sum.inl (Sum.inl w), fun l => ∃ w, l = Sum.inl (Sum.inl w),
    fun l => match l with
      | Sum.inl (Sum.inl (Sum.inl a)) => fun _ hl => Sum.inl (Sum.inl (Sum.inl (lm a hl)))
      | Sum.inl (Sum.inl (Sum.inr a)) => fun _ hl => Sum.inl (Sum.inl (Sum.inr (lm a hl)))
      | Sum.inl (Sum.inr Y) => fun hP _ => absurd hP (hP0 Y)
      | Sum.inr Z => fun hP _ => absurd hP (hP1 Z), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ l hl Φ
    rw [tiltActObs_H, physActObs_H_new A hN hκ0 hεH hdj hK _ _ l (fun z hz => hl ⟨z, hz⟩),
      mul_zero]
  · intro s _ l hl Φ
    rw [tiltActObs_H, physActObs_H_new A' hN' hκ0' hεH' hdj' hK' _ _ l (fun z hz => hl ⟨z, hz⟩),
      mul_zero]
  · intro l hP hl
    rcases l with ((a | a) | Y) | Z
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)
  · intro l hP hl
    rcases l with ((a | a) | Y) | Z
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (lm a hl')) =
        (blocksOf m₀ (k + 1) Set.univ (Lab.ysite a)).image (fun b => σBi (σc (σAc b)))
      rw [hlmy a hl']
      exact blocksOf_recentred hN hN' tA tB htA htB hnc hnc' (hlmR a hl')
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (lm a hl')) =
        (blocksOf m₀ (k + 1) Set.univ (Lab.ysite a)).image (fun b => σBi (σc (σAc b)))
      rw [hlmy a hl']
      exact blocksOf_recentred hN hN' tA tB htA htB hnc hnc' (hlmR a hl')
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)
  · intro l₁ hP₁ hl₁ l₂ hP₂ hl₂ h
    rcases l₁ with ((a₁ | a₁) | Y₁) | Z₁
    · rcases l₂ with ((a₂ | a₂) | Y₂) | Z₂
      · have h' : lm a₁ hl₁ = lm a₂ hl₂ := by
          injection h with h; injection h with h; injection h
        rw [hlminj a₁ hl₁ a₂ hl₂ h']
      · injection h with h; injection h with h; injection h
      · exact absurd hP₂ (hP0 Y₂)
      · exact absurd hP₂ (hP1 Z₂)
    · rcases l₂ with ((a₂ | a₂) | Y₂) | Z₂
      · injection h with h; injection h with h; injection h
      · have h' : lm a₁ hl₁ = lm a₂ hl₂ := by
          injection h with h; injection h with h; injection h
        rw [hlminj a₁ hl₁ a₂ hl₂ h']
      · exact absurd hP₂ (hP0 Y₂)
      · exact absurd hP₂ (hP1 Z₂)
    · exact absurd hP₁ (hP0 Y₁)
    · exact absurd hP₁ (hP1 Z₁)
  · intro l' hP' hl'
    obtain ⟨w', rfl⟩ := hP'
    rcases w' with a' | a'
    · obtain ⟨a, ha, rfl⟩ := hlmsurj a' hl'
      exact ⟨Sum.inl (Sum.inl (Sum.inl a)), ⟨_, rfl⟩, ha, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := hlmsurj a' hl'
      exact ⟨Sum.inl (Sum.inl (Sum.inr a)), ⟨_, rfl⟩, ha, rfl⟩
  · intro s hs l hP hl Φ Φ' hΦ
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
    rcases l with ((a | a) | Y) | Z
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl (lm a hl')))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inl,
        physAct_H_inl, hAeq 1 h1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ,
        hAeq (s : ℂ) hs1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ]
    · have hl' : blocksOf m₀ (k + 1) Set.univ (Lab.ysite a) ⊆ T := hl
      show (tiltActObs A' hN' hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr (lm a hl')))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inr,
        physAct_H_inr, hAeqθ (s : ℂ) hs1 a (lm a hl') (hlmR a hl') (hlmy a hl') Φ Φ' hΦ]
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)


end TiltRec

end Balaban.Polymer.TwoTorusStep
