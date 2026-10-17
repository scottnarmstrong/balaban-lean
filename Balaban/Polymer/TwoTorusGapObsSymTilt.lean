/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsSymCoef
public import Balaban.Polymer.TwoTorusObsActivity

/-!
# Translation covariance of the activities of the observable

The label map of two activity systems whose domain families correspond under the translation, and the
activity hypotheses of `obsCoeffParam_sym` for `tiltActObs` from the correspondence of the
activities of the labels of `Lab` (the potential and the source parts).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited

section Tilt

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "σc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight t)

/-- **The label map of two label systems whose domains correspond under a translation.** -/
theorem labelMap_sym {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (t : CTorus d L N₁ m₁ (k + 1))
    (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) {Lb Lb' : Type*}
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴 𝒴' : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmem : ∀ Y, (Equiv.addRight t) '' Y ∈ 𝒴' ↔ Y ∈ 𝒴) :
    ∃ lm : Lb → Lb',
      (∀ l, Lab'.ysite (lm l) = (Equiv.addRight t) '' Lab.ysite l) ∧
      Function.Injective lm ∧
      (∀ l', blocksOf m₀ (k + 1) Set.univ (Lab'.ysite l') ⊆ T.image (σc) →
        ∃ l, blocksOf m₀ (k + 1) Set.univ (Lab.ysite l) ⊆ T ∧ lm l = l') := by
  have hσ := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) t ht)
  have hinj := cubeMap_injective_sym hN hσ
  refine ⟨fun l => ys'.symm ⟨(Equiv.addRight t) '' (ys l).1, (hmem _).2 (ys l).2⟩,
    fun l => ?_, fun l₁ l₂ h => ?_, fun l' hl' => ?_⟩
  · rw [hys', Equiv.apply_symm_apply, hys]
  · have h1 := congrArg (fun l' => (ys' l').1) h
    simp only [Equiv.apply_symm_apply] at h1
    exact ys.injective (Subtype.ext ((Equiv.addRight t).injective.image_injective h1))
  · rw [hys'] at hl'
    have h1 : (Equiv.addRight t) '' ((Equiv.addRight t).symm '' (ys' l').1) = (ys' l').1 := by
      rw [← Set.image_comp]; simp
    have hY : (Equiv.addRight t).symm '' (ys' l').1 ∈ 𝒴 := (hmem _).1 (by
      rw [h1]; exact (ys' l').2)
    refine ⟨ys.symm ⟨_, hY⟩, ?_, ?_⟩
    · rw [hys, Equiv.apply_symm_apply]
      show blocksOf m₀ (k + 1) Set.univ ((Equiv.addRight t).symm '' (ys' l').1) ⊆ T
      have hb := blocksOf_image_sym hN hσ ((Equiv.addRight t).symm '' (ys' l').1)
      rw [h1] at hb
      intro b hb0
      have : σc b ∈ T.image (σc) := hl' (by rw [hb]; exact Finset.mem_image_of_mem _ hb0)
      obtain ⟨b1, hb1, he⟩ := Finset.mem_image.1 this
      rwa [← hinj he]
    · apply ys'.injective
      apply Subtype.ext
      simp only [Equiv.apply_symm_apply]
      exact h1

/-- **The activities of the observable under a translation.**  Let the label systems `Lab`, `Lab'`
of the activity families `A`, `A'` correspond (`ys`, `ys'`) to domain families that correspond under
the translation, and let the activities of corresponding labels agree at the zero-source parameters
`(θ.1, 0)`, `(θ'.1, 0)` (`hAeq`) and at `θ`, `θ'` (`hAeqθ`), for block variables corresponding under
`unitAct`.  Then `tiltActObs A …` and `tiltActObs A' …` satisfy the activity hypotheses of
`obsCoeffParam_sym`: the active labels are those of `Lab.sum Lab`, and `ψ` carries the label `(a)`
of `Lab` to the label of `lm a`. -/
theorem tiltActObs_sym (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (SS : LatSymm S.G' S.G' (Equiv.addRight t)) (hU : UnitBlockPres (Equiv.addRight t))
    (hp : 0 < S.p₁)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    {Lb Lb' : Type} [Fintype Lb] [Fintype Lb']
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb)
    (Lab' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb')
    {𝒴v 𝒴v' : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (ys : Lb ≃ {Y // Y ∈ 𝒴v}) (ys' : Lb' ≃ {Y // Y ∈ 𝒴v'})
    (hys : ∀ l, Lab.ysite l = (ys l).1) (hys' : ∀ l', Lab'.ysite l' = (ys' l').1)
    (hmem : ∀ Y, (Equiv.addRight t) '' Y ∈ 𝒴v' ↔ Y ∈ 𝒴v)
    {𝒴 𝒴' : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (A' : physParam N S → ℂ → LabelAct Lab' (S.blockSplit m₀ hp).Ωb εH' κH' κ0' Kco')
    (hκ0 : aEnt d L + 1 ≤ κ0) (hκ0' : aEnt d L + 1 ≤ κ0') (hεH : 0 ≤ εH) (hεH' : 0 ≤ εH')
    {Kobs Kobs' : ℝ} (hK : Kco + Kco + K0 d L κ0 + K0 d L κ0 ≤ Kobs)
    (hK' : Kco' + Kco' + K0 d L κ0' + K0 d L κ0' ≤ Kobs')
    (Rg : ℝ) (hR : 0 ≤ Rg) (𝒰 : Set ℂ) (θ θ' : physParam N S)
    (hAeq : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      Lab'.ysite l' = (Equiv.addRight t) '' Lab.ysite l →
      ∀ (Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b),
      (∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) →
      (A' ((θ'.1, 0) : physParam N S) σ).H l' Φ' = (A ((θ.1, 0) : physParam N S) σ).H l Φ)
    (hAeqθ : ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ (l : Lb) (l' : Lb'),
      Lab'.ysite l' = (Equiv.addRight t) '' Lab.ysite l →
      ∀ (Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b),
      (∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) →
      (A' θ' σ).H l' Φ' = (A θ σ).H l Φ) :
    ∃ (P : ObsLb (Lb ⊕ Lb) m₀ 𝒴 → Prop) (P' : ObsLb (Lb' ⊕ Lb') m₀ 𝒴' → Prop)
      (ψ : ∀ l, P l → blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite l) ⊆ T →
        ObsLb (Lb' ⊕ Lb') m₀ 𝒴'),
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l, ¬ P l → ∀ Φ,
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H l Φ = 0) ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l', ¬ P' l' → ∀ Φ',
        (tiltActObs A' hN hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H l' Φ' = 0) ∧
      (∀ l hP hl, P' (ψ l hP hl)) ∧
      (∀ l hP hl, blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab'.sum Lab') hdj').ysite (ψ l hP hl)) =
        (blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite l)).image (σc)) ∧
      (∀ l₁ hP₁ hl₁ l₂ hP₂ hl₂, ψ l₁ hP₁ hl₁ = ψ l₂ hP₂ hl₂ → l₁ = l₂) ∧
      (∀ l', P' l' → blocksOf m₀ (k + 1) Set.univ ((obsLab (Lab'.sum Lab') hdj').ysite l') ⊆
        T.image (σc) → ∃ l hP hl, ψ l hP hl = l') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l hP hl, ∀ Φ Φ',
        (∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
          Φ (S.cellOf m₀ u) ⟨u, rfl⟩) →
        (tiltActObs A' hN hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H (ψ l hP hl) Φ' =
          (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H l Φ) := by
  have hσ := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) t ht)
  have hinj := cubeMap_injective_sym hN hσ
  obtain ⟨lm, hlmy, hlminj, hlmsurj⟩ := labelMap_sym hN t ht T Lab Lab' ys ys' hys hys' hmem
  have hP0 : ∀ (Y : {Y // Y ∈ 𝒴}), ¬ ∃ w : Lb ⊕ Lb,
      (Sum.inl (Sum.inr Y) : ObsLb (Lb ⊕ Lb) m₀ 𝒴) = Sum.inl (Sum.inl w) := by
    intro Y ⟨w, h⟩
    simp at h
  have hP1 : ∀ (Z : {Z // Z ∈ cubeFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      (m₀ := m₀) (k + 1)}), ¬ ∃ w : Lb ⊕ Lb,
      (Sum.inr Z : ObsLb (Lb ⊕ Lb) m₀ 𝒴) = Sum.inl (Sum.inl w) := by
    intro Z ⟨w, h⟩
    simp at h
  have hbl : ∀ a : Lb, blocksOf m₀ (k + 1) Set.univ (Lab'.ysite (lm a)) =
      (blocksOf m₀ (k + 1) Set.univ (Lab.ysite a)).image (σc) := fun a => by
    rw [hlmy a]; exact blocksOf_image_sym hN hσ _
  have hs1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖(s : ℂ)‖ ≤ 1 := fun s hs => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  refine ⟨fun l => ∃ w, l = Sum.inl (Sum.inl w), fun l => ∃ w, l = Sum.inl (Sum.inl w),
    fun l => match l with
      | Sum.inl (Sum.inl (Sum.inl a)) => fun _ _ => Sum.inl (Sum.inl (Sum.inl (lm a)))
      | Sum.inl (Sum.inl (Sum.inr a)) => fun _ _ => Sum.inl (Sum.inl (Sum.inr (lm a)))
      | Sum.inl (Sum.inr Y) => fun hP _ => absurd hP (hP0 Y)
      | Sum.inr Z => fun hP _ => absurd hP (hP1 Z), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _ l hl Φ
    rw [tiltActObs_H, physActObs_H_new A hN hκ0 hεH hdj hK _ _ l (fun z hz => hl ⟨z, hz⟩),
      mul_zero]
  · intro s _ l hl Φ
    rw [tiltActObs_H, physActObs_H_new A' hN hκ0' hεH' hdj' hK' _ _ l (fun z hz => hl ⟨z, hz⟩),
      mul_zero]
  · intro l hP hl
    rcases l with ((a | a) | Y) | Z
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)
  · intro l hP hl
    rcases l with ((a | a) | Y) | Z
    · exact hbl a
    · exact hbl a
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)
  · intro l₁ hP₁ hl₁ l₂ hP₂ hl₂ h
    rcases l₁ with ((a₁ | a₁) | Y₁) | Z₁
    · rcases l₂ with ((a₂ | a₂) | Y₂) | Z₂
      · have h' : lm a₁ = lm a₂ := by
          injection h with h; injection h with h; injection h
        rw [hlminj h']
      · injection h with h; injection h with h; injection h
      · exact absurd hP₂ (hP0 Y₂)
      · exact absurd hP₂ (hP1 Z₂)
    · rcases l₂ with ((a₂ | a₂) | Y₂) | Z₂
      · injection h with h; injection h with h; injection h
      · have h' : lm a₁ = lm a₂ := by
          injection h with h; injection h with h; injection h
        rw [hlminj h']
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
    have h1 : ‖(1 : ℂ)‖ ≤ 1 := by simp
    rcases l with ((a | a) | Y) | Z
    · show (tiltActObs A' hN hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl (lm a)))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inl a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inl,
        physAct_H_inl, hAeq 1 h1 a (lm a) (hlmy a) Φ Φ' hΦ,
        hAeq (s : ℂ) (hs1 s hs) a (lm a) (hlmy a) Φ Φ' hΦ]
    · show (tiltActObs A' hN hκ0' hεH' hdj' hK' Rg hR 𝒰 θ' (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr (lm a)))) Φ' =
        (tiltActObs A hN hκ0 hεH hdj hK Rg hR 𝒰 θ (s : ℂ) 1).H
          (Sum.inl (Sum.inl (Sum.inr a))) Φ
      rw [tiltActObs_H, tiltActObs_H, physActObs_H_inl, physActObs_H_inl, physAct_H_inr,
        physAct_H_inr, hAeqθ (s : ℂ) (hs1 s hs) a (lm a) (hlmy a) Φ Φ' hΦ]
    · exact absurd hP (hP0 Y)
    · exact absurd hP (hP1 Z)

end Tilt

end Balaban.Polymer.TwoTorusStep
