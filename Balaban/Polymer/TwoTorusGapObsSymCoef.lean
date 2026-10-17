/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsSymMarks

/-!
# Translation covariance of the coefficient of the observable (item 24, blocker 7)

`obsCoeffParam_sym`: for a translation `t` by a multiple of the cell side `a_{k+1}`, the coefficient
of the observable with the translated constituents (first-order marks, kernel, remainder marks,
activities) at the translated cubes equals the coefficient with the original constituents.  It is
`obsCoeffParam_transport` for the block measures of one step, the cube map of the translation and
the relation "block variables correspond under `unitAct`" (`integral_blockSplit_sym`); the
correspondences of the constituents are proved in `TwoTorusGapObsSym{,Labels,Marks}`.  What remains
as hypotheses: the correspondence of the domain families (`hmem`), of the terms `Ev` (`hEvT`) and of
the activities (`hA`), as in `obsCoeffParam_twoTorus_of_activities`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited

section Coef

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "σc" => Balaban.Fluctuation.cubeMap (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
  (K := k + 1) (m₀ := m₀) (Equiv.addRight t)

/-- **Translation covariance of the coefficient of the observable.** -/
theorem obsCoeffParam_sym (S : StepSetting d L N₁ m₁ k N ϱ) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (t : CTorus d L N₁ m₁ (k + 1)) (ht : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (t μ).val)
    (SS : LatSymm S.G' S.G' (Equiv.addRight t)) (hU : UnitBlockPres (Equiv.addRight t))
    (hp : 0 < S.p₁)
    {𝒴 𝒴' : Finset (Set (CTorus d L N₁ m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (hmem : ∀ Y, (Equiv.addRight t) '' Y ∈ 𝒴' ↔ Y ∈ 𝒴)
    {Ev Ev' : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (S.U × Fin N → ℂ) → ℂ}
    {cψ : ℝ} (hcψ : 0 < cψ) (hq : S.p₁ / cψ ≤ 1 / 4)
    {A A' : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (θ θ' : physParam N S)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A)
    (hθ' : (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ A')
    (hdEv : ∀ Y ∈ 𝒴, ∀ u ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      ∀ u' ∈ A ×ˢ {ψ : S.U × Fin N → ℂ | ∀ p, ‖ψ p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hEvT : ∀ Y ∈ 𝒴, ∀ (ψh ψh' : S.U × Fin N → ℂ), (∀ q, ‖ψh q‖ ≤ cψ) → (∀ q, ‖ψh' q‖ ≤ cψ) →
      (∀ u i, ψh' (unitAct S.G' SS hU u, i) = ψh (u, i)) →
      Ev' ((Equiv.addRight t) '' Y) ((θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh') =
        Ev Y ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    {Lb₀ Lb₀' : Type} [Fintype Lb₀] [Fintype Lb₀']
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    (bx bx' : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    {εH κH κ0 Kco εH' κH' κ0' Kco' : ℝ}
    (Aact : physParam N S → ℂ → ℂ →
      LabelAct (obsLab Lab₀ hdj) (S.blockSplit m₀ hp).Ωb εH κH κ0 Kco)
    (Aact' : physParam N S → ℂ → ℂ →
      LabelAct (obsLab Lab₀' hdj') (S.blockSplit m₀ hp).Ωb εH' κH' κ0' Kco')
    (P : ObsLb Lb₀ m₀ 𝒴 → Prop) (P' : ObsLb Lb₀' m₀ 𝒴' → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l, ¬ P l → ∀ Φ, (Aact θ (s : ℂ) 1).H l Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l', ¬ P' l' → ∀ Φ',
      (Aact' θ' (s : ℂ) 1).H l' Φ' = 0)
    (ψ : ∀ l, P l → blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite l) ⊆ T →
      ObsLb Lb₀' m₀ 𝒴')
    (hψP : ∀ l hP hl, P' (ψ l hP hl))
    (hψb : ∀ l hP hl, blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite (ψ l hP hl)) =
      (blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite l)).image (σc))
    (hψinj : ∀ l₁ hP₁ hl₁ l₂ hP₂ hl₂, ψ l₁ hP₁ hl₁ = ψ l₂ hP₂ hl₂ → l₁ = l₂)
    (hψsurj : ∀ l', P' l' → blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀' hdj').ysite l') ⊆
      T.image (σc) → ∃ l hP hl, ψ l hP hl = l')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ l hP hl, ∀ Φ Φ',
      (∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩) →
      (Aact' θ' (s : ℂ) 1).H (ψ l hP hl) Φ' = (Aact θ (s : ℂ) 1).H l Φ) :
    obsCoeffParam (S.blockSplit m₀ hp).μ Aact' (fun m => obsY1 m₀ S Lb₀' 𝒴' m)
        (fun m => blockMarkC S m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker 𝒴' (fun Y => hatCoeff (Ev' Y)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec S m)) m₀ T'')
        (obsRemLab 𝒴' (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀' 𝒴' bx'))
        (fun θ => obsGrFam S m₀ hp Ev' 𝒴' A' θ) θ' (T.image (σc)) =
      obsCoeffParam (S.blockSplit m₀ hp).μ Aact (fun m => obsY1 m₀ S Lb₀ 𝒴 m)
        (fun m => blockMarkC S m₀ hp m.1 m.2)
        (fun θ m T'' => obsHker 𝒴 (fun Y => hatCoeff (Ev Y)
          (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (obsUnitVec S m)) m₀ T'')
        (obsRemLab 𝒴 (fun Y => Sum.inl (Sum.inr Y)) (obsY0 m₀ Lb₀ 𝒴 bx))
        (fun θ => obsGrFam S m₀ hp Ev 𝒴 A θ) θ T := by
  classical
  have hσ := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) t ht)
  have hinj := cubeMap_injective_sym hN hσ
  refine obsCoeffParam_transport _ _ Aact Aact' _ _ _ _ _ _ _ _ _ _ θ θ' (σc) T
    (fun a _ b _ h => hinj h)
    (fun Φ Φ' => ∀ u : S.U, Φ' (S.cellOf m₀ (unitAct S.G' SS hU u)) ⟨unitAct S.G' SS hU u, rfl⟩ =
        Φ (S.cellOf m₀ u) ⟨u, rfl⟩)
    (fun Z _ F F' _ hFF => integral_blockSplit_sym S m₀ hp SS hU hFF) P P' hA0 hA0' ψ hψP hψb
    hψinj hψsurj hA
    (fun i => depOn_blockMarkC i.1 i.2 (obsCubeLab_mem m₀ (S.cellOf m₀ i.1)))
    (fun i _ => (unitAct S.G' SS hU i.1, i.2))
    (fun i _ => blocksOf_obsY1_sym S hN t ht SS hU Lab₀ Lab₀' hdj hdj' i) ?_ ?_
    (fun i _ Φ Φ' hΦ => blockMarkC_sym S m₀ hp SS hU hΦ i.1 i.2) ?_
    (fun i => i ≠ none) (fun i => i ≠ none) ?_ ?_
    (fun i u => depOn_obsGrFam_all hN hcψ hq hdj hdEv (obsLab Lab₀ hdj)
      (fun Y => Sum.inl (Sum.inr Y)) _ (fun _ => rfl) θ i u)
    (fun i hQ hi => match i, hQ, hi with
      | some Y, _, _ => some ⟨(Equiv.addRight t) '' Y.1, (hmem Y.1).2 Y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · -- injectivity of the first-order correspondence
    intro i₁ _ i₂ _ h
    rw [Prod.mk.injEq] at h
    exact Prod.ext ((unitAct S.G' SS hU).injective h.1) h.2
  · -- surjectivity
    intro i' hi'
    have hi : blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite
        (obsY1 m₀ S Lb₀ 𝒴 ((unitAct S.G' SS hU).symm i'.1, i'.2))) ⊆ T := by
      have h1 := blocksOf_obsY1_sym S hN t ht SS hU Lab₀ Lab₀' hdj hdj' (𝒴' := 𝒴')
        ((unitAct S.G' SS hU).symm i'.1, i'.2)
      simp only [Equiv.apply_symm_apply] at h1
      rw [h1] at hi'
      intro b hb
      have := hi' (Finset.mem_image_of_mem _ hb)
      obtain ⟨b0, hb0, he⟩ := Finset.mem_image.1 this
      rwa [← hinj he]
    exact ⟨((unitAct S.G' SS hU).symm i'.1, i'.2), hi, by simp⟩
  · -- the kernels
    intro i _ T₁ _
    exact obsHker_sym hN hσ hmem (fun Y hY => hatCoeff_obsUnitVec_sym S SS hU hcψ
      (hEvT Y hY) i) T₁
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
    · exact blocksOf_image_sym hN hσ Y.1
  · intro i₁ hQ₁ hi₁ i₂ hQ₂ hi₂ h
    rcases i₁ with _ | Y₁
    · exact absurd rfl hQ₁
    rcases i₂ with _ | Y₂
    · exact absurd rfl hQ₂
    injection h with h'
    injection h' with h1
    exact congrArg some (Subtype.ext ((Equiv.addRight t).injective.image_injective h1))
  · intro i' hQ' hi'
    rcases i' with _ | Y'
    · exact absurd rfl hQ'
    have h1 : (Equiv.addRight t) '' ((Equiv.addRight t).symm '' Y'.1) = Y'.1 := by
      rw [← Set.image_comp]; simp
    have hY : (Equiv.addRight t).symm '' Y'.1 ∈ 𝒴 := (hmem _).1 (by rw [h1]; exact Y'.2)
    have hb := blocksOf_image_sym hN hσ ((Equiv.addRight t).symm '' Y'.1)
    rw [h1] at hb
    have hi'' : blocksOf m₀ (k + 1) Set.univ Y'.1 ⊆ T.image (σc) := hi'
    refine ⟨some ⟨_, hY⟩, Option.some_ne_none _, ?_, ?_⟩
    · show blocksOf m₀ (k + 1) Set.univ ((Equiv.addRight t).symm '' Y'.1) ⊆ T
      intro b hb0
      have : (σc b) ∈ T.image (σc) := hi'' (by rw [hb]; exact Finset.mem_image_of_mem _ hb0)
      obtain ⟨b1, hb1, he⟩ := Finset.mem_image.1 this
      rwa [← hinj he]
    · exact congrArg some (Subtype.ext h1)
  · intro s _ i hQ hi Φ Φ' hΦ
    rcases i with _ | Y
    · exact absurd rfl hQ
    rw [obsGrFam_of_mem hθ', obsGrFam_of_mem hθ]
    exact obsGrRawC_sym S m₀ SS hU hp Y _ hcψ hq (hEvT Y.1 Y.2) hΦ s

end Coef

end Balaban.Polymer.TwoTorusStep
