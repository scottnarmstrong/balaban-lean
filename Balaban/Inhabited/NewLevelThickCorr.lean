/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelClassPair
public import Balaban.Inhabited.NewLevelHPairs
public import Balaban.Polymer.TwoTorusLabelBox

/-!
# The thick labels of two systems of the new level on two tori

* `NewLevelSystem.mem_𝒴C_iff`: a domain is a thick label iff it lies in the domain of an old term;
* `thick_act_agree`: the thick activities `AC` of two systems agree at a label of the box and its
  image under `boxMap`, from the partial index bijection of the old terms (`hE`) and the premises of
  the comparison of corresponding old terms (`hprem`);
* `thick_labelCorr`: the thick labels with blocks in a set `T` of the box correspond injectively
  and onto those with blocks in `cubeMap '' T`, with agreeing activities.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

section Coeff


variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))

theorem NewLevelSystem.mem_𝒴C_iff {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    Y ∈ NS.𝒴C ↔ ∃ τ, NS.Dom Y τ := by
  rw [NS.h𝒴]
  simp [NewLevelSystem.Dom]

attribute [local irreducible] NewLevelSystem.Dom

theorem thick_act_agree
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : (SA).JointRep t pp}
    {C' : StepClass d L N₁' m₁ k N ϱ} {z' : RootIdx d L N₁' m₁ (k + 1)} {pp' : ℝ}
    {Jr' : (SB).JointRep t pp'}
    (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' z' Jr')
    {R : ℕ}
    (hm₀ : NS'.O.m₀ = NS.O.m₀)
    (hE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ,
        NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm)
    (hprem : ∀ (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N (SA)) (θ' : physParam N (SB))
      (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (Φ : ∀ b, ((SA).blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 NS'.hp).Ωb b)
      (u t₀ : ℂ), NS.Dom Y τ → NS'.O.jL τ' = NS.O.jL τ →
      NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm → (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (‖u‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
        (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (y : {Y // Y ∈ NS.𝒴C}) (hyR : ∀ x ∈ y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hy' : bm '' y.1 ∈ NS'.𝒴C)
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        (NS'.AC θ' (s : ℂ)).H ⟨bm '' y.1, hy'⟩ Φ' = (NS.AC θ (s : ℂ)).H y Φ := by
  intro s hs Φ Φ' hΦ
  have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hu : ‖(s : ℂ)‖ < corrU := by
    have : (corrU : ℝ) = 17 / 16 := rfl
    rw [this]; linarith
  obtain ⟨e, he⟩ := hE y.1 hyR
  obtain ⟨hXs, hjs⟩ : (∀ (τ : NS.O.ι) (hτ : NS.Dom y.1 τ),
      NS'.O.X₁f (e ⟨τ, hτ⟩).1 = (NS.O.X₁f τ).image bm) ∧
      (∀ (τ : NS.O.ι) (hτ : NS.Dom y.1 τ), NS'.O.jL (e ⟨τ, hτ⟩).1 = NS.O.jL τ) :=
    ⟨fun τ hτ => (he ⟨τ, hτ⟩).2, fun τ hτ => (he ⟨τ, hτ⟩).1⟩
  have key := NS.H_twoTorus_partial_of_pairs NS' θ θ' y ⟨bm '' y.1, hy'⟩ (s : ℂ) Φ Φ' e
    (fun τ hτ => (e ⟨τ, hτ⟩).1) (fun _ _ => rfl)
    ⟨fun _ => ⟨hθ'.1, hu⟩, fun _ => ⟨hθ.1, hu⟩⟩ rfl rfl rfl rfl
    hXs hm₀ hjs rfl
    (fun τ hτ => hprem τ (e ⟨τ, hτ⟩).1 θ θ' y.1 Φ Φ' (s : ℂ) 0 hτ (hjs τ hτ)
      (hXs τ hτ) hyR hΦ (by simpa using hum (s : ℂ) hs1))
    (fun τ hτ => hprem τ (e ⟨τ, hτ⟩).1 θ θ' y.1 Φ Φ' 0 0 hτ (hjs τ hτ)
      (hXs τ hτ) hyR hΦ (by simpa using hum 0 (by simp)))
  rw [show (NS'.AC θ' (s : ℂ)).H ⟨bm '' y.1, hy'⟩ Φ' = NS'.H θ' ⟨bm '' y.1, hy'⟩ (s : ℂ) Φ' from
    congrFun (NS'.hAC θ' hθ' (s : ℂ) ⟨bm '' y.1, hy'⟩) Φ',
    show (NS.AC θ (s : ℂ)).H y Φ = NS.H θ y (s : ℂ) Φ from congrFun (NS.hAC θ hθ (s : ℂ) y) Φ]
  exact key

theorem thick_labelCorr
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : (SA).JointRep t pp}
    {C' : StepClass d L N₁' m₁ k N ϱ} {z' : RootIdx d L N₁' m₁ (k + 1)} {pp' : ℝ}
    {Jr' : (SB).JointRep t pp'}
    (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' z' Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') {R : ℕ}
    (hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hr : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hc : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hc' : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hm₀ : NS'.O.m₀ = NS.O.m₀)
    (hE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ,
        NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm)
    (hprem : ∀ (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N (SA)) (θ' : physParam N (SB))
      (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (Φ : ∀ b, ((SA).blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 NS'.hp).Ωb b)
      (u t₀ : ℂ), NS.Dom Y τ → NS'.O.jL τ' = NS.O.jL τ →
      NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm → (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (‖u‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
        (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t) :
    ∃ ψ₁ : (∀ y : {Y // Y ∈ NS.𝒴C}, blocksOf 1 (k + 1) Set.univ y.1 ⊆ T →
        {Y // Y ∈ NS'.𝒴C}),
      (∀ y hy, blocksOf 1 (k + 1) Set.univ (ψ₁ y hy).1 =
        (blocksOf 1 (k + 1) Set.univ y.1).image (σc)) ∧
      (∀ y₁ hy₁ y₂ hy₂, ψ₁ y₁ hy₁ = ψ₁ y₂ hy₂ → y₁ = y₂) ∧
      (∀ y' : {Y // Y ∈ NS'.𝒴C}, blocksOf 1 (k + 1) Set.univ y'.1 ⊆ T.image (σc) →
        ∃ y hy, ψ₁ y hy = y') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hy,
        ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
          Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
            Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
          (NS'.AC θ' (s : ℂ)).H (ψ₁ y hy) Φ' = (NS.AC θ (s : ℂ)).H y Φ) := by
  classical
  have hYR1 : ∀ y : {Y // Y ∈ NS.𝒴C}, blocksOf 1 (k + 1) Set.univ y.1 ⊆ T →
      ∀ x ∈ y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun y hy => inBox_of_blocksOf_subset hN (NS.h𝒴dj y.1 y.2) hT hy
  have hmem : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ NS'.𝒴C ↔ Y ∈ NS.𝒴C) := by
    intro Y hY
    obtain ⟨e, -⟩ := hE Y hY
    rw [NS'.mem_𝒴C_iff, NS.mem_𝒴C_iff]
    constructor
    · rintro ⟨τ', hτ'⟩
      exact ⟨(e.symm ⟨τ', hτ'⟩).1, (e.symm ⟨τ', hτ'⟩).2⟩
    · rintro ⟨τ, hτ⟩
      exact ⟨(e ⟨τ, hτ⟩).1, (e ⟨τ, hτ⟩).2⟩
  obtain ⟨ψ₁, hψ⟩ : ∃ ψ₁ : (∀ y : {Y // Y ∈ NS.𝒴C}, blocksOf 1 (k + 1) Set.univ y.1 ⊆ T →
      {Y // Y ∈ NS'.𝒴C}), ∀ y hy, (ψ₁ y hy).1 = bm '' y.1 :=
    ⟨fun y hy => ⟨bm '' y.1, (hmem y.1 (hYR1 y hy)).2 y.2⟩, fun _ _ => rfl⟩
  refine ⟨ψ₁, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hψ]
    exact blocksOf_image_boxMap hN hN' hc hc' (hYR1 y hy)
  · intro y₁ hy₁ y₂ hy₂ h
    have h' := congrArg Subtype.val h
    rw [hψ, hψ] at h'
    exact Subtype.ext (image_boxMap_inj (N₁' := N₁') hm' (hYR1 y₁ hy₁) (hYR1 y₂ hy₂) h')
  · intro y' hy'
    obtain ⟨hYR, hYT, hYimg⟩ := exists_preimage_label hN hN' hm hm' hr hc hc' T hT
      (NS'.h𝒴dj y'.1 y'.2) hy'
    refine ⟨⟨_, (hmem _ hYR).1 (by rw [hYimg]; exact y'.2)⟩, hYT, Subtype.ext ?_⟩
    rw [hψ]
    exact hYimg
  · intro s hs y hy Φ Φ' hΦ
    have hy'mem := (hmem y.1 (hYR1 y hy)).2 y.2
    have hψy : ψ₁ y hy = ⟨bm '' y.1, hy'mem⟩ := Subtype.ext (hψ y hy)
    rw [hψy]
    exact thick_act_agree hN2 hk νS β p₁ δ NS NS' hm₀ hE hprem hum y (hYR1 y hy) hy'mem θ θ' hθ hθ'
      s hs Φ Φ' hΦ

end Coeff
end Balaban.Inhabited
