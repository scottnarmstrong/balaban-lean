/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelZeroCorr
public import Balaban.Inhabited.NewLevelThickCorr

/-!
# The active labels of two systems of the new level on two tori

`NewLevelSystem.IsActLab`: the labels with a non-zero activity (the zero-source labels and the thick
labels).  `newLevel_psi_data`: the active labels with blocks in a set `T` of the box correspond to
those with blocks in `cubeMap '' T` and the activities `NewLevelSystem.A` agree at corresponding
labels (`zeroSource_labelCorr`, `thick_labelCorr`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

section Psi

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))

/-- The labels of the new level with a non-zero activity: the labels of the zero-source family and
the thick labels (the labels of the roots are extended by zero). -/
def NewLevelSystem.IsActLab {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) : NS.LbAll → Prop :=
  Sum.elim (Sum.elim (fun _ => True) (Sum.elim (fun _ => True) (fun _ => False))) (fun _ => False)

theorem NewLevelSystem.not_isActLab_c {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr)
    (r : RootUnionLb 1 (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))) :
    ¬ NS.IsActLab (Sum.inl (Sum.inr (Sum.inr r))) := fun h => h

theorem NewLevelSystem.not_isActLab_d {S : StepSetting d L N₁ m₁ k N ϱ}
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ}
    {Jr : S.JointRep t pp} (NS : NewLevelSystem S C z Jr)
    (r : RootUnionLb 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S)) :
    ¬ NS.IsActLab (Sum.inr r) := fun h => h

/-- **The activity of the new level vanishes off the active labels.** -/
theorem NewLevelSystem.A_H_inactive {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) (θ : physParam N S) (u : ℂ) (y : NS.LbAll)
    (hy : ¬ NS.IsActLab y) (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) : (NS.A θ u).H y Φ = 0 := by
  rcases y with (a | b | r) | r
  · exact absurd trivial hy
  · exact absurd trivial hy
  · rfl
  · rfl

attribute [local irreducible] NewLevelSystem.Dom

/-- **The active labels of two systems correspond on two tori, and their activities agree.** -/
theorem newLevel_psi_data
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (Q : NS.O.ι → NS'.O.ι → Prop)
    (hκ : NS'.κ = NS.κ) (hBG : NS'.BG = NS.BG) (hBG₂ : NS'.BG₂ = NS.BG₂)
    (hp₁ : NS.p₁ = NS'.p₁) (hεU : NS.Z.εU = NS'.Z.εU) (hκH : NS.Z.κH = NS'.Z.κH)
    (hκ0 : NS.Z.κ0 = NS'.Z.κ0)
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      k (Nat.le_succ k)) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hC' : FlCore N (GB) (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      k (Nat.le_succ k)) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (hm₁ : 1 ≤ m₁) {R : ℕ}
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρc : 2 * NS.p₁ ≤ cψ)
    (hrad : markedRad d L N k 1 NS.κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hI𝒴 : NS.Z.I.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hI𝒴' : NS'.Z.I.𝒴 = (Finset.univ.biUnion fun z : TB =>
        polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁' m₁ (k + 1) × Fin N =>
        polyDom (GB) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hm₀ : NS'.O.m₀ = NS.O.m₀)
    (hE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ,
        NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm ∧
        Q τ.1 (e τ).1)
    (hprem : ∀ (τ : NS.O.ι) (τ' : NS'.O.ι) (θ : physParam N (SA)) (θ' : physParam N (SB))
      (Y : Set (CTorus d L N₁ m₁ (k + 1)))
      (Φ : ∀ b, ((SA).blockSplit 1 NS.hp).Ωb b) (Φ' : ∀ b, ((SB).blockSplit 1 NS'.hp).Ωb b)
      (u t₀ : ℂ), θ ∈ physV (SA) (SA).a₁ (SA).ν t → θ' ∈ physV (SB) (SB).a₁ (SB).ν t →
      RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) →
      Q τ τ' → NS.Dom Y τ → NS'.O.jL τ' = NS.O.jL τ →
      NS'.O.X₁f τ' = (NS.O.X₁f τ).image bm → (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
      (‖u‖ + ‖t₀‖) * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ
        (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      TermPairPremisesAt NS NS' τ τ' θ θ' Y Φ Φ' u t₀)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁) :
    ∃ ψ : (∀ y : NS.LbAll, NS.IsActLab y →
        blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite y) ⊆ T → NS'.LbAll),
      (∀ y hP hy, NS'.IsActLab (ψ y hP hy)) ∧
      (∀ y hP hy, blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite (ψ y hP hy)) =
        (blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite y)).image (σc)) ∧
      (∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂) ∧
      (∀ y' : NS'.LbAll, NS'.IsActLab y' →
        blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite y') ⊆ T.image (σc) →
        ∃ y hP hy, ψ y hP hy = y') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy,
        ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ = Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        ((NS'.A θ') (s : ℂ)).H (ψ y hP hy) Φ' = ((NS.A θ) (s : ℂ)).H y Φ) := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hc : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hc' : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hr : 2 * R + L * cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨ψ₀, h0b, h0i, h0s, h0A⟩ := zeroSource_labelCorr hN2 hk νS β p₁ δ NS NS' hκ hBG hBG₂
    hp₁ hεU hκH hκ0 hC hC' hGA hGB hMX hmar hαK hsm hN hN' hm₁ hn hn' θ θ' hθ hθ' hraw hcψ hρc
    hrad hI𝒴 hI𝒴' T hT
  obtain ⟨ψ₁, h1b, h1i, h1s, h1A⟩ := thick_labelCorr hN2 hk νS β p₁ δ NS NS' Q hN hN' hm hm' hr hc
    hc' T hT hm₀ hE hprem hum θ θ' hθ hθ' hraw
  refine ⟨fun y => match y with
    | Sum.inl (Sum.inl a) => fun _ hy => Sum.inl (Sum.inl (ψ₀ a hy))
    | Sum.inl (Sum.inr (Sum.inl b)) => fun _ hy => Sum.inl (Sum.inr (Sum.inl (ψ₁ b hy)))
    | Sum.inl (Sum.inr (Sum.inr r)) => fun hP _ => absurd hP (NS.not_isActLab_c r)
    | Sum.inr r => fun hP _ => absurd hP (NS.not_isActLab_d r), ?_, ?_, ?_, ?_, ?_⟩
  · rintro ((a | b | r) | r) hP hy
    · exact trivial
    · exact trivial
    · exact absurd hP (NS.not_isActLab_c r)
    · exact absurd hP (NS.not_isActLab_d r)
  · rintro ((a | b | r) | r) hP hy
    · exact h0b a hy
    · exact h1b b hy
    · exact absurd hP (NS.not_isActLab_c r)
    · exact absurd hP (NS.not_isActLab_d r)
  · rintro ((a₁ | b₁ | r₁) | r₁) hP₁ hy₁ ((a₂ | b₂ | r₂) | r₂) hP₂ hy₂ h <;>
      first
      | exact absurd hP₁ (NS.not_isActLab_c r₁)
      | exact absurd hP₁ (NS.not_isActLab_d r₁)
      | exact absurd hP₂ (NS.not_isActLab_c r₂)
      | exact absurd hP₂ (NS.not_isActLab_d r₂)
      | skip
    · exact congrArg (fun a => Sum.inl (Sum.inl a)) (h0i a₁ hy₁ a₂ hy₂ (by simpa using h))
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact congrArg (fun b => Sum.inl (Sum.inr (Sum.inl b))) (h1i b₁ hy₁ b₂ hy₂ (by simpa using h))
  · rintro ((a | b | r) | r) hP hy
    · obtain ⟨y, hy0, rfl⟩ := h0s a hy
      exact ⟨Sum.inl (Sum.inl y), trivial, hy0, rfl⟩
    · obtain ⟨y, hy0, rfl⟩ := h1s b hy
      exact ⟨Sum.inl (Sum.inr (Sum.inl y)), trivial, hy0, rfl⟩
    · exact absurd hP (NS'.not_isActLab_c r)
    · exact absurd hP (NS'.not_isActLab_d r)
  · rintro s hs ((a | b | r) | r) hP hy Φ Φ' hΦ
    · exact h0A s hs a hy Φ Φ' hΦ
    · exact h1A s hs b hy Φ Φ' hΦ
    · exact absurd hP (NS.not_isActLab_c r)
    · exact absurd hP (NS.not_isActLab_d r)

end Psi

end Balaban.Inhabited
