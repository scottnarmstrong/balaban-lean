/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelAnchorG

/-!
# The anchors and the marks of two systems of the new level on two tori

`newLevel_kappa_data`: the anchors of the marks with blocks in a set `T` of the box correspond to
those with blocks in `cubeMap '' T` and the marks `NewLevelSystem.G` agree at corresponding anchors
(`anchor_inl_corr`, `anchor_inr_corr`, `anchor_G_inl`, `anchor_G_inr`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

section Kappa

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
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))

attribute [local irreducible] NewLevelSystem.Dom

/-- **The anchors of the marks of two systems correspond on two tori, and their marks agree.** -/
theorem newLevel_kappa_data
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (Q : NS.O.ι → NS'.O.ι → Prop)
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) (hrc : L ^ (k + 1) * rc ≤ R) (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t) (hC' : FlCore N (GB) (HB) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hκ : NS'.κ = NS.κ) (hBG : NS'.BG = NS.BG) (hBG₂ : NS'.BG₂ = NS.BG₂) (hp₁ : NS'.p₁ = NS.p₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc) (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2) (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t) (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z} (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    (hm₀ : NS'.O.m₀ = NS.O.m₀)
    (hE : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ, NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm ∧ Q τ.1 (e τ).1)
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
    (humB : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k 1 NS.κ NS.p₁ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁) :
    ∃ κ : (∀ i : NS.AnchorIdx, blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i)) ⊆ T →
        NS'.AnchorIdx),
      (∀ i hi, blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite (NS'.y0 (κ i hi))) =
        (blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i))).image (σc)) ∧
      (∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂) ∧
      (∀ i' : NS'.AnchorIdx,
        blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite (NS'.y0 i')) ⊆ T.image (σc) →
        ∃ i hi, κ i hi = i') ∧
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hi, ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x → Φ' ((SB).cellOf 1 (unitPt (SB).hG' (bm x))) ⟨unitPt (SB).hG' (bm x), rfl⟩ = Φ ((SA).cellOf 1 (unitPt (SA).hG' x)) ⟨unitPt (SA).hG' x, rfl⟩) →
        (NS'.G θ') (κ i hi) (s : ℂ) Φ' = (NS.G θ) i (s : ℂ) Φ) := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, hnH, hnM⟩, ⟨hn1', hnS', hnF', hnH', hnM'⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hc : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hc' : 2 * R + cellSide L 1 m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  obtain ⟨φ, hφr, hφi, hφs⟩ := anchor_inl_corr (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (T := T) (hT := hT)
  obtain ⟨ψ, hψr, hψi, hψs, hψb⟩ := anchor_inr_corr (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (T := T) (hT := hT) (hE := hE) (Q := Q)
  have hbox : ∀ a : {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG (SA)) z},
      blocksOf 1 (k + 1) Set.univ a.1 ⊆ T → ∀ x ∈ a.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x :=
    fun a hi => inBox_of_blocksOf_subset (Y := a.1) hN
      (bridgeFamily_isDj hN NS.hL NS.hdomE z a.1 a.2) hT hi
  refine ⟨fun i => match i with
    | Sum.inl a => fun hi => Sum.inl (φ a hi)
    | Sum.inr q => fun hi => Sum.inr (ψ q hi), ?_, ?_, ?_, ?_⟩
  · rintro (a | q) hi
    · show blocksOf 1 (k + 1) Set.univ (φ a hi).1 = (blocksOf 1 (k + 1) Set.univ a.1).image (σc)
      rw [hφr a hi]
      exact blocksOf_image_boxMap hN hN' hc hc' (hbox a hi)
    · exact hψb q hi
  · rintro (a₁ | q₁) h₁ (a₂ | q₂) h₂ h
    · exact congrArg Sum.inl (hφi a₁ h₁ a₂ h₂ (by simpa using h))
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact congrArg Sum.inr (hψi q₁ h₁ q₂ h₂ (by simpa using h))
  · rintro (b | q') hi'
    · obtain ⟨a, ha, h⟩ := hφs b hi'
      exact ⟨Sum.inl a, ha, congrArg Sum.inl h⟩
    · obtain ⟨q, hq, h⟩ := hψs q' hi'
      exact ⟨Sum.inr q, hq, congrArg Sum.inr h⟩
  · rintro s hs (a | q) hi Φ Φ' hΦ
    · exact anchor_G_inl (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (hC := hC) (hC' := hC') (hκ := hκ) (hBG := hBG) (hBG₂ := hBG₂) (hp₁ := hp₁) (hGA := hGA) (hGB := hGB) (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (θ := θ) (θ' := θ') (hθ := hθ) (hθ' := hθ') (hraw := hraw) (hum := humB) a (φ a hi) (hφr a hi) (hbox a hi) s hs Φ Φ' hΦ
    · obtain ⟨h2, hYR, hDom, hj, hX, hQ⟩ := hψr q hi
      exact anchor_G_inr (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hm₀ := hm₀) (hprem := hprem) (Q := Q) (hum := hum) (θ := θ) (θ' := θ') (hθ := hθ) (hθ' := hθ') (hraw := hraw) q (ψ q hi) h2 hYR hDom hj hX hQ s hs Φ Φ' hΦ

end Kappa

end Balaban.Inhabited
