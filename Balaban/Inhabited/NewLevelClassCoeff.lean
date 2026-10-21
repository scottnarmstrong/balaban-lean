/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffPairs
public import Balaban.Inhabited.NewLevelCanonHE
public import Balaban.Inhabited.NewLevelCanonHPrem

/-!
# The coefficient of the new level on two tori for canonically pinned inherited levels

`newLevel_coeff_twoTorus_of_class_of_cellTerms`: two systems of the new level on two tori whose
inherited levels are canonically indexed and covered (`OldTermsCanonPinsAt`) have the same coefficient on
the blocks of the box.  The index bijections are `canon_hE`, the premises of the comparison of
corresponding old terms are `canon_hprem` (with the cell case `CellTermsAgree` inside the geometry data),
and the coefficient is `newLevel_coeff_twoTorus_of_pairs`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep
  Balaban.SmallField.Def6v2

section Final

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
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

attribute [local irreducible] NewLevelSystem.Dom

/-- **The coefficient of the new level on two tori for systems with canonically pinned inherited
levels.**  Two systems `NS`, `NS'` of the new level (steps `hatStepKG`, roots `z`, `bc z`, the same `t`)
whose inherited levels are indexed and covered canonically (`OldTermsCanonPinsAt`) have the same
coefficient on the blocks of the box.  Hypotheses: the class (the old terms are the torus-independent
irrelevant terms `irrelTorus` of the small-field terms `Tm`), the geometry of the canonical covers and of
the margins of the old terms (`hgeom`, whose last clause is the agreement of the irrelevant term at the
distinguished cell, `hcellcase` of `oldTerm_E_agree`), the typing and numerical data of the decoupled
fields, and the explicit form of the zero-source direct terms (`hI𝒴`). -/
theorem newLevel_coeff_twoTorus_of_class_of_cellTerms
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z) 
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1)) (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t) (hC' : FlCore N (GB) (HB) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hκ : NS'.κ = NS.κ) (hBG : NS'.BG = NS.BG) (hBG₂ : NS'.BG₂ = NS.BG₂) (hp₁ : NS'.p₁ = NS.p₁)
    (hεU : NS.Z.εU = NS'.Z.εU) (hκH : NS.Z.κH = NS'.Z.κH)
    (hκ0 : NS.Z.κ0 = NS'.Z.κ0)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc) (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2) (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (θ : physParam N (SA)) (θ' : physParam N (SB)) (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t) (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t) (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z} (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
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
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k (SA).a₁ NS.O.κ NS.O.ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (humB : ∀ u : ℂ, ‖u‖ ≤ 1 → ‖u‖ * markedRad d L N k 1 NS.κ NS.p₁ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hδc : 0 ≤ δc)
    (hconn : HatConn (SA).G')
    (hconn' : HatConn (SB).G')
    (hD : XiCData (SA).G' (compWeight L 1) (SA).ν (k + 1) 1 t (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2))
    (hD' : XiCData (SB).G' (compWeight L 1) (SA).ν (k + 1) 1 t (bgOfRaw (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) θ'.1.2))
    (i₀ i₁ : Fin N) {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    (hP : OldTermsCanonPinsAt (SA) C NS.O F i₀ i₁) (hP' : OldTermsCanonPinsAt (SB) C' NS'.O F' i₀ i₁)
    (hCm : C'.m₀ = C.m₀)
    {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ (k + 1) N ϱ} (hCT : C.Tm = Tm N₁)
    (hCT' : C'.Tm = Tm N₁') (hTI : TorusIndep C.m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₁').E j y X Ψ h = (Tm N₁').E j y X Ψ' h')
    (hM8 : 8 ≤ L ^ (C.m₀ + m₁))
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k → insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    (hcX' : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k → insert y₀ X₀ ⊆ ↑(F'.X₁fC j y₀ X₀))
    {R₂ : ℕ} (hRR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (hGA2 : (SA).G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hGB2 : (SB).G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hnE : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hgeom : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      (∀ μ : Fin d, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
        (y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)))) ∧
      (∀ z ∈ box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j)) (L * cellSide L C.m₀ m₁ j), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z) ∧
      ∃ Z : Set (CTorus d L N₁ m₁ (k + 1)), X₀ ⊆ Z ∧
        (∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈ Z) ∧
        Z ⊆ ↑(F.X₁fC j y₀ X₀) ∧ BlockMargin (SA).G' (F.X₁fC j y₀ X₀) Z ∧
        GSCorr (F.GkC j y₀ X₀) (F'.GkC j (bm y₀) (bm '' X₀)) bm Z ∧
        GSCorr (F.GjC j y₀ X₀) (F'.GjC j (bm y₀) (bm '' X₀)) bm Z ∧
        GSIso (compWeight L (SA).a₁) (SA).ν (F.GkC j y₀ X₀) (F'.GkC j (bm y₀) (bm '' X₀)) bm Z ∧
        (∀ z ∈ Z, z ∈ (F.GkC j y₀ X₀).Ω 1 →
          (∀ y ∈ (F.GkC j y₀ X₀).blk ((F.GkC j y₀ X₀).layerIndex z) z, y ∈ Z) ∧
          (∀ y ∈ (SA).G'.blk ((SA).G'.layerIndex z) z, y ∈ Z) ∧
          (∀ y ∈ (stepG d L N₁ m₁ k ϱ).blk ((stepG d L N₁ m₁ k ϱ).layerIndex z) z, y ∈ Z)) ∧
        (∀ z ∈ Z, z ∈ (F.GjC j y₀ X₀).Ω 1 →
          (∀ y ∈ (F.GjC j y₀ X₀).blk ((F.GjC j y₀ X₀).layerIndex z) z, y ∈ Z) ∧
          (∀ y ∈ (F.GkC j y₀ X₀).blk ((F.GkC j y₀ X₀).layerIndex z) z, y ∈ Z)) ∧
        CellTermsAgree C C' i₀ i₁ j y₀ X₀ Z)
    {K : NewLevelConsts} (hK : NS.HasConsts K) (hK' : NS'.HasConsts K)
    {oδc : ℝ} (oMX : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (omar : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < oδc)
    (oαK : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (osm : oδc ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) (hρ : 0 < NS.O.ρ)
    (hΦan : ∀ τ, AnalyticOnNhd ℂ (fun t' => (eTermFun (SA).G' (NS.O.Gk τ) (NS.O.Gj τ)
      (stepG d L N₁ m₁ k ϱ) (compWeight L (SA).a₁) (NS.O.FkL τ)
      (fun r => ((SA).β : ℂ)⁻¹ * NS.O.Eτ τ r)) t'.1 t'.2.1 t'.2.2)
      (FlReal (SA).G' (stepG d L N₁ m₁ k ϱ) (SA).a₁ (SA).ν NS.O.BG NS.O.κ t (NS.O.X₁f τ)
        NS.O.BG₂ NS.O.δ₁))
    (hn19 : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn19' : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hmE₁ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmE₂ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1)) :
    NS'.coeff θ' (T.image (σc)) = NS.coeff θ T := by
  classical
  obtain ⟨hm₀, y, X, hEτ, hB, hpin⟩ := hP
  obtain ⟨hm₀', y', X', hEτ', hB', hpin'⟩ := hP'
  have hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ) := fun τ => (hpin τ).1
  have hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ) := fun τ => (hpin' τ).1
  have hGk : ∀ τ, NS.O.Gk τ = F.GkC (NS.O.jL τ) (y τ) (X τ) := fun τ => (hpin τ).2.2.1
  have hGk' : ∀ τ, NS'.O.Gk τ = F'.GkC (NS'.O.jL τ) (y' τ) (X' τ) := fun τ => (hpin' τ).2.2.1
  have hGj : ∀ τ, NS.O.Gj τ = F.GjC (NS.O.jL τ) (y τ) (X τ) := fun τ => (hpin τ).2.2.2.1
  have hGj' : ∀ τ, NS'.O.Gj τ = F'.GjC (NS'.O.jL τ) (y' τ) (X' τ) := fun τ => (hpin' τ).2.2.2.1
  have hrc0 : L ^ (k + 1) * rc ≤ R := by omega
  have hm₀N : NS'.O.m₀ = NS.O.m₀ := by rw [hm₀', hCm, hm₀]
  have hE := canon_hE (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hB := hB) (hB' := hB') (hX₁ := hX₁) (hX₁' := hX₁') (hm₀ := hm₀) (hm₀' := hm₀') (hC := hCm) (hcX := hcX) (hcX' := hcX') (hR := hRR) (hcloc := hcloc) (hcov := hcov) (hGA := hGA2) (hGB := hGB2) (hn := hnE) (hn' := hnE')
  have hprem := canon_hprem (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (i₀ := i₀) (i₁ := i₁) (hB := hB) (hX₁ := hX₁) (hm₀ := hm₀) (hm₀' := hm₀') (hC := hCm) (hEτ := hEτ) (hEτ' := hEτ') (hGk := hGk) (hGk' := hGk') (hGj := hGj) (hGj' := hGj') (hcX := hcX) (hCT := hCT) (hCT' := hCT') (hTI := hTI) (hlocB := hlocB) (hM8 := hM8) (hgeom := hgeom) (hK := hK) (hK' := hK') (hMX := oMX) (hmar := omar) (hαK := oαK) (hsm := osm) (hρ := hρ) (hΦan := hΦan) (hm₁ := hm₁) (hn19 := hn19) (hn19' := hn19') (hm₀N := hm₀N) (hmE₁ := hmE₁) (hmE₂ := hmE₂) (hz := hz) (hrc := hrc0) (hGA := hGA) (hGB := hGB)
  exact newLevel_coeff_twoTorus_of_pairs (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (Q := fun τ τ' => y' τ' = bm (y τ) ∧ X' τ' = bm '' X τ) (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (T := T) (hT := hT) (hC := hC) (hC' := hC') (hκ := hκ) (hBG := hBG) (hBG₂ := hBG₂) (hp₁ := hp₁) (hεU := hεU) (hκH := hκH) (hκ0 := hκ0) (hGA := hGA) (hGB := hGB) (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (hδc := hδc) (θ := θ) (θ' := θ') (hθ := hθ) (hθ' := hθ') (hraw := hraw) (hcψ := hcψ) (hρc := hρc) (hrad := hrad) (hI𝒴 := hI𝒴) (hI𝒴' := hI𝒴') (hm₀ := hm₀N) (hE := hE) (hprem := hprem) (humB := humB) (hum := hum) (hconn := hconn) (hconn' := hconn') (hD := hD) (hD' := hD')

end Final

end Balaban.Inhabited
