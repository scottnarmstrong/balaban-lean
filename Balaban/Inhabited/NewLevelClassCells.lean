/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffPairs
public import Balaban.Inhabited.NewLevelCanonHE
public import Balaban.Inhabited.NewLevelCanonHPrem
public import Balaban.Inhabited.NewLevelClassCoeff
public import Balaban.Inhabited.NewLevelCanonGeom

/-!
# The coefficient of the new level on two tori for canonical covers from local generating sets

`newLevel_coeff_twoTorus_of_class_cells`: `newLevel_coeff_twoTorus_of_class_of_cellTerms` with the geometry
hypothesis `hgeom` discharged by `hgeom_of_local` for canonical covers whose generating sets are local
generating sets of polymers (`CanonCoverLocal`).  The hypotheses besides the class, the pins, the
zero-source pins and `CellTermsAgree` are the cover requirements `hmarg`, `hcb` (the region `X₁` contains the `6 M`-neighbourhood of the margin and the cell box), the correspondence of the polymers, and size
conditions.
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

/-- **The coefficient of the new level on two tori for canonical covers built from local generating
sets.**  The geometry hypothesis of `newLevel_coeff_twoTorus_of_class_of_cellTerms` is discharged by
`hgeom_of_local`; `hmarg` (the `6 M`-neighbourhood of the margin lies in `X₁`) and `hcb` are the cover requirements and `hcell` the agreement of the irrelevant term at
the distinguished cell. -/
theorem newLevel_coeff_twoTorus_of_class_cells
    (hN2 : 2 ≤ N)
    (hk : 1 ≤ k)
    (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)}
    {t pp : ℝ}
    {Jr : (SA).JointRep t pp}
    {C' : StepClass d L N₁' m₁ k N ϱ}
    {pp' : ℝ}
    {Jr' : (SB).JointRep t pp'}
    (NS : NewLevelSystem (SA) C z Jr)
    (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁')
    (hm₁ : 1 ≤ m₁)
    {rc R : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {c Kc Cx c₂ : ℝ}
    (hC : FlCore N (GA) (HA) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hC' : FlCore N (GB) (HB) 1 νS c NS.BG NS.κ t Kc Cx c₂ NS.BG₂ t)
    (hκ : NS'.κ = NS.κ)
    (hBG : NS'.BG = NS.BG)
    (hBG₂ : NS'.BG₂ = NS.BG₂)
    (hp₁ : NS'.p₁ = NS.p₁)
    (hεU : NS.Z.εU = NS'.Z.εU)
    (hκH : NS.Z.κH = NS'.Z.κH)
    (hκ0 : NS.Z.κ0 = NS'.Z.κ0)
    (hGA : IsLevel (GA) (k + 1))
    (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    {δc : ℝ}
    (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (θ : physParam N (SA))
    (θ' : physParam N (SB))
    (hθ : θ ∈ physV (SA) (SA).a₁ (SA).ν t)
    (hθ' : θ' ∈ physV (SB) (SB).a₁ (SB).ν t)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z} (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hρc : 2 * NS.p₁ ≤ cψ)
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
    (i₀ i₁ : Fin N)
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁}
    {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    (hP : OldTermsCanonPinsAt (SA) C NS.O F i₀ i₁)
    (hP' : OldTermsCanonPinsAt (SB) C' NS'.O F' i₀ i₁)
    (hCm : C'.m₀ = C.m₀)
    {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ (k + 1) N ϱ}
    (hCT : C.Tm = Tm N₁)
    (hCT' : C'.Tm = Tm N₁')
    (hTI : TorusIndep C.m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₁').E j y X Ψ h = (Tm N₁').E j y X Ψ' h')
    (hM8 : 8 ≤ L ^ (C.m₀ + m₁))
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k → insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    (hcX' : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k → insert y₀ X₀ ⊆ ↑(F'.X₁fC j y₀ X₀))
    {R₂ : ℕ}
    (hRR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (hGA2 : (SA).G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hGB2 : (SB).G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hnE : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnE' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (LC : CanonCoverLocal F F')
    (SpG : DGSetting (SA).G' (compWeight L (SA).a₁) (SA).ν)
    (hbig : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁ * L ^ m₁ * L ^ (k + 1))
    (hbig' : 2 * (R + 1 + 6 * (k + 1) * L ^ (k + 1 + m₁) + (5 * L + 2) * L ^ (k + 1 + m₁) +
      L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < N₁' * L ^ m₁ * L ^ (k + 1))
    (hmarg : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      ∀ x ∈ canonZ LC j y₀ X₀, ∀ w : Fin d → ℤ,
        (∀ μ, |(w μ : ℝ)| < 6 * (L : ℝ) ^ ((k + 1) + m₁)) →
        x + (intTorus w : CTorus d L N₁ m₁ (k + 1)) ∈
          (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hcb : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      Localization.box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j))
        (L * cellSide L C.m₀ m₁ j) ⊆ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hPK : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      LC.PK' j (bm y₀) (bm '' X₀) = bm '' LC.PK j y₀ X₀)
    (hPJ : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      LC.PJ' j (bm y₀) (bm '' X₀) = bm '' LC.PJ j y₀ X₀)
    (hcell : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      CellTermsAgree C C' i₀ i₁ j y₀ X₀ (canonZ LC j y₀ X₀))
    {K : NewLevelConsts}
    (hK : NS.HasConsts K)
    (hK' : NS'.HasConsts K)
    {oδc : ℝ}
    (oMX : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (omar : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < oδc)
    (oαK : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (osm : oδc ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4)
    (hρ : 0 < NS.O.ρ)
    (hΦan : ∀ τ, AnalyticOnNhd ℂ (fun t' => (eTermFun (SA).G' (NS.O.Gk τ) (NS.O.Gj τ)
      (stepG d L N₁ m₁ k ϱ) (compWeight L (SA).a₁) (NS.O.FkL τ)
      (fun r => ((SA).β : ℂ)⁻¹ * NS.O.Eτ τ r)) t'.1 t'.2.1 t'.2.2)
      (FlReal (SA).G' (stepG d L N₁ m₁ k ϱ) (SA).a₁ (SA).ν NS.O.BG NS.O.κ t (NS.O.X₁f τ)
        NS.O.BG₂ NS.O.δ₁))
    (hn19 : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn19' : 4 * R + 19 * L ^ (k + 2 + NS.O.m₀ + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hmE₁ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmE₂ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (k + 1) < (N₁' * L ^ m₁) * L ^ (k + 1)):
    NS'.coeff θ' (T.image (σc)) = NS.coeff θ T := by
  exact newLevel_coeff_twoTorus_of_class_of_cellTerms (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (NS := NS) (NS' := NS') (hN := hN) (hN' := hN') (hm₁ := hm₁) (hz := hz) (hrc := hrc) (hroot := hroot) (hn := hn) (hn' := hn') (T := T) (hT := hT) (hC := hC) (hC' := hC') (hκ := hκ) (hBG := hBG) (hBG₂ := hBG₂) (hp₁ := hp₁) (hεU := hεU) (hκH := hκH) (hκ0 := hκ0) (hGA := hGA) (hGB := hGB) (hMX := hMX) (hmar := hmar) (hαK := hαK) (hsm := hsm) (θ := θ) (θ' := θ') (hθ := hθ) (hθ' := hθ') (hraw := hraw) (hcψ := hcψ) (hρc := hρc) (hrad := hrad) (hI𝒴 := hI𝒴) (hI𝒴' := hI𝒴') (hum := hum) (humB := humB) (hδc := hδc) (hconn := hconn) (hconn' := hconn') (hD := hD) (hD' := hD') (i₀ := i₀) (i₁ := i₁) (hP := hP) (hP' := hP') (hCm := hCm) (hCT := hCT) (hCT' := hCT') (hTI := hTI) (hlocB := hlocB) (hM8 := hM8) (hcX := hcX) (hcX' := hcX') (hRR := hRR) (hcloc := hcloc) (hcov := hcov) (hGA2 := hGA2) (hGB2 := hGB2) (hnE := hnE) (hnE' := hnE') (hK := hK) (hK' := hK') (oMX := oMX) (omar := omar) (oαK := oαK) (osm := osm) (hρ := hρ) (hΦan := hΦan) (hn19 := hn19) (hn19' := hn19') (hmE₁ := hmE₁) (hmE₂ := hmE₂) (hgeom := hgeom_of_local LC NS.hL SpG hbig hbig' hmarg hcb hPK hPJ hcell)

end Final

end Balaban.Inhabited
