/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.NewLevelDetTwoTorus
public import Balaban.Polymer.TwoTorusE1Coef
public import Balaban.Inhabited.NewLevelGPairs

/-!
# The coefficient of the new level on two tori

`NewLevelSystem.coeff_twoTorus`: for two systems of the tower steps `hatStepKG` on the tori `N₁`,
`N₁'` (with the roots `z` and `bc z`), the coefficients `NS.coeff θ T` and `NS'.coeff θ' (T.image cubeMap)`
agree: the determinant parts by `newLevelDetBg_twoTorus` and the interpolation coefficients by
`gsumCoeff_blockSplit_twoTorus` (generic `gsumCoeff_transport`), from the premises of the two
lemmas: the correspondence of the active labels, of the activities and of the marks.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Polymer.TwoTorusStep Balaban.Multiscale Balaban.Background
  Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ}

/-- The labels of all roots of a system. -/
abbrev NewLevelSystem.LbAll {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) : Type :=
  NS.Lb1 ⊕ RootUnionLb 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S)

/-- The anchors of the marks of a system. -/
abbrev NewLevelSystem.AnchorIdx {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
    (NS : NewLevelSystem S C z Jr) : Type :=
  {Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
    (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
    {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
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
local notation "𝔅A" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
  Set.univ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

/-- **The coefficient of the new level on two tori.** -/
theorem NewLevelSystem.coeff_twoTorus
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)}
    {C' : StepClass d L N₁' m₁ k N ϱ}
    (hN2 : 2 ≤ N)
    (hk : 1 ≤ k)
    (νS β p₁ δ : ℝ)
    {t pp : ℝ} {Jr : (SA).JointRep t pp} {t' pp' : ℝ} {Jr' : (SB).JointRep t' pp'}
    (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hBG : NS'.BG = NS.BG) (hκ : NS'.κ = NS.κ)
    {R : ℕ}
    (hN : L ^ 1 ∣ N₁)
    (hN' : L ^ 1 ∣ N₁')
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel (GA) (k + 1))
    (hGB : IsLevel (GB) (k + 1))
    (hp : 0 < (SA).p₁)
    (hp' : 0 < (SB).p₁)
    (hGdep : ∀ i u, DepOn (blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i))) ((NS.G θ) i u))
    (T : Finset (𝔅A))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (P : NS.LbAll → Prop)
    (P' : NS'.LbAll → Prop)
    (hA0 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ¬ P y → ∀ Φ, ((NS.A θ) (s : ℂ)).H y Φ = 0)
    (hA0' : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y', ¬ P' y' → ∀ Φ', ((NS'.A θ') (s : ℂ)).H y' Φ' = 0)
    (ψ : ∀ y, P y → blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite y) ⊆ T → NS'.LbAll)
    (hψP : ∀ y hP hy, P' (ψ y hP hy))
    (hψb : ∀ y hP hy, blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite (ψ y hP hy)) =
      (blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite y)).image (σc))
    (hψinj : ∀ y₁ hP₁ hy₁ y₂ hP₂ hy₂, ψ y₁ hP₁ hy₁ = ψ y₂ hP₂ hy₂ → y₁ = y₂)
    (hψsurj : ∀ y', P' y' → blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite y') ⊆ T.image (σc) →
      ∃ y hP hy, ψ y hP hy = y')
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y hP hy,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) →
        ((NS'.A θ') (s : ℂ)).H (ψ y hP hy) Φ' = ((NS.A θ) (s : ℂ)).H y Φ)
    (κ : ∀ i, blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i)) ⊆ T → NS'.AnchorIdx)
    (hκb : ∀ i hi, blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite (NS'.y0 (κ i hi))) =
      (blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i))).image (σc))
    (hκinj : ∀ i₁ hi₁ i₂ hi₂, κ i₁ hi₁ = κ i₂ hi₂ → i₁ = i₂)
    (hκsurj : ∀ i', blocksOf 1 (k + 1) Set.univ (NS'.Lab.ysite (NS'.y0 i')) ⊆ T.image (σc) →
      ∃ i hi, κ i hi = i')
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i hi,
      ∀ Φ Φ', (∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
        Φ' ((SB).cellOf 1 (unitPt hGB (bm x))) ⟨unitPt hGB (bm x), rfl⟩ =
          Φ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩) →
        (NS'.G θ') (κ i hi) (s : ℂ) Φ' = (NS.G θ) i (s : ℂ) Φ)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {c eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (SA).G' Hm 1 (SA).ν c NS.BG NS.κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (SB).G' Hm' 1 (SA).ν c NS.BG NS.κ eps Kc Cx c₂ BG₂ δ₁)
    {δc : ℝ}
    (hδc : 0 ≤ δc)
    (hcap : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4)
    (hmar : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (SA).G')
    (hconn' : HatConn (SB).G')
    (hD : XiCData (SA).G' (compWeight L 1) (SA).ν (k + 1) 1 eps (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2))
    (hD' : XiCData (SB).G' (compWeight L 1) (SA).ν (k + 1) 1 eps (bgOfRaw (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) θ'.1.2))
    {rc r : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ r)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hYr : ∀ x ∈ sitesOf T, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hnd : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnd' : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (r + 2 * (L * (cellSide L 1 m₁ (k + 1)))) + L * (cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * (cellSide L 1 m₁ (k + 1)))) + L * (cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (r + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2)) (rawOf (bgOfRaw (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) θ'.1.2))) :
    NS'.coeff θ' (T.image σc) = NS.coeff θ T := by
  have hd : newLevelDetBg (SB).G' (compWeight L 1) 1 (SB).ν (rho4 d L N NS'.BG NS'.κ)
      ((SB).blockU (bc z)) θ' (T.image σc) =
      newLevelDetBg (SA).G' (compWeight L 1) 1 (SA).ν (rho4 d L N NS.BG NS.κ)
      ((SA).blockU z) θ T := by
    rw [hBG, hκ]
    exact newLevelDetBg_twoTorus (GA' := (SA).G') (GB' := (SB).G') rfl rfl θ θ' hN hN' hk (hC := hC) (hC' := hC') (hδc := hδc) (hcap := hcap) (hsm := hsm) (hmar := hmar) (hαK := hαK) (hconn := hconn) (hconn' := hconn') (hD := hD) (hD' := hD') (hz := hz) (hrc := hrc) (hroot := hroot) (hYr := hYr) (hn := hnd) (hn' := hnd') (hnS := hnS) (hnS' := hnS') (hnH := hnH) (hnH' := hnH') (hraw := hraw)
  have hg := gsumCoeff_blockSplit_twoTorus (hN2 := hN2) (hk := hk) (νS := νS) (β := β) (p₁ := p₁) (δ := δ) (Lab := NS.Lab) (Lab' := NS'.Lab) (A := NS.A θ) (A' := NS'.A θ') (y0 := NS.y0) (y0' := NS'.y0) (G := NS.G θ) (G' := NS'.G θ') (hN := hN) (hN' := hN') (hn := hn) (hn' := hn') (hGA := hGA) (hGB := hGB) (hp := hp) (hp' := hp') (hGdep := hGdep) (T := T) (hT := hT) (P := P) (P' := P') (hA0 := hA0) (hA0' := hA0') (ψ := ψ) (hψP := hψP) (hψb := hψb) (hψinj := hψinj) (hψsurj := hψsurj) (hA := hA) (κ := κ) (hκb := hκb) (hκinj := hκinj) (hκsurj := hκsurj) (hG := hG)
  exact congrArg₂ (· + ·) hd hg

end Balaban.Inhabited
