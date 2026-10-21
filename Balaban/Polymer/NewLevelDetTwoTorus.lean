/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusCoef
public import Balaban.Fluctuation.NewLevelCoeffBg

/-!
# The determinant part of the coefficient of the new level on two tori

`newLevelDetBg_twoTorus`: `sum_blockU_detActivityBg_twoTorus` for the determinant part
`newLevelDetBg` of generating sets equal to the whole-lattice ones (`GA' = levelGS`, by `subst`), at
parameters `θ`, `θ'` whose raw data agree on the box.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Polymer Balaban.Multiscale Balaban.Background

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

/-- **The determinant part of the coefficient on two tori.** -/
theorem newLevelDetBg_twoTorus
    {GA' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {GB' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ}
    (eGA : GA' = GA) (eGB : GB' = GB)
    (θ : physParamBg N GA') (θ' : physParamBg N GB')
 (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N GA' Hm 1 ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N GB' Hm' 1 ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn GA') (hconn' : HatConn GB')
    (hD : XiCData GA' (compWeight L 1) ν (k + 1) 1 eps (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2))
    (hD' : XiCData GB' (compWeight L 1) ν (k + 1) 1 eps (bgOfRaw (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) θ'.1.2))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {rc r : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ r)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
      Set.univ))
    (hYr : ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (r + 2 * (L * (cellSide L 1 m₁ (k + 1)))) + L * (cellSide L 1 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * (cellSide L 1 m₁ (k + 1)))) + L * (cellSide L 1 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (r + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf (bgOfRaw (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) θ.1.2)) (rawOf (bgOfRaw (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) θ'.1.2))) :
    newLevelDetBg GB' (compWeight L 1) 1 ν (rho4 d L N BG κ)
        (Finset.univ.filter fun u : unitPts GB' => unitBlock1 (u : UnitTorus d L N₁' m₁ k) = bc z)
        θ' (Y.image (cubeMap hN hN' le_rfl)) =
      newLevelDetBg GA' (compWeight L 1) 1 ν (rho4 d L N BG κ)
        (Finset.univ.filter fun u : unitPts GA' => unitBlock1 (u : UnitTorus d L N₁ m₁ k) = z)
        θ Y := by
  subst eGA eGB
  exact sum_blockU_detActivityBg_twoTorus (hN := hN) (hN' := hN') (hC := hC) (hC' := hC') (hk := hk) (hδc := hδc) (hcap := hcap) (hsm := hsm) (hmar := hmar) (hαK := hαK) (hconn := hconn) (hconn' := hconn') (hD := hD) (hD' := hD') (z := z) (hz := hz) (hrc := hrc) (hroot := hroot) (Y := Y) (hYr := hYr) (hn := hn) (hn' := hn') (hnS := hnS) (hnS' := hnS') (hnH := hnH) (hnH' := hnH') (hraw := hraw)

end Balaban.Polymer.TwoTorusStep
