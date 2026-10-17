/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapObsRecentreCoef
public import Balaban.Polymer.TwoTorusGapIdentDet
public import Balaban.Fluctuation.DetSymmGroup

/-!
# The determinant block sum under the recentring map (item 24, blocker 7)

`sum_blockU_detActivityBg_recentred`: the sum over the unit points of the block `B_{k+1}(z')` of the
second torus of the determinant activities at a set `Y'` of cubes equals the sum over the unit points
of the block `B_{k+1}(z)` of the first torus at `Y`, when the translate of `z'` by `tB` is the
`bc`-image of the translate of `z` by `tA` and the translate of `Y'` by `tB` is the `cubeMap`-image of the
translate of `Y` by `tA`.  Composition of the translation covariance of the block sums
(`sum_detActivityBg_sym_genSymm`) on each torus with the landed transport between two tori
(`sum_blockU_detActivityBg_twoTorus`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory
  Balaban.Localization.DetUnitIncidence Balaban.Inhabited Balaban.Inhabited.LevelStep

section DetSum

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
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

/-- **The determinant block sum under the recentring map.** -/
theorem sum_blockU_detActivityBg_recentred (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L 1) νS (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L 1) νS (k + 1) 1 eps D')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (z' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hzz : rootAct (Equiv.addRight tB) z' = bc (rootAct (Equiv.addRight tA) z)) {rc r : ℕ}
    (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) (rootAct (Equiv.addRight tA) z))
    (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ r)
    (hroot : ∀ x ∈ rootSet m₀ z, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hY : cubeAct (Equiv.addRight tB) Y' =
      (cubeAct (Equiv.addRight tA) Y).image (cubeMap hN hN' le_rfl))
    (hYr : ∀ x ∈ sitesOf Y, InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
    (hn : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * r + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (r + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnH : 2 * (r + 2 * (L * aK)) + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnH' : 2 * (r + 2 * (L * aK)) + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hraw : RawBoxAgree {z | InBox d (r + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (symRaw (Equiv.addRight tA) (rawOf D)) (symRaw (Equiv.addRight tB) (rawOf D'))) :
    ∑ y' ∈ (Finset.univ.filter fun u : unitPts (GB) =>
        unitBlock1 (u : UnitTorus d L N₁' m₁ k) = z'),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) D' y' Y' =
      ∑ y ∈ (Finset.univ.filter fun u : unitPts (GA) =>
        unitBlock1 (u : UnitTorus d L N₁ m₁ k) = z),
        detActivityBg m₀ (compWeight L 1) 1 νS (rho4 d L N BG κ) D y Y := by
  obtain ⟨SSA, hA⟩ := sum_detActivityBg_sym_genSymm (m₀ := m₀) (SA) (SA).hG' hN
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  obtain ⟨SSB, hB⟩ := sum_detActivityBg_sym_genSymm (m₀ := m₀) (SB) (SB).hG' hN'
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tB htB)
  have hσA := genSymm_mem_pavingSymGroup
    (Balaban.Localization.DecEquiv.GenSymm.translate (n := k + 1) (m₀ := m₀) tA htA)
  have hrootA : ∀ x ∈ rootSet m₀ (rootAct (Equiv.addRight tA) z),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rw [rootSet_rootAct hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    exact hroot x hx
  have hYA : ∀ x ∈ sitesOf (cubeAct (Equiv.addRight tA) Y),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rw [sitesOf_cubeAct hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    exact hYr x hx
  have hmain := sum_blockU_detActivityBg_twoTorus hN hN' hC hC' hk hδc hcap hsm hmar hαK hconn
    hconn' (xiCData_sym SSA hD) (xiCData_sym SSB hD') (rootAct (Equiv.addRight tA) z) hz hrc
    hrootA (cubeAct (Equiv.addRight tA) Y) hYA hn hn' hnS hnS' hnH hnH' hraw
  have e1 := hA (rho4 d L N BG κ) D z Y
  have e2 := hB (rho4 d L N BG κ) D' z' Y'
  rw [hzz, hY] at e2
  exact e2.symm.trans (hmain.trans e1)

end DetSum

end Balaban.Polymer.TwoTorusStep
