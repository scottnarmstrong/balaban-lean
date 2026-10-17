/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusCoef
public import Balaban.Polymer.TwoTorusGapCloseSym
public import Balaban.Fluctuation.DetSymmGroup

/-!
# The determinant activities under the recentring map (item 24, blocker 7)

`detActivityBg_recentred`: the determinant activity of a unit point and a set of cubes on the first
torus equals the activity of the corresponding unit point and set of cubes on the second torus, where
the correspondence is the recentred map `x ↦ bm (x + tA) - tB` (the translations `tA`, `tB` by
multiples of the cell side).  The proof composes the covariance under the translations
(`detActivityBg_sym_genSymm`, `DetSymmGroup`) on each torus with the transport between the two tori on
the common box (`detActivityBg_image_twoTorus`), so that the supports need not lie near the origin.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Balaban.Multiscale Balaban.Background

section Det

open Balaban.Localization.DetUnitIncidence Balaban.Localization.DecEquiv

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱm ϱm' : ℝ} {m₀ : ℕ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)

/-- **The determinant activity under the recentring map** (item 24, part 2).  Let `tA`, `tB` be
translations of the two step tori by multiples of the cell side, `x₀` a site of the first torus and
`x₀'` a site of the second with `x₀' + tB = bm (x₀ + tA)`, `Y` a set of level-`(k+1)` cubes of the
first torus and `Y'` a set of cubes of the second torus whose translate by `tB` is the `cubeMap`-image
of the translate of `Y` by `tA`.  If the translated root cell and the translated sites of `Y` lie in
the box of radius `r` (margins as in `detActivityBg_image_twoTorus`) and the translated data agree on
the box, then `detActivityBg` of the data `D'` at the unit point of `x₀'` and `Y'` equals
`detActivityBg` of `D` at the unit point of `x₀` and `Y`. -/
theorem detActivityBg_recentred (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) Hm' a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
    (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hconn : HatConn (GA)) (hconn' : HatConn (GB))
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (tA : CTorus d L N₁ m₁ (k + 1)) (tB : CTorus d L N₁' m₁ (k + 1))
    (htA : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tA μ).val)
    (htB : ∀ μ, L ^ ((k + 1) + m₀ + m₁) ∣ (tB μ).val)
    (x₀ : CTorus d L N₁ m₁ (k + 1)) (x₀' : CTorus d L N₁' m₁ (k + 1))
    (hx₀ : x₀' + tB = bm (x₀ + tA))
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (Y' : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hY : cubeAct (Equiv.addRight tB) Y' =
      (cubeAct (Equiv.addRight tA) Y).image (cubeMap hN hN' le_rfl)) {r : ℕ}
    (hroot : ∀ x ∈ rootSet m₀ (rootIdxOf (unitPt hGA x₀)),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (x + tA))
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
    detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D' (unitPt hGB x₀') Y' =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D (unitPt hGA x₀) Y := by
  obtain ⟨SA, hUA, hA⟩ := detActivityBg_sym_genSymm (m₀ := m₀) (N := N) hGA hN
    (GenSymm.translate tA htA) (compWeight L a₁) a₁ ν
  obtain ⟨SB, hUB, hB⟩ := detActivityBg_sym_genSymm (m₀ := m₀) (N := N) hGB hN'
    (GenSymm.translate tB htB) (compWeight L a₁) a₁ ν
  have hσA := genSymm_mem_pavingSymGroup (m₀ := m₀) (GenSymm.translate tA htA)
  have hσB := genSymm_mem_pavingSymGroup (m₀ := m₀) (GenSymm.translate tB htB)
  have hyA : unitAct (GA) SA hUA (unitPt hGA x₀) = unitPt hGA (x₀ + tA) :=
    unitPt_sym hGA SA hUA x₀
  have hyB : unitAct (GB) SB hUB (unitPt hGB x₀') = unitPt hGB (x₀' + tB) :=
    unitPt_sym hGB SB hUB x₀'
  have hroot0 : ∀ x ∈ rootSet m₀ (rootIdxOf (unitPt hGA x₀)), InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1))
      (x + tA) := hroot
  have hx₀R : InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) (x₀ + tA) :=
    hroot0 x₀ (by rw [rootIdxOf_eq (y := unitPt hGA x₀) rfl]; exact mem_rootSet_blockIndex x₀)
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hn1 : 2 * r + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hι : (ιu (unitAct (GA) SA hUA (unitPt hGA x₀))) = unitAct (GB) SB hUB (unitPt hGB x₀') := by
    apply Subtype.ext
    rw [hyA, hyB]
    show bU ((unitPt hGA (x₀ + tA) : unitPts (GA)) : UnitTorus d L N₁ m₁ k) =
      ((unitPt hGB (x₀' + tB) : unitPts (GB)) : UnitTorus d L N₁' m₁ k)
    have := unitImage_val (N₁' := N₁') hn1 (unitPt hGA (x₀ + tA)) (y := x₀ + tA) rfl hx₀R
    rw [hx₀]
    exact this
  have hrootA : ∀ x ∈ rootSet m₀ (rootIdxOf (unitAct (GA) SA hUA (unitPt hGA x₀))),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rw [rootIdxOf_unitAct SA hUA hσA, rootSet_rootAct hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    exact hroot0 x hx
  have hYA : ∀ x ∈ sitesOf (cubeAct (Equiv.addRight tA) Y),
      InBox d r ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    rw [sitesOf_cubeAct hN hσA]
    rintro _ ⟨x, hx, rfl⟩
    exact hYr x hx
  have hmain := detActivityBg_image_twoTorus hN hN' hC hC' hk hδc hcap hsm hmar hαK hconn hconn'
    (xiCData_sym SA hD) (xiCData_sym SB hD') (unitAct (GA) SA hUA (unitPt hGA x₀))
    (cubeAct (Equiv.addRight tA) Y) hrootA hYA hn hn' hnS hnS' hnH hnH' hraw
  rw [hι, ← hY] at hmain
  rw [← hB (rho4 d L N BG κ) D' (unitPt hGB x₀') Y', hmain, hA (rho4 d L N BG κ) D (unitPt hGA x₀) Y]

end Det

end Balaban.Polymer.TwoTorusStep
