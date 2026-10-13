/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsCoef

/-!
# The coefficient of the observable on two tori: the explicit labels of the first-order marks

The single-cube label of a cube `c` is now the explicit box `box c (L a_K)` of the aligned cube
`c` (`obsCubeLab`), not a choice among the one-cube labels containing `c`.  The first-order label of
the mark `(u, a)` is the single-cube label of its mark cube `S.cellOf m₀ u`.  On two tori, for
cubes of the box of radius `R`, the labels and their blocks correspond under `cubeMap`.

## Main statements

* `obsCubeLab_val`: the label of `c` is `box c (L a_K)`.
* `obsCubeLab_cubeMap`, `blocksOf_obsCubeLab_cubeMap`: the label of `cubeMap c` is the image of the
  label of `c` under the box map, and its blocks are the images of the blocks of the label of `c`.
* `cellOf_unitImage`: the mark cube of the image `ιu u` of a unit point is `cubeMap` of the mark
  cube of `u`.
* `blocksOf_obsY1_unitImage`: the transport of the first-order label blocks, the hypothesis
  `hκ1b` of `obsCoeffParam_blockSplit_twoTorus` for the labels `obsY1` of the first-order marks
  and the correspondence `(u, a) ↦ (ιu u, a)` of the marks.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory

/-! ### The single-cube labels on two tori -/

section CubeLabels

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L]

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L m₀ m₁ (k + 1)
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))

omit [NeZero N₁'] in
/-- The single-cube label of the aligned cube `c` is the box `box c (L a_K)`. -/
theorem obsCubeLab_val {m₀ : ℕ}
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) :
    (obsCubeLab m₀ c).1 = box c.1 (L * cellSide L m₀ m₁ (k + 1)) := rfl

/-- **The single-cube label of a cube of the box on two tori.**  If the label box `box c (L a_K)` of
the cube `c` lies in the box of radius `R`, the label of `cubeMap c` is the image of the label of
`c` under the box map.  Margin: `2 R + L a_K < N₁ L^m₁ L^(k+1)`. -/
theorem obsCubeLab_cubeMap {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    (hc : ∀ x ∈ box c.1 (L * aK), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    (obsCubeLab m₀ (σc c)).1 = bm '' (obsCubeLab m₀ c).1 := by
  rw [obsCubeLab_val, obsCubeLab_val, cubeMap_val,
    image_box_boxMap hn (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ _)) hc]

/-- **The blocks of the single-cube label of a cube of the box on two tori.**  If the label box of
`c` lies in the box of radius `R`, the blocks of the label of `cubeMap c` are the images under
`cubeMap` of the blocks of the label of `c` (`blocksOf_image_boxMap`).  Margin:
`2 R + L a_K < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem blocksOf_obsCubeLab_cubeMap {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    (c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ)
    (hc : ∀ x ∈ box c.1 (L * aK), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    blocksOf m₀ (k + 1) Set.univ (obsCubeLab m₀ (σc c)).1 =
      (blocksOf m₀ (k + 1) Set.univ (obsCubeLab m₀ c).1).image (σc) := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  rw [obsCubeLab_cubeMap hN hN' hn c hc]
  exact blocksOf_image_boxMap hN hN' (by omega) (by omega) hc

end CubeLabels

/-! ### The first-order labels of the marks of two steps -/

section MarkLabels

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
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
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ιu" b:max => (Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _) : (SB).U)

/-- **The mark cube of the image of a unit point.**  For the steps `hatStepKG` on `N₁` and `N₁'`
and a unit point `u` of the first torus whose mark cube `S.cellOf m₀ u` lies in the box of radius
`R`, the mark cube of the image `ιu u = bU u` is `cubeMap` of the mark cube of `u`.  Margins:
`2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 R + a_K < N₁ L^m₁ L^(k+1)`. -/
theorem cellOf_unitImage (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnc : 2 * R + aK < (N₁ * L ^ m₁) * L ^ (k + 1)) (u : (SA).U)
    (hu : ∀ x ∈ box ((SA).cellOf m₀ u).1 aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    (SB).cellOf m₀ (ιu u) = σc ((SA).cellOf m₀ u) := by
  obtain ⟨x, hxu, hxb⟩ := exists_site_of_unitPt (SA) m₀ u
  have hxR : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := hu x hxb
  have hux : unitPt (SA).hG' x = u := Subtype.ext hxu
  have hu' : (ιu u) = unitPt (SB).hG' (bm x) := by
    apply Subtype.ext
    show bU (u : UnitTorus d L N₁ m₁ k) = unitBlock (bm x)
    rw [← hxu, unitBlock_boxMap hn hxR]
  have hcA : (SA).cellOf m₀ u = cubeOfSite m₀ x := by
    rw [← hux]; exact (SA).cellOf_unitPt m₀ x
  rw [hu', (SB).cellOf_unitPt m₀ (bm x), hcA]
  apply Subtype.ext
  rw [cubeMap_val]
  show cbase aK (bm x) = bm (cbase aK x)
  have hbox : ∀ y ∈ box (cbase aK x) aK, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y := by
    intro y hy
    refine hu y ?_
    rw [hcA]
    exact hy
  exact (cbase_boxMap (cellSide_dvd (K := k + 1) (m₁ := m₁) hN le_rfl)
    (cellSide_dvd (K := k + 1) (m₁ := m₁) hN' le_rfl) (cellSide_pos m₀ m₁ _) hnc x hbox).symm

/-- **D1: the transport of the first-order label blocks.**  For the steps `hatStepKG` on `N₁` and
`N₁'`, label systems `Lab₀`, `Lab₀'` of activity labels, domain families `𝒴`, `𝒴'`, and a mark
`(u, a)` of the first torus whose label box `box c (L a_K)` (`c` the mark cube of `u`) lies in the
box of radius `R`: the blocks of the first-order label of the mark `(ιu u, a)` of the second step
are the images under `cubeMap` of the blocks of the first-order label of `(u, a)`.  This is the
hypothesis `hκ1b` of `obsCoeffParam_blockSplit_twoTorus` for the labels `obsY1` and the
correspondence `(u, a) ↦ (ιu u, a)`.  Margins: `2 R + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and
`2 R + L a_K < N₁ L^m₁ L^(k+1), N₁′ L^m₁ L^(k+1)`. -/
theorem blocksOf_obsY1_unitImage (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {m₀ R : ℕ}
    (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hn : 2 * R + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL : 2 * R + L * aK < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnL' : 2 * R + L * aK < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Lb₀ Lb₀' : Type}
    (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀)
    (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ Lb₀')
    {𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (hdj : ∀ Y ∈ 𝒴, IsDj m₀ (k + 1) Y) (hdj' : ∀ Y ∈ 𝒴', IsDj m₀ (k + 1) Y)
    (i : ObsMarkIdx (SA))
    (hi : ∀ x ∈ box ((SA).cellOf m₀ i.1).1 (L * aK),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    blocksOf m₀ (k + 1) Set.univ
        ((obsLab Lab₀' hdj').ysite (obsY1 m₀ (SB) Lb₀' 𝒴' ((ιu i.1), i.2))) =
      (blocksOf m₀ (k + 1) Set.univ ((obsLab Lab₀ hdj).ysite (obsY1 m₀ (SA) Lb₀ 𝒴 i))).image
        (σc) := by
  have hcs : aK ≤ L * aK := cellSide_le_mul
  have hcell : (SB).cellOf m₀ (ιu i.1) = σc ((SA).cellOf m₀ i.1) :=
    cellOf_unitImage hN2 hk νS β p₁ δ hN hN' hn (by omega) i.1
      (fun x hx => hi x (box_mono _ hcs hx))
  show blocksOf m₀ (k + 1) Set.univ (obsCubeLab m₀ ((SB).cellOf m₀ (ιu i.1))).1 =
    (blocksOf m₀ (k + 1) Set.univ (obsCubeLab m₀ ((SA).cellOf m₀ i.1)).1).image (σc)
  rw [hcell]
  exact blocksOf_obsCubeLab_cubeMap hN hN' hnL hnL' _ hi

end MarkLabels

end Balaban.Polymer.TwoTorusStep
