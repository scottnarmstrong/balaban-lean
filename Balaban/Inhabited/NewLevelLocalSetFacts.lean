/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairCast
public import Balaban.Fluctuation.MarkedTwoMarkLocal
public import Balaban.Fluctuation.BgTransport

/-!
# The margins of a label polymer in its local generating set

Route R-LOC, L5: the facts of the polymer `T` and its cast local set
`𝔹 = castG hc (𝔹_{k+1}(Yp))` built on the collar `Yp` of a set `Y ⊇ sitesOf T` (the collar of
width `2 L^{k+1+m₁'}`, `hYp`) read by the clauses of the recomputed family.

* `fineBlock_subset_box_rootCube`: the fine block of a root lies in the box of its root cube;
* `castLocal_margin`: every site within sup-distance `r ≤ 2 L^{k+1+m₁'}` of `sitesOf T` lies in the
  top layer of `𝔹` (the label margin at `r = 2 L^{k+1+m₁}`, the deep margin of the determinant
  part at `r = 8 L^{k+1+m₁}`);
* `castLocal_labelMargin`: `LabelMargin 𝔹 (sitesOf T)`;
* `blockU_mem_unitPts_of_margin`: the unit points of the block of a root whose root cube lies in
  `T` are unit points of a generating set in whose top layer the sites of `T` lie.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.GsSpec Balaban.LargeField Finset

section Root

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- **The fine block of a root lies in the box of its root cube.** -/
theorem fineBlock_subset_box_rootCube (z : RootIdx d L N₁ m₁ (k + 1)) :
    fineBlock z ⊆ Localization.box (rootCube (m₀ := 1) z).1 (cellSide L 1 m₁ (k + 1)) := by
  intro x hx
  have hb : blockBase (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1) x = rootSite z := by
    rw [← rootSite_blockIndex, show blockIndex x = z from hx]
  have h1 : SameCell (L ^ (k + 1)) x (rootSite z) :=
    (sameCell_iff_cbase_eq (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)).2
      (hb.trans (blockBase_rootSite z).symm)
  have h2 : SameCell (L ^ (k + 1 + 1 + m₁)) x (rootSite z) :=
    SameCell.mono (pow_dvd_pow L (by omega)) h1
  exact mem_box_cbase_of_sameCell (cellSide_pos (L := L) 1 m₁ (k + 1)) h2

end Root

section Margin

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ : ℝ}

/-- **The margin of `sitesOf T` in its cast local set**: for `sitesOf T ⊆ Y` and `Yp` the collar of
`Y` on the torus `(N₁', m₁')` of width `2 L^{k+1+m₁'}`, every site within sup-distance
`r ≤ 2 L^{k+1+m₁'}` of a site of `T` lies in the top layer of `castG hc (𝔹_{k+1}(Yp))`. -/
theorem castLocal_margin (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hTY : sitesOf T ⊆ Y)
    {Yp' : Set (CTorus d L N₁' m₁' (k + 1))}
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ {x' : CTorus d L N₁' m₁' (k + 1) |
        (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y}, ∃ y : CTorus d L N₁' m₁' (k + 1),
      fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁'))
    {r : ℕ} (hr : r ≤ 2 * L ^ (k + 1 + m₁')) :
    ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ r →
      y ∈ (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)).Ω (k + 1) := by
  classical
  intro x hx y hxy
  refine castG_localB_collar_margin_le hc (le_refl (k + 1)) (Y := Y)
    (Y' := {x' : CTorus d L N₁' m₁' (k + 1) | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y})
    hsep (fun _ => Iff.rfl) hYp' (R := Finset.univ.filter (· ∈ sitesOf T))
    (fun x hx => hTY (Finset.mem_filter.1 hx).2) hr x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)
    y hxy

/-- **The label margin of `sitesOf T` in its cast local set** (`m₁ ≤ m₁'`). -/
theorem castLocal_labelMargin (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁')
    (hsep : ϱ ≤ minSep L (L ^ m₁'))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hTY : sitesOf T ⊆ Y)
    {Yp' : Set (CTorus d L N₁' m₁' (k + 1))}
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ {x' : CTorus d L N₁' m₁' (k + 1) |
        (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y}, ∃ y : CTorus d L N₁' m₁' (k + 1),
      fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁')) :
    LabelMargin (castG hc (localB (k + 1) (le_refl (k + 1)) Yp' hsep)) (sitesOf T) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact castLocal_margin hc hsep hTY hYp'
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hL (by omega)))

end Margin

section Units

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}

/-- **The unit points of the block of a root inside the top layer**: if the root cube of `z` lies in
`T` and the sites of `T` lie in the top layer of `Gb`, the unit points of the block of `z` are unit
points of `Gb` (the hypothesis `hZp` of `newLevelDetBg_castG_canon`). -/
theorem blockU_mem_unitPts_of_margin (S : StepSetting d L N₁ m₁ k N ϱ)
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} (z : RootIdx d L N₁ m₁ (k + 1))
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)}
    (hzT : rootCube (m₀ := 1) z ∈ T) (hTm : ∀ x ∈ sitesOf T, x ∈ Gb.Ω (k + 1)) :
    ∀ y ∈ S.blockU z, (y : UnitTorus d L N₁ m₁ k) ∈ unitPts Gb := by
  intro y hy
  obtain ⟨x, hx⟩ := exists_unitBlock_eq (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
    (y : UnitTorus d L N₁ m₁ k)
  have hxz : x ∈ fineBlock z := by
    refine (mem_fineBlock_iff_unitBlock1 (k := k)).2 ?_
    rw [hx]
    unfold StepSetting.blockU at hy
    exact (Finset.mem_filter.1 hy).2
  have hxT : x ∈ sitesOf T :=
    mem_sitesOf.2 ⟨rootCube (m₀ := 1) z, hzT, fineBlock_subset_box_rootCube z hxz⟩
  exact (mem_unitPts Gb).2 ⟨x, Gb.mem_layer.2 ⟨hTm x hxT, by simp [Gb.top]⟩, hx⟩

end Units

end Balaban.Inhabited
