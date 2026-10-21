/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonBox
public import Balaban.Fluctuation.LevelLocalCover

/-!
# The union of the `π_{k+1}`-cells of a set of sites

For a set `P` of sites of the step torus, `cellUnion m₀ P` is the union of the `π_{k+1}`-cells (aligned
boxes of side `cellSide L m₀ m₁ (k + 1)`) of its sites.  A block of any generating set (side
`L ^ n`, `n ≤ k + 1`) lies in one cell, so `cellUnion m₀ P` is closed under the blocks.  When the
region `X₁` contains the neighbourhood `nbhd m₀ x` of the cell of every site `x` of `P`, the union has
the block margin against `X₁` (`blockMargin_cellUnion`, from the landed `LocalCover.blockMargin`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LocalCover

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The union of the cells of a set of sites.** -/
def cellUnion (m₀ : ℕ) (P : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {z | ∃ x ∈ P, z ∈ box (corner m₀ x) (cellSide L m₀ m₁ (k + 1))}

theorem subset_cellUnion (m₀ : ℕ) (P : Set (CTorus d L N₁ m₁ (k + 1))) :
    P ⊆ cellUnion m₀ P := fun x hx => ⟨x, hx, mem_cell m₀ x⟩

omit [NeZero L] [NeZero N₁] in
theorem cellUnion_mono (m₀ : ℕ) {P Q : Set (CTorus d L N₁ m₁ (k + 1))} (h : P ⊆ Q) :
    cellUnion m₀ P ⊆ cellUnion m₀ Q := fun _ ⟨x, hx, hz⟩ => ⟨x, h hx, hz⟩

omit [NeZero N₁] in
/-- The union of the cells lies in a set containing the neighbourhood of the cell of each site. -/
theorem cellUnion_subset (m₀ : ℕ) {P S : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : ∀ x ∈ P, nbhd m₀ x ⊆ S) : cellUnion m₀ P ⊆ S := by
  rintro z ⟨x, hx, hz⟩
  exact h x hx (cell_subset_cellNbhd (Nat.pos_of_ne_zero (NeZero.ne L)) _ _ hz)

/-- **Blocks lie in one cell**: the `n`-block of a site of the union of cells (`n ≤ k + 1`) lies in the
union. -/
theorem blk_subset_cellUnion {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) {P : Set (CTorus d L N₁ m₁ (k + 1))}
    {ϱ' : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') {n : ℕ} (hn : n ≤ k + 1)
    {z y : CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ cellUnion m₀ P) (hy : y ∈ G.blk n z) :
    y ∈ cellUnion m₀ P := by
  obtain ⟨x, hx, hzx⟩ := hz
  have hsc : SameCell (L ^ n) y z := sameCell_of_jBlock_eq hn (GeneratingSet.mem_blk.1 hy)
  have hsc' : SameCell (cellSide L m₀ m₁ (k + 1)) y z :=
    SameCell.mono (pow_dvd_pow L (by omega)) hsc
  have h1 := (sameCell_iff_cbase_eq (cellSide_pos (L := L) m₀ m₁ (k + 1))).1 hsc'
  have hdv := cellSide_dvd (L := L) (m₁ := m₁) (K := k + 1) hN (le_refl (k + 1))
  have h2 : cbase (cellSide L m₀ m₁ (k + 1)) z = corner m₀ x :=
    cbase_eq_of_mem_box hdv (aligned_corner m₀ x) hzx
  refine ⟨x, hx, ?_⟩
  have h3 := mem_box_cbase (cellSide_pos (L := L) m₀ m₁ (k + 1)) y
  rwa [h1, h2] at h3

/-- The block margin is monotone in the region. -/
theorem BlockMargin.mono {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {X X' : Finset (CTorus d L N₁ m₁ (k + 1))} {Zα : Set (CTorus d L N₁ m₁ (k + 1))}
    (hXX : X ⊆ X') (h : BlockMargin Gp X Zα) : BlockMargin Gp X' Zα := by
  classical
  intro x hx hxΩ
  obtain ⟨q, hq, hqi, hP, hS⟩ := h x hx hxΩ
  refine ⟨q, hq, hqi, fun P hPQ hpar => hP P hPQ ?_, fun y hy => hXX (hS y hy)⟩
  unfold DecCover.parCubes at hpar ⊢
  rw [Finset.mem_filter] at hpar ⊢
  exact ⟨hpar.1, fun hsub => hpar.2 (hsub.trans hXX)⟩

/-- **The union of the cells of the sites whose cell neighbourhoods lie in `X₁` has the block margin
against `X₁`.** -/
theorem blockMargin_cellUnion {a : ℕ → ℝ} {ν : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (S : DGSetting Gp a ν) (hG : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    {P : Set (CTorus d L N₁ m₁ (k + 1))} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hP : ∀ x ∈ P, nbhd m₀ x ⊆ ↑X₁) : BlockMargin Gp X₁ (cellUnion m₀ P) := by
  intro z hz hzΩ
  obtain ⟨x, hx, hzx⟩ := hz
  have h := blockMargin S hG hm₀ x (Zα := {z})
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hzx)
  refine (BlockMargin.mono (X := nbhdF m₀ x) (X' := X₁) (fun y hy => ?_) h) z rfl hzΩ
  rw [← Finset.mem_coe, coe_nbhdF] at hy
  exact hP x hx hy

/-- **The cell of a site at level `j ≤ k`, enlarged by half a side, lies in the neighbourhood of the
`π_{k+1}`-cell of the site.** -/
theorem cellBox_subset_nbhd (m₀ : ℕ) (hL : 2 ≤ L) {j : ℕ} (hj : j + 1 ≤ k + 1)
    (y₀ : CTorus d L N₁ m₁ (k + 1)) :
    box (cbase (cellSide L m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L m₀ m₁ j))
      (L * cellSide L m₀ m₁ j) ⊆ nbhd m₀ y₀ := by
  rintro z ⟨u, hu, rfl⟩
  have hLpos : 0 < L := by omega
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hac : L * a ≤ cellSide L m₀ m₁ (k + 1) := cellSide_succ_le hLpos hj m₀ m₁
  have hc : cellSide L m₀ m₁ (k + 1) ≤ (L - 1) * cellSide L m₀ m₁ (k + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hh : L / 2 * a + a ≤ L * a := by
    have : L / 2 + 1 ≤ L := by omega
    nlinarith
  have hx : y₀ ∈ box (corner m₀ y₀) (cellSide L m₀ m₁ (k + 1)) := mem_cell m₀ y₀
  have hb : ∀ μ, |(u μ : ℤ) - ((L / 2 * a : ℕ) : ℤ) - (((y₀ μ).val % a : ℕ) : ℤ)| ≤
      (((L - 1) * cellSide L m₀ m₁ (k + 1) : ℕ) : ℤ) := by
    intro μ
    have h1 := hu μ
    have h2 : (y₀ μ).val % a < a := Nat.mod_lt _ ha0
    have h3 := hac.trans hc
    generalize L * a = P at h1 hh h3
    generalize (L - 1) * cellSide L m₀ m₁ (k + 1) = Q at h3 ⊢
    generalize L / 2 * a = h at hh ⊢
    generalize (y₀ μ).val % a = r at h2 ⊢
    rw [abs_le]
    constructor <;> omega
  have key := add_intTorus_mem_cellNbhd (L := L) (c := cellSide L m₀ m₁ (k + 1)) (by omega) hx
    (fun μ => (u μ : ℤ) - ((L / 2 * a : ℕ) : ℤ) - (((y₀ μ).val % a : ℕ) : ℤ)) hb
  have e : cbase a y₀ - natT (fun _ => L / 2 * a) + natT u = y₀ + (intTorus fun μ =>
      (u μ : ℤ) - ((L / 2 * a : ℕ) : ℤ) - (((y₀ μ).val % a : ℕ) : ℤ) : CTorus d L N₁ m₁ (k + 1)) := by
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply, natT_apply, intTorus_apply, cbase_eq_sub,
      Int.cast_sub, Int.cast_natCast]
    ring
  rw [e]
  exact key

end Balaban.Inhabited
