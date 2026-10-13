/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusSY
public import Balaban.Polymer.TwoTorusCubeOps
public import Balaban.Localization.Decoupled2FpLocal
public import Balaban.Localization.RowsFl
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fluctuation block set on two tori

For the cover `C = coverOf (levelGS (j+1))` and the operator lattice `H = levelGS j` (the mixed
pair of a step), on two tori identified on a centred box by `boxMap`, this file shows that the
objects of the fluctuation comparison correspond: the rows of the potential-free operator
(`row_support_levelGS`, `rowSet_image`), the footprints (`footprint_image`), the eligibility and
liveness of centres (`eligC_boxMap_iff`, `liveI_boxMap_iff`), the centres `Z_Y^F` and the block set
`S_Y^F` (`ZYF_image`, `SYF_image`), the row sets `RowF` (`RowF_image`), and the collar of `H`
(`collar_levelGS`, empty).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Balaban.Localization.Dec2
  Balaban.Localization.Dec2.RowsFl

section Rows

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

omit [NeZero N₁'] in
/-- **The rows of the potential-free operator of `levelGS j` are local.**  If the entry
`H_D(0) b y` is nonzero and `b` lies in the box of radius `r`, then `y` lies in the box of radius
`r + L^j`.  Margin: `2 (r + L^j) + 1 < N₁ L^m₁ L^K`. -/
theorem row_support_levelGS (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ) {r : ℕ}
    (hn : 2 * (r + L ^ j) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (b y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1)
    (hb : InBox d r ((N₁ * L ^ m₁) * L ^ K) (b : CTorus d L N₁ m₁ K))
    (h : dirichletOperator (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      a ν 0 b y ≠ 0) :
    InBox d (r + L ^ j) ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K) := by
  have hp : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  by_contra hy
  apply h
  unfold dirichletOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply,
    Pi.zero_apply, ite_self, add_zero]
  have hne : (b : CTorus d L N₁ m₁ K) ≠ y := fun h' => hy (h' ▸ inBox_mono (by omega) hb)
  have h1 : ∀ μ : Fin d, (y : CTorus d L N₁ m₁ K) ≠ (b : CTorus d L N₁ m₁ K) + Pi.single μ 1 := fun μ h' =>
    hy (h' ▸ inBox_mono (by omega) (inBox_add_single (by omega) hb μ))
  have h2 : ∀ μ : Fin d, (b : CTorus d L N₁ m₁ K) ≠ (y : CTorus d L N₁ m₁ K) + Pi.single μ 1 := fun μ h' => by
    apply hy
    have : (y : CTorus d L N₁ m₁ K) = (b : CTorus d L N₁ m₁ K) - Pi.single μ 1 := by rw [h']; abel
    rw [this]
    exact inBox_mono (by omega) (inBox_sub_single (by omega) hb μ)
  have h3 : jBlock d L (N₁ * L ^ m₁) K j (b : CTorus d L N₁ m₁ K) ≠
      jBlock d L (N₁ * L ^ m₁) K j (y : CTorus d L N₁ m₁ K) := fun h' => by
    have hbx := (jBlock_eq_iff_mem_box hj (y : CTorus d L N₁ m₁ K) (b : CTorus d L N₁ m₁ K)).1 h'.symm
    exact hy (inBox_of_mem_cell (by omega) hb hbx)
  have hfull : fullMatrix (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
      (b : CTorus d L N₁ m₁ K) y = 0 := by
    unfold fullMatrix
    rw [Matrix.add_apply, latticeLaplacian_apply, avgMatrix_levelGS_apply hj1 hj]
    simp [hne, h1, h2, h3]
  rw [hfull]
  simp

/-- **The operator rows of a set on two tori.**  For a set `S` of sites in the box of radius `r`,
the set of sites `x = b` or with `H_D(0) b x ≠ 0` for some `b ∈ S` on the first torus has as image
under `boxMap` the corresponding set of the image `bm '' S` on the second torus.  Margin
`2 (r + L^j) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem rowSet_image (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ) {r : ℕ}
    (hn : 2 * (r + L ^ j) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (r + L ^ j) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (S : Set (CTorus d L N₁ m₁ K)) (hS : ∀ b ∈ S, InBox d r ((N₁ * L ^ m₁) * L ^ K) b) :
    bm '' {x | ∃ b : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
        (b : CTorus d L N₁ m₁ K) ∈ S ∧ (x = (b : CTorus d L N₁ m₁ K) ∨
          ∃ y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
            dirichletOperator (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
              a ν 0 b y ≠ 0 ∧ x = (y : CTorus d L N₁ m₁ K))} =
      {x' | ∃ b' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
        (b' : CTorus d L N₁' m₁ K) ∈ bm '' S ∧ (x' = (b' : CTorus d L N₁' m₁ K) ∨
          ∃ y' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
            dirichletOperator (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
              a ν 0 b' y' ≠ 0 ∧ x' = (y' : CTorus d L N₁' m₁ K))} := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hp : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hα : ∀ x : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
      InBox d (r + L ^ j) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
        (0 : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ)
          ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ =
        (0 : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ) x :=
    fun _ _ => rfl
  have hent := fun x y hx hy => dirichletOperator_boxMap (N₁' := N₁') (ϱ := ϱ) (ρ := r + L ^ j) hj1 hj
    a ν (by omega) (by omega) hα x y hx hy
  ext x'
  constructor
  · rintro ⟨x, ⟨b, hbS, hx⟩, rfl⟩
    have hb := hS _ hbS
    refine ⟨⟨bm (b : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩, ⟨_, hbS, rfl⟩, ?_⟩
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact Or.inl rfl
    · have hyB := row_support_levelGS hj1 hj a ν (by omega) b y hb hy
      refine Or.inr ⟨⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩, ?_, rfl⟩
      rw [hent b y (inBox_mono (by omega) hb) hyB]
      exact hy
  · rintro ⟨b', ⟨b0, hb0S, hb0⟩, hx'⟩
    have hb := hS _ hb0S
    have hb' : b' = ⟨bm b0, levelGS_mem_Ω_one hj1 hj _⟩ := Subtype.ext hb0.symm
    subst hb'
    have hbB : InBox d r ((N₁' * L ^ m₁) * L ^ K) (bm b0) := inBox_boxMap (by omega) hb
    let B0 : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 :=
      ⟨b0, levelGS_mem_Ω_one hj1 hj _⟩
    rcases hx' with rfl | ⟨y', hy', rfl⟩
    · exact ⟨b0, ⟨B0, hb0S, Or.inl rfl⟩, rfl⟩
    · have hyB := row_support_levelGS (N₁ := N₁') hj1 hj a ν (by omega)
        ⟨bm b0, levelGS_mem_Ω_one hj1 hj _⟩ y' hbB hy'
      have hbb : bm (bm' (y' : CTorus d L N₁' m₁ K)) = y' := boxMap_boxMap (by omega) hyB
      have hyA : InBox d (r + L ^ j) ((N₁ * L ^ m₁) * L ^ K) (bm' (y' : CTorus d L N₁' m₁ K)) :=
        inBox_boxMap (by omega) hyB
      let Y0 : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 :=
        ⟨bm' (y' : CTorus d L N₁' m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
      refine ⟨bm' (y' : CTorus d L N₁' m₁ K), ⟨B0, hb0S, Or.inr ⟨Y0, ?_, rfl⟩⟩, hbb⟩
      have e := hent B0 Y0 (inBox_mono (by omega) hb) hyA
      have hsub : (⟨bm (Y0 : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ :
          (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1) = y' :=
        Subtype.ext hbb
      rw [hsub] at e
      rw [← e]
      exact hy'

omit [NeZero N₁'] in
/-- The collar of `levelGS j` is empty: `Ω₁` is the whole torus. -/
theorem collar_levelGS (hj1 : 1 ≤ j) (hj : j ≤ K) :
    collar (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  exact ((mem_collar _).1 hx).1 (levelGS_mem_Ω_one hj1 hj x)

omit [NeZero N₁'] in
/-- Every centre is live for `levelGS j`: its interaction cube contains its base point. -/
theorem liveI_levelGS (hj1 : 1 ≤ j) (hj : j ≤ K) (z : ℕ × CTorus d L N₁ m₁ K) :
    LiveI (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) z :=
  ⟨⟨z.2, levelGS_mem_Ω_one hj1 hj _⟩, base_mem_intBox z⟩

/-- Liveness of a centre and of its image (both always hold). -/
theorem liveI_boxMap_iff (hj1 : 1 ≤ j) (hj : j ≤ K) (z : ℕ × CTorus d L N₁ m₁ K) :
    LiveI (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (Prod.map id bm z) ↔
      LiveI (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) z :=
  iff_of_true (liveI_levelGS hj1 hj _) (liveI_levelGS hj1 hj _)

/-- **The footprint of a centre of the box lies in a box.**  For `z = (j', y0)` with `y0` in the
box of radius `ρ`, the footprint is inside the box of radius `ρ + 3 L^(j'+m₁) + L^j`. -/
theorem footprint_inBox (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ) {ρ j' : ℕ}
    (hn : 2 * (ρ + 3 * L ^ (j' + m₁) + L ^ j) + 1 < (N₁ * L ^ m₁) * L ^ K)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0)
    {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ footprint (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      a ν ((j', y0) : ℕ × CTorus d L N₁ m₁ K)) :
    InBox d (ρ + 3 * L ^ (j' + m₁) + L ^ j) ((N₁ * L ^ m₁) * L ^ K) x := by
  have hp : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  obtain ⟨b, hb, hx⟩ := hx
  have hbB := ((mem_intBox_iff hy0 (by omega)).1 hb).1
  rcases hx with rfl | ⟨y, hy, rfl⟩
  · exact inBox_mono (by omega) hbB
  · exact row_support_levelGS hj1 hj a ν hn b y hbB hy

/-- **T1 (`footprint_image`).**  For a centre `(j+1, y0)` of the cover of level `j+1`, with `y0` in
the box of radius `ρ`, the footprint of `H = levelGS j` of the image centre is the image of the
footprint.  Margin: `2 (ρ + 3 L^(j+1+m₁) + L^j) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem footprint_image (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ) {ρ : ℕ}
    (hn : 2 * (ρ + 3 * L ^ (j + 1 + m₁) + L ^ j) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + 3 * L ^ (j + 1 + m₁) + L ^ j) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    bm '' footprint (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K) =
      footprint (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) := by
  have hp : 1 ≤ L ^ j := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hI := intBox_image (N₁' := N₁') (j := j + 1) hy0 (by omega) (by omega)
  have h := rowSet_image (N₁' := N₁') (ϱ := ϱ) hj1 hj a ν (r := ρ + 3 * L ^ (j + 1 + m₁)) hn hn'
    (↑(intBox ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)))
    (fun b hb => ((mem_intBox_iff hy0 (by omega)).1 (Finset.mem_coe.1 hb)).1)
  rw [hI] at h
  exact h

omit [NeZero N₁'] in
/-- The set of rows `RowF` as a set. -/
theorem coe_RowF (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    (B : Finset (CTorus d L N₁ m₁ K)) :
    (↑(RowF (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν B) :
        Set (CTorus d L N₁ m₁ K)) =
      {x | ∃ b : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
        (b : CTorus d L N₁ m₁ K) ∈ (↑B : Set (CTorus d L N₁ m₁ K)) ∧
          (x = (b : CTorus d L N₁ m₁ K) ∨
          ∃ y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
            dirichletOperator (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
              a ν 0 b y ≠ 0 ∧ x = (y : CTorus d L N₁ m₁ K))} := by
  ext x
  simp [RowF]

/-- **T3 (`RowF_image`).**  The sites read by the rows of `H_D(0)` at the sites of a set `B` of the
box of radius `r`: `(RowF H a ν B).image bm = RowF H' a ν (B.image bm)`.  Margin
`2 (r + L^j) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem RowF_image (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ) {r : ℕ}
    (hn : 2 * (r + L ^ j) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (r + L ^ j) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {B : Finset (CTorus d L N₁ m₁ K)} (hB : ∀ x ∈ B, InBox d r ((N₁ * L ^ m₁) * L ^ K) x) :
    (RowF (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν B).image bm =
      RowF (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        (B.image bm) := by
  apply Finset.coe_injective
  rw [Finset.coe_image, coe_RowF hj, coe_RowF hj, Finset.coe_image]
  exact rowSet_image (N₁' := N₁') (ϱ := ϱ) hj1 hj a ν hn hn' _ (fun b hb => hB b hb)

section Cover

variable (hj1 : 1 ≤ j) (hj : j ≤ K) (hjK : j + 1 ≤ K)

local notation "GH" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GH'" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GC" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjK
local notation "GC'" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjK

variable {ρ : ℕ}

local notation "ρ₁" => ρ + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁)
local notation "cs" => L * cellSide L 0 m₁ (j + 1)
local notation "ρf" => ρ + 3 * L ^ (j + 1 + m₁) + L ^ j

include hj1 in
/-- **T1 (`eligC_boxMap_iff`).**  A centre `z` of the box of the cover of level `j+1` is eligible for
`(X₁, 𝒞)` iff its image is eligible for the images.  Margin
`2 ρ₁ + 5 L · cellSide L 0 m₁ (j+1) < N₁ L^m₁ L^K` (and for `N₁'`), with
`ρ₁ = ρ + (3 L^(j+1+m₁) + 3 L^(j+1+2)) + L^(j+1+m₁)`. -/
theorem eligC_boxMap_iff
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx GC)
    (hz0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) z.2) :
    EligC (coverOf GC') (X₁.image bm) (𝒞.image (Prod.map id bm)) (Prod.map id bm z) ↔
      EligC (coverOf GC) X₁ 𝒞 z := by
  have hj1' : 1 ≤ j + 1 := by omega
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (j + 1)
  have hzB : Prod.map id bm z ∈ cubeIdx GC' := by
    have hf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁)
      (K := K) (ρ := ρ₁) (ϱ := ϱ) hj1' hjK (by omega) (by omega)
    have : Prod.map id bm z ∈ (cubeIdx GC').filter
        (fun q => InBox d (ρ₁) ((N₁' * L ^ m₁) * L ^ K) q.2) := by
      rw [hf]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hz, inBox_mono (by omega) hz0⟩)
    exact (Finset.mem_filter.1 this).1
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hjK hz
  have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 := hz0
  have hQ := qset_image (ϱ := ϱ) hj1' hjK hn hn' hz hz0
  have hbase : ∀ P ∈ Qset GC ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K),
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2 := by
    intro P hP
    obtain ⟨y1, rfl, -, hy1⟩ := qset_base_inBox (ϱ := ϱ) hjK (by omega) hy0 hP
    exact hy1
  unfold EligC
  have hq : (∀ P' ∈ (coverOf GC').Qset (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)),
      P' ∈ (coverOf GC').parCubes (X₁.image bm) → P' ∈ 𝒞.image (Prod.map id bm)) ↔
      ∀ P ∈ (coverOf GC).Qset ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K),
        P ∈ (coverOf GC).parCubes X₁ → P ∈ 𝒞 := by
    change (∀ P' ∈ Qset GC' (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)),
      P' ∈ parCubes GC' (X₁.image bm) → P' ∈ 𝒞.image (Prod.map id bm)) ↔
      ∀ P ∈ Qset GC ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K), P ∈ parCubes GC X₁ → P ∈ 𝒞
    rw [hQ]
    constructor
    · intro h P hP hPp
      have hPc := Balaban.Localization.Qset_subset_cubeIdx _ hP
      exact (map_mem_image_iff (j := j + 1) hn' hC (hbase P hP)).1
        (h _ (Finset.mem_image_of_mem _ hP)
          ((map_mem_parCubes_iff hj1' hjK hn hn' hX hPc (hbase P hP)).2 hPp))
    · intro h P' hP' hPp
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
      have hPc := Balaban.Localization.Qset_subset_cubeIdx _ hP
      exact (map_mem_image_iff (j := j + 1) hn' hC (hbase P hP)).2
        (h P hP ((map_mem_parCubes_iff hj1' hjK hn hn' hX hPc (hbase P hP)).1 hPp))
  exact ⟨fun h => ⟨hz, hq.1 h.2⟩, fun h => ⟨hzB, hq.2 h.2⟩⟩

include hj1 in
/-- The footprint condition of `Z_Y^F` on two tori: the footprint of the image centre lies in the
image of `Y` iff the footprint of the centre lies in `Y`. -/
theorem footprint_subset_iff (a : ℕ → ℝ) (ν : ℝ)
    (hf : 2 * (ρf) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hf' : 2 * (ρf) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {Y : Finset (CTorus d L N₁ m₁ K)} (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    (∀ x' ∈ footprint GH' a ν (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)),
        x' ∈ Y.image bm) ↔
      (∀ x ∈ footprint GH a ν ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K), x ∈ Y) := by
  have hfp := footprint_image (N₁' := N₁') (ϱ := ϱ) hj1 hj a ν hf hf' hy0
  constructor
  · intro h x hx
    have hxb := footprint_inBox hj1 hj a ν (j' := j + 1) (by omega) hy0 hx
    have hx' : bm x ∈ footprint GH' a ν (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) := by
      rw [← hfp]; exact ⟨x, hx, rfl⟩
    obtain ⟨x0, hx0, hxe⟩ := Finset.mem_image.1 (h _ hx')
    have := boxMap_inj (hm' := (by omega : 2 * (ρf) + 1 < (N₁' * L ^ m₁) * L ^ K))
      (inBox_mono (by omega) (hY x0 hx0)) hxb hxe
    exact this ▸ hx0
  · intro h x' hx'
    rw [← hfp] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    exact Finset.mem_image_of_mem _ (h x hx)

include hj1 hjK in
/-- **The centres `Z_Y^F` correspond (pointwise).**  For a centre `z` of the cover of level `j+1`
with base point in the box of radius `ρ`, `z ∈ Z_Y^F` iff the image centre lies in `Z^F_{Y'}` of the
images `X₁' = bm '' X₁`, `𝒞' = Prod.map id bm '' 𝒞`, `Y' = bm '' Y`. -/
theorem map_mem_ZYF_iff (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    (hf : 2 * (ρf) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hf' : 2 * (ρf) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {Y : Finset (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx GC)
    (hz0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) z.2) :
    Prod.map id bm z ∈ ZYF (coverOf GC') GH' a ν (X₁.image bm) (𝒞.image (Prod.map id bm))
        (Y.image bm) ↔
      z ∈ ZYF (coverOf GC) GH a ν X₁ 𝒞 Y := by
  have hj1' : 1 ≤ j + 1 := by omega
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (j + 1)
  have hE := eligC_boxMap_iff (N₁' := N₁') (ϱ := ϱ) hj1 hjK hn hn' hX hC hz hz0
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hjK hz
  have hfs := footprint_subset_iff (N₁' := N₁') (ϱ := ϱ) hj1 hj a ν hf hf' hY hz0
  unfold ZYF
  rw [Finset.mem_filter, Finset.mem_filter]
  have hl := liveI_levelGS (N₁ := N₁) (ϱ := ϱ) hj1 hj ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)
  have hl' := liveI_levelGS (N₁ := N₁') (ϱ := ϱ) hj1 hj
    (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K))
  constructor
  · rintro ⟨-, he, -, hfp⟩
    exact ⟨hz, hE.1 he, hl, hfs.1 hfp⟩
  · rintro ⟨-, he, -, hfp⟩
    exact ⟨(hE.2 he).1, hE.2 he, hl', hfs.2 hfp⟩

include hj1 hjK in
/-- **T2 (`ZYF_image`).**  The centres `Z^F_{Y'}` of the images `X₁' = bm '' X₁`,
`𝒞' = Prod.map id bm '' 𝒞`, `Y' = bm '' Y` are the images of the centres `Z^F_Y`, for the cover
`coverOf (levelGS (j+1))` and `H = levelGS j`.  Margins, with
`ρ₁ = ρ + (3 L^(j+1+m₁) + 3 L^(j+1+2)) + L^(j+1+m₁)` and `ρf = ρ + 3 L^(j+1+m₁) + L^j`:
`2 ρ₁ + 5 L · cellSide L 0 m₁ (j+1) < N₁ L^m₁ L^K` and
`2 ρf + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem ZYF_image (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    (hf : 2 * (ρf) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hf' : 2 * (ρf) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {Y : Finset (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    ZYF (coverOf GC') GH' a ν (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm) =
      (ZYF (coverOf GC) GH a ν X₁ 𝒞 Y).image (Prod.map id bm) := by
  have hj1' : 1 ≤ j + 1 := by omega
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (j + 1)
  have hcf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁)
    (K := K) (ρ := ρ) (ϱ := ϱ) hj1' hjK (by omega) (by omega)
  ext z'
  constructor
  · intro hz'
    have hzc : z' ∈ cubeIdx GC' := (Finset.mem_filter.1 hz').1
    have hfp := (Finset.mem_filter.1 hz').2.2.2
    have hbase : z'.2 ∈ Y.image bm := hfp z'.2
      (mem_footprint_self (b := ⟨z'.2, levelGS_mem_Ω_one hj1 hj _⟩) (base_mem_intBox z'))
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hbase
    have hb : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) z'.2 := by
      rw [← hxe]; exact inBox_boxMap (by omega) (hY x hx)
    have hmem : z' ∈ (cubeIdx GC').filter
        (fun q => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2) :=
      Finset.mem_filter.2 ⟨hzc, hb⟩
    rw [hcf] at hmem
    obtain ⟨z, hzm, rfl⟩ := Finset.mem_image.1 hmem
    obtain ⟨hzcc, hz0⟩ := Finset.mem_filter.1 hzm
    exact Finset.mem_image.2 ⟨z, (map_mem_ZYF_iff (N₁' := N₁') (ϱ := ϱ) hj1 hj hjK a ν hn hn' hf hf'
      hX hC hY hzcc hz0).1 hz', rfl⟩
  · intro hz'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    have hfp := (Finset.mem_filter.1 hz).2.2.2
    have hbase : z.2 ∈ Y := hfp z.2
      (mem_footprint_self (b := ⟨z.2, levelGS_mem_Ω_one hj1 hj _⟩) (base_mem_intBox z))
    exact (map_mem_ZYF_iff (N₁' := N₁') (ϱ := ϱ) hj1 hj hjK a ν hn hn' hf hf' hX hC hY
      (Finset.mem_filter.1 hz).1 (hY _ hbase)).2 hz

include hj1 hjK in
/-- **T2 (`SYF_image`).**  The block set `S^F_Y` of the images is the image of `S^F_Y`:
`(SYF C H a ν X₁ 𝒞 Y).image bm = SYF C' H' a ν (X₁.image bm) (𝒞.image (Prod.map id bm))
(Y.image bm)`, for `C = coverOf (levelGS (j+1))`, `H = levelGS j`, and `X₁`, the base points of `𝒞`
and `Y` in the box of radius `ρ`.  Margins as in `ZYF_image`. -/
theorem SYF_image (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    (hf : 2 * (ρf) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hf' : 2 * (ρf) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {Y : Finset (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    (SYF (coverOf GC) GH a ν X₁ 𝒞 Y).image bm =
      SYF (coverOf GC') GH' a ν (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (j + 1)
  unfold SYF
  rw [ZYF_image (N₁' := N₁') (ϱ := ϱ) hj1 hj hjK a ν hn hn' hf hf' hX hC hY, Finset.biUnion_image,
    Finset.image_biUnion]
  refine Finset.biUnion_congr rfl fun z hz => ?_
  have hzc := (Finset.mem_filter.1 hz).1
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hjK hzc
  have hfp := (Finset.mem_filter.1 hz).2.2.2
  have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 := hY _ (hfp _
    (mem_footprint_self (b := ⟨y0, levelGS_mem_Ω_one hj1 hj _⟩) (base_mem_intBox _)))
  apply Finset.coe_injective
  rw [Finset.coe_image]
  exact (intBox_image (N₁' := N₁') (ρ₀ := ρ) (j := j + 1) hy0 (by omega) (by omega))

end Cover

end Rows

end Balaban.Polymer.TwoTorusStep
