/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDecBg
public import Balaban.Localization.RowsFl
public import Balaban.Localization.Decoupled2Solve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The decoupled fluctuation field on two tori

The fluctuation problem of the step is posed on the pair `(C, H)` with the cover
`C = coverOf (levelGS (j + 1))` (the cubes of level `j + 1`) and the operator generating set
`H = levelGS j` (the lattice of level `j`).  For two step tori `CTorus d L N₁ m₁ K` and
`CTorus d L N₁' m₁ K`, identified on a centred box by `boxMap`, this file compares the decoupled
fluctuation systems `Dec2.DecFixed` on a union `Y` of components of the incidence graph and its
block set `B_F = S_Y^F` (`Dec2.SYF`).

* `Gstar2_block`, `Kcal2_block` and their corollaries: the block identities `P G*_s = G*_s P` and
  `P 𝒦_s = 𝒦_s P` of `Decoupled2.lean` for the indicator `P` of a set `T` (one torus).
* `cubeH_boxMap_lvl`, `cubeG_boxMap_lvl`: the cube operator `cubeH` and the cube resolvent
  `cubeG = cubeH⁻¹ c_z` of the operator `levelGS j` at a centre `(i, y₀)` of any level `i` (here
  `i = j + 1`), for any covers containing the centre and its image (the landed `cubeG_boxMap` has
  `i = j` and the cover `cubeIdx (levelGS j)`).  What is new for the mixed pair is only that the
  cube of the centre has level `j + 1` while the cut operator, its cube cut and its invertibility
  are those of `levelGS j`; the latter come from the pair hypothesis `Dec2.CoverBase`.
* `chi_cover_boxMap`, `Kz2_boxMap`: the partition weights of the cover of level `j + 1` and the
  commutators `K_z = χ_z H_D - H_D χ_z` (with `H_D` of level `j`) correspond.
* `Gstar2_boxMap_apply`, `Kcal2_boxMap_apply`, `Gs2_boxMap_rows` and
  `decSol_green_rows_transport` (D1): the rows of `G*_s`, `𝒦_s` and of
  `G_s = G*_s (1 - 𝒦_s)⁻¹` on the component correspond under `boxMap`;
  `decSol_green_rows_SYF` is the form on the block set `S_Y^F` of a union of components of the
  incidence graph.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### The block identities of a pair `(C, H)` on one torus -/

section Dec2Block

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ}
  {ν Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- **The block identity for `G*_s` of a pair `(C, H)`.**  If every interaction cube with a
non-zero factor lies inside `T` or avoids it, then `P G*_s = G*_s P = ∑_{z inner} s_z χ_z G^{(z)} c_z`
for the indicator `P` of `T`. -/
theorem Gstar2_block (S : Dec2.CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    indY H T * Dec2.Gstar C H a ν α s =
        ∑ q ∈ Dec2.innerCentres C H T, C.sProd s q • (Dec2.chiD C H q * cubeG H a ν α q) ∧
      Dec2.Gstar C H a ν α s * indY H T =
        ∑ q ∈ Dec2.innerCentres C H T, C.sProd s q • (Dec2.chiD C H q * cubeG H a ν α q) := by
  have hM : ∀ q ∈ C.cubeIdx, RowSupp (Dec2.chiD C H q * cubeG H a ν α q) (intBox q) ∧
      Dec2.chiD C H q * cubeG H a ν α q * cD H q = Dec2.chiD C H q * cubeG H a ν α q :=
    fun q hq => ⟨Dec2.rowSupp_chi_cubeG S hα hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  obtain ⟨hin, hout⟩ := Dec2.blk_conditions (s := s) _ hM hdich
  exact Dec2.sum_block_facts _ hin hout

/-- **The block identity for `𝒦_s` of a pair `(C, H)`**:
`P 𝒦_s = 𝒦_s P = ∑_{z inner} s_z K_z G^{(z)} c_z`. -/
theorem Kcal2_block (S : Dec2.CoverBase C H a ν Kc Cx) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T) :
    indY H T * Dec2.Kcal C H a ν α s =
        ∑ q ∈ Dec2.innerCentres C H T, C.sProd s q • (Dec2.Kz C H a ν q * cubeG H a ν α q) ∧
      Dec2.Kcal C H a ν α s * indY H T =
        ∑ q ∈ Dec2.innerCentres C H T, C.sProd s q • (Dec2.Kz C H a ν q * cubeG H a ν α q) := by
  have hM : ∀ q ∈ C.cubeIdx, RowSupp (Dec2.Kz C H a ν q * cubeG H a ν α q) (intBox q) ∧
      Dec2.Kz C H a ν q * cubeG H a ν α q * cD H q = Dec2.Kz C H a ν q * cubeG H a ν α q :=
    fun q hq => ⟨Dec2.rowSupp_Kz_cubeG S hq, by rw [Matrix.mul_assoc, cubeG_mul_cD]⟩
  obtain ⟨hin, hout⟩ := Dec2.blk_conditions (s := s) _ hM hdich
  exact Dec2.sum_block_facts _ hin hout

theorem Kcal2_apply_eq_zero_of_mem (S : Dec2.CoverBase C H a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {x z : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∉ T) :
    Dec2.Kcal C H a ν α s x z = 0 := by
  obtain ⟨h1, h2⟩ := Kcal2_block (α := α) S hdich
  have h := congrFun (congrFun (h1.trans h2.symm) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

theorem Kcal2_apply_eq_zero_of_not_mem (S : Dec2.CoverBase C H a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {x z : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∉ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    Dec2.Kcal C H a ν α s x z = 0 := by
  obtain ⟨h1, h2⟩ := Kcal2_block (α := α) S hdich
  have h := congrFun (congrFun (h1.trans h2.symm) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_right hx, ite_eq_left hz] at h
  exact h.symm

theorem Gstar2_apply_eq_zero_of_mem (S : Dec2.CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {x z : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∉ T) :
    Dec2.Gstar C H a ν α s x z = 0 := by
  obtain ⟨h1, h2⟩ := Gstar2_block S hα hdich
  have h := congrFun (congrFun (h1.trans h2.symm) x) z
  rw [indY_mul_apply, mul_indY_apply, ite_eq_left hx, ite_eq_right hz] at h
  exact h

/-- The row at a site of `T` of `G*_s` is the sum over the cubes inside `T`. -/
theorem Gstar2_apply_of_mem (S : Dec2.CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    {T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {x : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (z : H.Ω 1) :
    Dec2.Gstar C H a ν α s x z =
      ∑ q ∈ Dec2.innerCentres C H T, C.sProd s q * (Dec2.chiD C H q * cubeG H a ν α q) x z := by
  have h := congrFun (congrFun (Gstar2_block S hα hdich).1 x) z
  rw [indY_mul_apply, ite_eq_left hx, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- The row at a site of `T` of `𝒦_s` is the sum over the cubes inside `T`. -/
theorem Kcal2_apply_of_mem (S : Dec2.CoverBase C H a ν Kc Cx) {T : Finset (CTorus d L N₁ m₁ K)}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    {x : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (z : H.Ω 1) :
    Dec2.Kcal C H a ν α s x z =
      ∑ q ∈ Dec2.innerCentres C H T, C.sProd s q * (Dec2.Kz C H a ν q * cubeG H a ν α q) x z := by
  have h := congrFun (congrFun (Kcal2_block (α := α) S hdich).1 x) z
  rw [indY_mul_apply, ite_eq_left hx, Matrix.sum_apply] at h
  rw [h]
  simp only [Matrix.smul_apply, smul_eq_mul]

/-- **Rows of `G_s(A) f` outside `T`.**  If every active interaction cube meets `Y` only inside
`T`, the rows of `G_s(A) f` on `Y \ T` vanish. -/
theorem Gs2_apply_eq_zero_of_not_mem (S : Dec2.CoverBase C H a ν Kc Cx) (hα : AdmPot H α)
    {Y T : Finset (CTorus d L N₁ m₁ K)} {s : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (f : H.Ω 1 → ℂ) {y : H.Ω 1} (hyY : (y : CTorus d L N₁ m₁ K) ∈ Y)
    (hyT : (y : CTorus d L N₁ m₁ K) ∉ T) : (Dec2.Gs C H a ν α s *ᵥ f) y = 0 := by
  unfold Dec2.Gs Dec2.Gstar
  rw [← Matrix.mulVec_mulVec, Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hs : C.sProd s q = 0
  · rw [hs, zero_mul]
  · have hyq : (y : CTorus d L N₁ m₁ K) ∉ intBox q := fun h => hyT (hrow q hq hs _ hyY h)
    rw [Dec2.rowSupp_chi_cubeG S hα hq _ y hyq, mul_zero]

end Dec2Block

/-! ### The cube operators of the mixed pair on two tori -/

section MixedCube

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱp : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K) (hjp : j + 1 ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "CA" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "CB" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- **The cube operator of a centre of any level.**  The entries of `cubeH` of the operator
`levelGS j` at the centre `(i, y0)`, `y0` in the box of radius `ρ₀`, at two sites of the box of
radius `ρ`, correspond (the landed `cubeH_boxMap` is the case `i = j`).  Margins, with
`R' = ρ + 2 + ρ₀ + 3 L^(i+m₁)`: `2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` and `2 R' + 1 < N₁ L^m₁ L^K` (and
for `N₁'`). -/
theorem cubeH_boxMap_lvl {i ρ ρ₀ : ℕ} (a : ℕ → ℝ) (ν : ℝ) {y0 : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hm : 2 * (ρ + 2 + (ρ₀ + 3 * L ^ (i + m₁))) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hm' : 2 * (ρ + 2 + (ρ₀ + 3 * L ^ (i + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ}
    (hα : ∀ x : (HA).Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
      α' (ιb x) = α x)
    (x y : (HA).Ω 1) (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    cubeH HB a ν α' (Prod.map id bm ((i, y0) : ℕ × CTorus d L N₁ m₁ K)) (ιb x) (ιb y) =
      cubeH HA a ν α ((i, y0) : ℕ × CTorus d L N₁ m₁ K) x y := by
  unfold cubeH
  refine cutOperator_boxMap hj1 hj a ν hn hn' (fun z hz μ => ?_) hα x y hx hy
  exact cubeCut_boxMap_iff (ρ := ρ) hj1 hj hn hn' (Λ' := intBox ((i, bm y0) :
    ℕ × CTorus d L N₁' m₁ K)) (fun w hw => mem_intBox_boxMap_iff_of_le (N₁' := N₁')
      (R' := ρ + 2 + (ρ₀ + 3 * L ^ (i + m₁))) hy0 (by omega) hm hm'
      (inBox_mono (by omega) hw)) (z := z) (inBox_mono (by omega) hz) μ

include hj1 in
/-- **The cube resolvent of a centre of any level (T3 for the mixed pair).**  Let `CA`, `CB` be
covers of the two tori with the pair hypotheses `Dec2.CoverBase` for the operator `levelGS j`,
containing the centre `(i, y0)` and its image.  Then the entries of the cube resolvent
`cubeG = cubeH⁻¹ c_z` of `levelGS j` at this centre correspond at two sites of the box of radius
`R = ρ₀ + 3 L^(i+m₁)`, for potentials with `α'(bm x) = α x` on that box.  The invertibility of
`cubeH`, the support of `cubeG` and the block alignment of the cube for `levelGS j` are the fields
of `Dec2.CoverBase`.  Margins: `2 R + 3 L^K + 5 < N₁ L^m₁ L^K` and `2 (R + 2 + R) + 1 < N₁ L^m₁ L^K`
(and for `N₁'`). -/
theorem cubeG_boxMap_lvl {i ρ₀ : ℕ} {a : ℕ → ℝ} {ν Kc Cx : ℝ} {CA' : DecCover d L N₁ m₁ K}
    {CB' : DecCover d L N₁' m₁ K}
    (SA : Dec2.CoverBase CA' HA a ν Kc Cx) (SB : Dec2.CoverBase CB' HB a ν Kc Cx)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hq : ((i, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ CA'.cubeIdx)
    (hq' : ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K) ∈ CB'.cubeIdx)
    (hn : 2 * (ρ₀ + 3 * L ^ (i + m₁)) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₀ + 3 * L ^ (i + m₁)) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hm : 2 * ((ρ₀ + 3 * L ^ (i + m₁)) + 2 + (ρ₀ + 3 * L ^ (i + m₁))) + 1 <
      (N₁ * L ^ m₁) * L ^ K)
    (hm' : 2 * ((ρ₀ + 3 * L ^ (i + m₁)) + 2 + (ρ₀ + 3 * L ^ (i + m₁))) + 1 <
      (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1,
      InBox d (ρ₀ + 3 * L ^ (i + m₁)) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
        α' (ιb x) = α x)
    (x y : (HA).Ω 1)
    (hx : InBox d (ρ₀ + 3 * L ^ (i + m₁)) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d (ρ₀ + 3 * L ^ (i + m₁)) ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    cubeG HB a ν α' (Prod.map id bm ((i, y0) : ℕ × CTorus d L N₁ m₁ K)) (ιb x) (ιb y) =
      cubeG HA a ν α ((i, y0) : ℕ × CTorus d L N₁ m₁ K) x y := by
  classical
  rw [show Prod.map id bm ((i, y0) : ℕ × CTorus d L N₁ m₁ K) = (i, bm y0) from rfl]
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  set R : ℕ := ρ₀ + 3 * L ^ (i + m₁) with hR
  have hn1 : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ K := lt_of_le_of_lt (by omega) hn
  have hn2 : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K := lt_of_le_of_lt (by omega) hn'
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) := inBox_boxMap (by omega) hy0
  obtain ⟨ι, hι⟩ : ∃ ι : (HA).Ω 1 → (HB).Ω 1, ∀ z, ι z = ιb z := ⟨_, fun _ => rfl⟩
  rw [← hι, ← hι]
  have hcubeA : ∀ z : (HA).Ω 1,
      (z : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K) →
      InBox d R ((N₁ * L ^ m₁) * L ^ K) (z : CTorus d L N₁ m₁ K) :=
    fun z h => inBox_of_mem_intBox hy0 hn1 h
  have hcubeB : ∀ z : (HB).Ω 1,
      (z : CTorus d L N₁' m₁ K) ∈ intBox ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K) →
      InBox d R ((N₁' * L ^ m₁) * L ^ K) (z : CTorus d L N₁' m₁ K) :=
    fun z h => inBox_of_mem_intBox hy0' hn2 h
  have hiff : ∀ z : (HA).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ K) (z : CTorus d L N₁ m₁ K) →
      ((z : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
        ((ι z : _) : CTorus d L N₁' m₁ K) ∈ intBox ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K)) := by
    intro z hz
    rw [hι]
    exact mem_intBox_boxMap_iff_of_le (N₁' := N₁') hy0 le_rfl hn1 hn2 hz
  have hinj : ∀ a b : (HA).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ K) (a : CTorus d L N₁ m₁ K) →
      InBox d R ((N₁ * L ^ m₁) * L ^ K) (b : CTorus d L N₁ m₁ K) → ι a = ι b → a = b := by
    intro a b ha hb h
    rw [hι, hι] at h
    exact Subtype.ext (boxMap_inj (hm' := hn2) ha hb (congrArg Subtype.val h))
  have hsurj : ∀ z' : (HB).Ω 1,
      (z' : CTorus d L N₁' m₁ K) ∈ intBox ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K) →
      ∃ z : (HA).Ω 1, (z : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K) ∧
        ι z = z' := by
    intro z' h
    have hb' := hcubeB z' h
    have hback : bm (bm' (z' : CTorus d L N₁' m₁ K)) = z' := boxMap_boxMap hn1 hb'
    obtain ⟨zz, hzz⟩ : ∃ zz : (HA).Ω 1,
        (zz : CTorus d L N₁ m₁ K) = bm' (z' : CTorus d L N₁' m₁ K) :=
      ⟨⟨_, levelGS_mem_Ω_one hj1 hj _⟩, rfl⟩
    have hz1 : InBox d R ((N₁ * L ^ m₁) * L ^ K) (zz : CTorus d L N₁ m₁ K) := by
      rw [hzz]; exact inBox_boxMap hn1 hb'
    have hιz : ι zz = z' := by
      rw [hι]
      refine Subtype.ext ?_
      show bm (zz : CTorus d L N₁ m₁ K) = _
      rw [hzz]; exact hback
    exact ⟨zz, (hiff zz hz1).2 (by rw [hιz]; exact h), hιz⟩
  have hcore : ∀ x y : (HA).Ω 1,
      (x : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K) →
      (y : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K) →
      cubeG HB a ν α' (i, bm y0) (ι x) (ι y) = cubeG HA a ν α (i, y0) x y := by
    intro x y hxc hyc
    unfold cubeG
    refine inv_block_transport (fun z : (HA).Ω 1 => (z : CTorus d L N₁ m₁ K) ∈
        intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K))
      (fun z : (HB).Ω 1 => (z : CTorus d L N₁' m₁ K) ∈
        intBox ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K)) ι
      (fun a b ha hb h => hinj a b (hcubeA a ha) (hcubeA b hb) h)
      (fun z hz => (hiff z (hcubeA z hz)).1 hz) hsurj _ _ _ _
      (fun f z => cD_mulVec _ f z) (fun f z => cD_mulVec _ f z) ?_ ?_
      (Dec2.cubeH_isUnit SA hαA hq) (Dec2.cubeH_isUnit SB hαB hq') ?_ hxc hyc
    · intro x z hx hz
      rw [hι, hι]
      exact cubeH_boxMap_lvl (ρ := R) (ρ₀ := ρ₀) hj1 hj a ν hy0 hn hn' hm hm' hα x z
        (hcubeA x hx) (hcubeA z hz)
    · intro u hu x hx
      exact cutOperator_mulVec_apply_of_not_mem _ (SA.blockAligned _ hq) α hu x hx
    · intro f z hz
      exact Dec2.cubeG_supp SB hαB hq' f z hz
  by_cases hyc : (y : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K)
  · by_cases hxc : (x : CTorus d L N₁ m₁ K) ∈ intBox ((i, y0) : ℕ × CTorus d L N₁ m₁ K)
    · exact hcore x y hxc hyc
    · have hxc' : ¬ ((ι x : _) : CTorus d L N₁' m₁ K) ∈
          intBox ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K) := fun h => hxc ((hiff x hx).2 h)
      have e1 := Dec2.cubeG_supp SA hαA hq (Pi.single y 1) x hxc
      have e2 := Dec2.cubeG_supp SB hαB hq' (Pi.single (ι y) 1) (ι x) hxc'
      rw [cubeG_mulVec_single] at e1 e2
      rw [e1]; exact e2
  · have hyc' : ¬ ((ι y : _) : CTorus d L N₁' m₁ K) ∈
        intBox ((i, bm y0) : ℕ × CTorus d L N₁' m₁ K) := fun h => hyc ((hiff y hy).2 h)
    rw [cubeG_apply_of_not_mem _ _ _ hyc, cubeG_apply_of_not_mem _ _ _ hyc']

omit [NeZero N₁'] in
/-- The partition weight of the cover of level `j + 1` is the weight `chi` of `levelGS (j + 1)`. -/
theorem coverOf_chi_eq (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) :
    (CA).chi q x = chi (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱp)
      (j + 1) hjp) q x := rfl

/-- **The partition weight of the cover of level `j + 1` on two tori.**  For `x` in the box of
radius `ρ` and `y0` in the box of radius `ρ + 2 L^(j+1+m₁)`.  Margin:
`2 ρ + 5 L^(j+1+m₁) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem chi_cover_boxMap {ρ : ℕ}
    (hn : 2 * ρ + 5 * L ^ (j + 1 + m₁) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ (j + 1 + m₁) + 1 < (N₁' * L ^ m₁) * L ^ K)
    {x y0 : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy0 : InBox d (ρ + 2 * L ^ (j + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ K) y0) :
    (CB).chi (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) (bm x) =
      (CA).chi (j + 1, y0) x :=
  chi_boxMap (ϱ := ϱp) (by omega) hjp hn hn' hx hy0

include hj1 in
/-- **The commutator of the mixed pair on two tori.**  The entries of `K_z = χ_z H_D - H_D χ_z`
(`χ_z` of the cover of level `j + 1`, `H_D` of `levelGS j`) of the centre `(j + 1, y0)`, `y0` in
the box of radius `ρ + 2 L^(j+1+m₁)`, at two sites of the box of radius `ρ`, correspond.
Margins: `2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` and `2 ρ + 5 L^(j+1+m₁) + 1 < N₁ L^m₁ L^K` (and for
`N₁'`). -/
theorem Kz2_boxMap {ρ : ℕ} (a : ℕ → ℝ) (ν : ℝ) {y0 : CTorus d L N₁ m₁ K}
    (hy0 : InBox d (ρ + 2 * L ^ (j + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hm : 2 * ρ + 5 * L ^ (j + 1 + m₁) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hm' : 2 * ρ + 5 * L ^ (j + 1 + m₁) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (x y : (HA).Ω 1) (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    Dec2.Kz CB HB a ν (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) (ιb x) (ιb y) =
      Dec2.Kz CA HA a ν (j + 1, y0) x y := by
  rw [Dec2.Kz_apply (H := HB) 0, Dec2.Kz_apply (H := HA) 0,
    dirichletOperator_boxMap (α := 0) (α' := 0) hj1 hj a ν hn hn' (fun _ _ => rfl) x y hx hy]
  simp only [chi_cover_boxMap hjp hm hm' hx hy0, chi_cover_boxMap hjp hm hm' hy hy0]

/-! #### The cubes of level `j + 1` inside `T` -/

include hj1 in
/-- A centre of the cover of level `j + 1` whose interaction cube lies in `T` (read on the
lattice of level `j`) has its base point in `T`. -/
theorem inner2_base_mem {T : Finset (CTorus d L N₁ m₁ K)} {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ Dec2.innerCentres CA HA T) :
    ∃ y0, q = (j + 1, y0) ∧ CubeBase (K := K) m₁ (j + 1) y0 ∧ y0 ∈ T ∧
      ∀ x ∈ intBox q, x ∈ T := by
  obtain ⟨hqc, hsub⟩ := Finset.mem_filter.1 hq
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx (ϱ := ϱp) hjp hqc
  have hall : ∀ x ∈ intBox ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K), x ∈ T := fun x hx =>
    hsub ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hx
  exact ⟨y0, rfl, hb, hall _ (base_mem_intBox _), hall⟩

omit [NeZero N₁'] in
theorem mem_innerCentres2 {T : Finset (CTorus d L N₁ m₁ K)} {y0 : CTorus d L N₁ m₁ K}
    (hb : CubeBase (K := K) m₁ (j + 1) y0)
    (hsub : ∀ x ∈ intBox ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K), x ∈ T) :
    ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ Dec2.innerCentres CA HA T :=
  Finset.mem_filter.2 ⟨(mem_cubeIdx_levelGS hjp _).2 ⟨rfl, by omega, hb⟩, fun _ hx => hsub _ hx⟩

include hj1 in
/-- **The cubes of level `j + 1` inside `T` correspond.**  For `T` in the box of radius `R` and
`T' = bm '' T`.  Margin: `2 (R + 3 L^(j+1+m₁)) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem innerCentres2_mapsTo {T : Finset (CTorus d L N₁ m₁ K)}
    {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T') {R : ℕ}
    (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 2 * (R + 3 * L ^ (j + 1 + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (R + 3 * L ^ (j + 1 + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ Dec2.innerCentres CA HA T) :
    Prod.map id bm q ∈ Dec2.innerCentres CB HB T' := by
  obtain ⟨y0, rfl, hb, hy0T, hsub⟩ := inner2_base_mem hj1 hj hjp hq
  have hy0 := hTR y0 hy0T
  refine mem_innerCentres2 hj hjp (cubeBase_boxMap hjp hb) fun w hw => ?_
  have him := intBox_image (N₁' := N₁') (j := j + 1) hy0 hn hn'
  have hw' : w ∈ bm '' (↑(intBox ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) :
      Set (CTorus d L N₁ m₁ K)) := by
    rw [him]; exact hw
  obtain ⟨x, hx, hxw⟩ := hw'
  rw [← hT', Finset.mem_image]
  exact ⟨x, hsub x hx, hxw⟩

include hj1 in
/-- **The sum over the cubes of level `j + 1` inside `T`, on two tori.** -/
theorem sum_innerCentres2_boxMap {T : Finset (CTorus d L N₁ m₁ K)}
    {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T') {R : ℕ}
    (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 2 * (R + 3 * L ^ (j + 1 + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (R + 3 * L ^ (j + 1 + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (F : ℕ × CTorus d L N₁ m₁ K → ℂ) (F' : ℕ × CTorus d L N₁' m₁ K → ℂ)
    (hF : ∀ q ∈ Dec2.innerCentres CA HA T, F' (Prod.map id bm q) = F q) :
    ∑ q ∈ Dec2.innerCentres CB HB T', F' q = ∑ q ∈ Dec2.innerCentres CA HA T, F q := by
  symm
  refine Finset.sum_bij (fun q _ => Prod.map id bm q)
    (fun q hq => innerCentres2_mapsTo hj1 hj hjp hT' hTR hn hn' hq)
    (fun q1 hq1 q2 hq2 h => ?_) (fun q' hq' => ?_) (fun q hq => (hF q hq).symm)
  · obtain ⟨y1, rfl, -, hy1T, -⟩ := inner2_base_mem hj1 hj hjp hq1
    obtain ⟨y2, rfl, -, hy2T, -⟩ := inner2_base_mem hj1 hj hjp hq2
    have h2 : bm y1 = bm y2 := congrArg Prod.snd h
    rw [boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K)) (hTR y1 hy1T)
      (hTR y2 hy2T) h2]
  · obtain ⟨y', rfl, hb', hy'T, hsub'⟩ := inner2_base_mem (N₁ := N₁') hj1 hj hjp hq'
    rw [← hT', Finset.mem_image] at hy'T
    obtain ⟨y0, hy0T, rfl⟩ := hy'T
    have hy0 := hTR y0 hy0T
    have hb0 : CubeBase (K := K) m₁ (j + 1) y0 := by
      have := cubeBase_boxMap (N₁ := N₁') (N₁' := N₁) hjp hb'
      rwa [boxMap_boxMap (by omega) hy0] at this
    refine ⟨(j + 1, y0), mem_innerCentres2 hj hjp hb0 fun x hx => ?_, rfl⟩
    have hxb := inBox_of_mem_intBox hy0 hn hx
    have h1 : bm x ∈ intBox ((j + 1, bm y0) : ℕ × CTorus d L N₁' m₁ K) :=
      (mem_intBox_boxMap_iff hy0 hn hn' hxb).1 hx
    have h2 := hsub' _ h1
    rw [← hT', Finset.mem_image] at h2
    obtain ⟨x2, hx2T, hx2⟩ := h2
    have hx2b : InBox d (R + 3 * L ^ (j + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ K) x2 :=
      inBox_mono (by omega) (hTR x2 hx2T)
    rw [← boxMap_inj (hm' := hn') hx2b hxb hx2]
    exact hx2T

include hj1 in
/-- **The cube resolvent of a cube of level `j + 1` inside `T`, with potentials corresponding on
`T` only.**  For a centre of the cover of level `j + 1` whose interaction cube lies in `T` (`T` in
the box of radius `R`, `T' = bm '' T`), the entries of `cubeG` of `levelGS j` at two sites of the
box of radius `R + 3 L^(j+1+m₁)` correspond, for admissible potentials with `α'(bm x) = α x` on
`T`.  The potential of the second torus is replaced on the box by the transported one, which
does not change `cubeG` (`Dec2.cubeG_congr`).  Margin:
`4 R + 12 L^(j+1+m₁) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem cubeG2_boxMap_inner {a : ℕ → ℝ} {ν Kc Cx : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ Dec2.innerCentres CA HA T) (x z : (HA).Ω 1)
    (hx : InBox d (R + 3 * L ^ (j + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hz : InBox d (R + 3 * L ^ (j + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ K) (z : CTorus d L N₁ m₁ K)) :
    cubeG HB a ν α' (Prod.map id bm q) (ιb x) (ιb z) = cubeG HA a ν α q x z := by
  have hq' := innerCentres2_mapsTo hj1 hj hjp hT' hTR (by omega) (by omega) hq
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner2_base_mem hj1 hj hjp hq
  have hy0 := hTR y0 hy0T
  have hqc : ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ (CA).cubeIdx := (Finset.mem_filter.1 hq).1
  have hqc' : Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ (CB).cubeIdx :=
    (Finset.mem_filter.1 hq').1
  have hspA : ∀ w : CTorus d L N₁ m₁ K, (HA).spacing w = (L : ℝ) ^ j := fun w => by
    unfold GeneratingSet.spacing; rw [layerIndex_levelGS hj1 hj]
  have hspB : ∀ w : CTorus d L N₁' m₁ K, (HB).spacing w = (L : ℝ) ^ j := fun w => by
    unfold GeneratingSet.spacing; rw [layerIndex_levelGS hj1 hj]
  -- the potential of the second torus, replaced on the box by the transported one
  obtain ⟨α'', hα''⟩ : ∃ α'' : (HB).Ω 1 → ℂ, α'' = fun w : (HB).Ω 1 =>
      if InBox d (R + 3 * L ^ (j + 1 + m₁)) ((N₁' * L ^ m₁) * L ^ K) (w : CTorus d L N₁' m₁ K)
      then α ⟨bm' (w : CTorus d L N₁' m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ else α' w := ⟨_, rfl⟩
  have hα''B : AdmPot HB α'' := by
    intro w
    rw [hα'']
    dsimp only
    split_ifs with hw
    · have h1 := hαA ⟨bm' (w : CTorus d L N₁' m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
      rw [hspA] at h1
      rw [hspB]
      exact h1
    · exact hαB w
  have hα''x : ∀ x : (HA).Ω 1, InBox d (R + 3 * L ^ (j + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ K)
      (x : CTorus d L N₁ m₁ K) → α'' (ιb x) = α x := by
    intro x hx
    have h1 : InBox d (R + 3 * L ^ (j + 1 + m₁)) ((N₁' * L ^ m₁) * L ^ K)
        (bm (x : CTorus d L N₁ m₁ K)) := inBox_boxMap (by omega) hx
    rw [hα'']
    dsimp only
    split_ifs
    congr 1
    exact Subtype.ext (boxMap_boxMap (by omega) hx)
  have hagree'' : ∀ w : (HB).Ω 1, (w : CTorus d L N₁' m₁ K) ∈
      intBox (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) → α' w = α'' w := by
    intro w hw
    have hwT : (w : CTorus d L N₁' m₁ K) ∈ T' := (Finset.mem_filter.1 hq').2 w hw
    rw [← hT', Finset.mem_image] at hwT
    obtain ⟨x, hxT, hxw⟩ := hwT
    have hw' : w = ιb (⟨x, levelGS_mem_Ω_one hj1 hj x⟩ : (HA).Ω 1) := Subtype.ext hxw.symm
    rw [hw', hα ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hxT,
      hα''x ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ (inBox_mono (by omega) (hTR x hxT))]
  rw [Dec2.cubeG_congr SB hαB hα''B hqc' hagree'']
  exact cubeG_boxMap_lvl (ρ₀ := R) hj1 hj SA SB hy0 hqc hqc' (by omega) (by omega) (by omega)
    (by omega) hαA hα''B hα''x x z hx hz

include hj1 in
/-- The entries of `χ_z G^{(z)} c_z` of a cube of level `j + 1` inside `T` at two sites of `T`
correspond. -/
theorem chiD2_cubeG_boxMap_inner {a : ℕ → ℝ} {ν Kc Cx : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ Dec2.innerCentres CA HA T) (x z : (HA).Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    (Dec2.chiD CB HB (Prod.map id bm q) * cubeG HB a ν α' (Prod.map id bm q)) (ιb x) (ιb z) =
      (Dec2.chiD CA HA q * cubeG HA a ν α q) x z := by
  have hxR := hTR _ hx
  have hzR := hTR _ hz
  unfold Dec2.chiD
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, cubeG2_boxMap_inner hj1 hj hjp SA SB hT' hTR hn
    hn' hαA hαB hα hq x z (inBox_mono (by omega) hxR) (inBox_mono (by omega) hzR)]
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner2_base_mem hj1 hj hjp hq
  have hy0 := hTR y0 hy0T
  have hc := chi_cover_boxMap (ϱp := ϱp) (N₁' := N₁') (ρ := R) hjp (by omega) (by omega) hxR
    (inBox_mono (by omega) hy0)
  simp only [hc]

include hj1 in
/-- The entries of `K_z G^{(z)} c_z` of a cube of level `j + 1` inside `T` at two sites of `T`
correspond. -/
theorem Kz2_cubeG_boxMap_inner {a : ℕ → ℝ} {ν Kc Cx : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ Dec2.innerCentres CA HA T) (x z : (HA).Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    (Dec2.Kz CB HB a ν (Prod.map id bm q) * cubeG HB a ν α' (Prod.map id bm q)) (ιb x) (ιb z) =
      (Dec2.Kz CA HA a ν q * cubeG HA a ν α q) x z := by
  have hq' := innerCentres2_mapsTo hj1 hj hjp hT' hTR (by omega) (by omega) hq
  have hqc' := (Finset.mem_filter.1 hq').1
  have hqc := (Finset.mem_filter.1 hq).1
  have hxR := hTR _ hx
  have hzR := hTR _ hz
  have hn1 : 2 * (R + 3 * L ^ (j + 1 + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hn2 : 2 * (R + 3 * L ^ (j + 1 + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner2_base_mem hj1 hj hjp hq
  have hy0 := hTR y0 hy0T
  refine mul_apply_transport
    (fun w : (HA).Ω 1 => (w : CTorus d L N₁ m₁ K) ∈
      intBox ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K))
    (fun w : (HB).Ω 1 => (w : CTorus d L N₁' m₁ K) ∈
      intBox (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)))
    (fun w => ιb w) (fun w1 w2 h1 h2 h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
    (fun w hw => ?_) (fun w' hw' => ?_) (fun w hw => ?_)
  · exact Subtype.ext (boxMap_inj (hm' := hn2) (inBox_of_mem_intBox hy0 hn1 h1)
      (inBox_of_mem_intBox hy0 hn1 h2) (congrArg Subtype.val h))
  · exact (mem_intBox_boxMap_iff hy0 hn1 hn2 (inBox_of_mem_intBox hy0 hn1 hw)).1 hw
  · have hw'' : (w' : CTorus d L N₁' m₁ K) ∈
        intBox (Prod.map id bm ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)) := hw'
    have hwT : (w' : CTorus d L N₁' m₁ K) ∈ T' := (Finset.mem_filter.1 hq').2 w' hw''
    rw [← hT', Finset.mem_image] at hwT
    obtain ⟨x2, hx2T, hx2⟩ := hwT
    refine ⟨⟨x2, levelGS_mem_Ω_one hj1 hj x2⟩, ?_, Subtype.ext hx2⟩
    show x2 ∈ intBox ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K)
    rw [mem_intBox_boxMap_iff hy0 hn1 hn2 (inBox_mono (by omega) (hTR x2 hx2T)), hx2]
    exact hw''
  · have h1 := Dec2.cubeG_supp SA hαA hqc (Pi.single z 1) w hw
    rw [cubeG_mulVec_single] at h1
    rw [h1, mul_zero]
  · have h1 := Dec2.cubeG_supp SB hαB hqc' (Pi.single (ιb z) 1) w' hw'
    rw [cubeG_mulVec_single] at h1
    rw [h1, mul_zero]
  · have hwR := inBox_of_mem_intBox hy0 hn1 hw
    rw [Kz2_boxMap (ρ := R + 3 * L ^ (j + 1 + m₁)) hj1 hj hjp a ν (inBox_mono (by omega) hy0)
      (by omega) (by omega) (by omega) (by omega) x w (inBox_mono (by omega) hxR) hwR,
      cubeG2_boxMap_inner hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα hq w z hwR
        (inBox_mono (by omega) hzR)]

/-! #### The rows of `G*_s`, `𝒦_s` and `G_s` -/

include hj1 in
/-- **D1 (`G*_s` of the mixed pair).**  Let every interaction cube of level `j + 1` with a
non-zero factor lie inside `T` or avoid it (read on the lattice of level `j`), on both tori (`T` in
the box of radius `R`, `T' = bm '' T`), the factors `s_z` agree on the cubes inside `T` and the
potentials on `T`.  Then the entries of `G*_s` at two sites of `T` correspond.  Margin:
`4 R + 12 L^(j+1+m₁) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem Gstar2_boxMap_apply {a : ℕ → ℝ} {ν Kc Cx : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hdich : ∀ q ∈ (CA).cubeIdx, (CA).sProd s q ≠ 0 →
      SubI HA (intBox q) T ∨ DisjI HA (intBox q) T)
    (hdich' : ∀ q ∈ (CB).cubeIdx, (CB).sProd s' q ≠ 0 →
      SubI HB (intBox q) T' ∨ DisjI HB (intBox q) T')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA T, (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q)
    (x z : (HA).Ω 1) (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    Dec2.Gstar CB HB a ν α' s' (ιb x) (ιb z) = Dec2.Gstar CA HA a ν α s x z := by
  have hx' : ((ιb x : (HB).Ω 1) : CTorus d L N₁' m₁ K) ∈ T' := by
    rw [← hT']; exact Finset.mem_image_of_mem _ hx
  rw [Gstar2_apply_of_mem SA hαA hdich hx, Gstar2_apply_of_mem SB hαB hdich' hx']
  refine sum_innerCentres2_boxMap hj1 hj hjp hT' hTR (by omega) (by omega) _ _ fun q hq => ?_
  rw [hagree q hq, chiD2_cubeG_boxMap_inner hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα hq x z hx hz]

include hj1 in
/-- **D1 (`𝒦_s` of the mixed pair).**  Under the hypotheses of `Gstar2_boxMap_apply`, the entries
of `𝒦_s` at two sites of `T` correspond. -/
theorem Kcal2_boxMap_apply {a : ℕ → ℝ} {ν Kc Cx : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hdich : ∀ q ∈ (CA).cubeIdx, (CA).sProd s q ≠ 0 →
      SubI HA (intBox q) T ∨ DisjI HA (intBox q) T)
    (hdich' : ∀ q ∈ (CB).cubeIdx, (CB).sProd s' q ≠ 0 →
      SubI HB (intBox q) T' ∨ DisjI HB (intBox q) T')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA T, (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q)
    (x z : (HA).Ω 1) (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    Dec2.Kcal CB HB a ν α' s' (ιb x) (ιb z) = Dec2.Kcal CA HA a ν α s x z := by
  have hx' : ((ιb x : (HB).Ω 1) : CTorus d L N₁' m₁ K) ∈ T' := by
    rw [← hT']; exact Finset.mem_image_of_mem _ hx
  rw [Kcal2_apply_of_mem SA hdich hx, Kcal2_apply_of_mem SB hdich' hx']
  refine sum_innerCentres2_boxMap hj1 hj hjp hT' hTR (by omega) (by omega) _ _ fun q hq => ?_
  rw [hagree q hq, Kz2_cubeG_boxMap_inner hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα hq x z hx hz]

include hj1 in
/-- **The cut resolvent of the mixed pair on the component.**  Under the hypotheses of
`Kcal2_boxMap_apply` and the invertibility of `1 - 𝒦_s` on each torus, the entries of
`(1 - 𝒦_s)⁻¹` at two sites of `T` correspond (`𝒦_s` does not couple `T` to its complement, so the
`T`-block of `(1 - 𝒦_s)⁻¹` is the inverse of the `T`-block of `1 - 𝒦_s`). -/
theorem inv_one_sub_Kcal2_boxMap_apply {a : ℕ → ℝ} {ν Kc Cx : ℝ}
    (SA : Dec2.CoverBase CA HA a ν Kc Cx) (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hU : IsUnit (1 - Dec2.Kcal CA HA a ν α s)) (hU' : IsUnit (1 - Dec2.Kcal CB HB a ν α' s'))
    (hdich : ∀ q ∈ (CA).cubeIdx, (CA).sProd s q ≠ 0 →
      SubI HA (intBox q) T ∨ DisjI HA (intBox q) T)
    (hdich' : ∀ q ∈ (CB).cubeIdx, (CB).sProd s' q ≠ 0 →
      SubI HB (intBox q) T' ∨ DisjI HB (intBox q) T')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA T, (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q)
    (x z : (HA).Ω 1) (hx : (x : CTorus d L N₁ m₁ K) ∈ T) (hz : (z : CTorus d L N₁ m₁ K) ∈ T) :
    (1 - Dec2.Kcal CB HB a ν α' s')⁻¹ (ιb x) (ιb z) = (1 - Dec2.Kcal CA HA a ν α s)⁻¹ x z := by
  refine inv_one_sub_transport (fun w : (HA).Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ T)
    (fun w : (HB).Ω 1 => (w : CTorus d L N₁' m₁ K) ∈ T') (fun w => ιb w)
    (fun w1 w2 h1 h2 h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _
    (fun x z hx hz => Kcal2_apply_eq_zero_of_mem SA hdich hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_mem SB hdich' hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_not_mem SB hdich' hx hz)
    (fun x z hx hz => Kcal2_boxMap_apply hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα hdich hdich'
      hagree x z hx hz) hU hU' hx hz
  · exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K))
      (hTR _ h1) (hTR _ h2) (congrArg Subtype.val h))
  · show bm (w : CTorus d L N₁ m₁ K) ∈ T'
    rw [← hT']; exact Finset.mem_image_of_mem _ hw
  · have hw'' : (w' : CTorus d L N₁' m₁ K) ∈ T' := hw'
    rw [← hT', Finset.mem_image] at hw''
    obtain ⟨x2, hx2T, hx2⟩ := hw''
    exact ⟨⟨x2, levelGS_mem_Ω_one hj1 hj x2⟩, hx2T, Subtype.ext hx2⟩

include hj1 in
/-- **The rows of `G_s(A) f` of the mixed pair on `T`.**  Let `T` be a set of sites of the box of
radius `R` such that every interaction cube of level `j + 1` with a non-zero factor lies inside `T`
or avoids it, on both tori (`T' = bm '' T`), the factors agree on the cubes inside `T`, `1 - 𝒦_s`
is invertible on each torus, and the potentials and the sources agree on `T`.  Then
`G_s(A) f = G_{s'}(A') f'` on `T` (after `bm`).  Margin:
`4 R + 12 L^(j+1+m₁) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem Gs2_boxMap_rows {a : ℕ → ℝ} {ν Kc Cx : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {T : Finset (CTorus d L N₁ m₁ K)} {T' : Finset (CTorus d L N₁' m₁ K)} (hT' : T.image bm = T')
    {R : ℕ} (hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α x = α' (ιb x))
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hU : IsUnit (1 - Dec2.Kcal CA HA a ν α s)) (hU' : IsUnit (1 - Dec2.Kcal CB HB a ν α' s'))
    (hdich : ∀ q ∈ (CA).cubeIdx, (CA).sProd s q ≠ 0 →
      SubI HA (intBox q) T ∨ DisjI HA (intBox q) T)
    (hdich' : ∀ q ∈ (CB).cubeIdx, (CB).sProd s' q ≠ 0 →
      SubI HB (intBox q) T' ∨ DisjI HB (intBox q) T')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA T, (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q)
    {f : (HA).Ω 1 → ℂ} {f' : (HB).Ω 1 → ℂ}
    (hf : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → f x = f' (ιb x))
    (y : (HA).Ω 1) (hy : (y : CTorus d L N₁ m₁ K) ∈ T) :
    (Dec2.Gs CA HA a ν α s *ᵥ f) y = (Dec2.Gs CB HB a ν α' s' *ᵥ f') (ιb y) := by
  have hα' : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α' (ιb x) = α x :=
    fun x hx => (hα x hx).symm
  symm
  unfold Dec2.Gs
  refine resolvent_rows_transport (fun w : (HA).Ω 1 => (w : CTorus d L N₁ m₁ K) ∈ T)
    (fun w : (HB).Ω 1 => (w : CTorus d L N₁' m₁ K) ∈ T') (fun w => ιb w)
    (fun w1 w2 h1 h2 h => ?_) (fun w hw => ?_) (fun w' hw' => ?_) _ _ _ _
    (fun x z hx hz => Gstar2_apply_eq_zero_of_mem SA hαA hdich hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_mem SA hdich hx hz)
    (fun x z hx hz => Gstar2_apply_eq_zero_of_mem SB hαB hdich' hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_mem SB hdich' hx hz)
    (fun x z hx hz => Kcal2_apply_eq_zero_of_not_mem SB hdich' hx hz)
    (fun x z hx hz => Gstar2_boxMap_apply hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα' hdich
      hdich' hagree x z hx hz)
    (fun x z hx hz => Kcal2_boxMap_apply hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα' hdich
      hdich' hagree x z hx hz) hU hU' (fun z hz => (hf z hz).symm) hy
  · exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K))
      (hTR _ h1) (hTR _ h2) (congrArg Subtype.val h))
  · show bm (w : CTorus d L N₁ m₁ K) ∈ T'
    rw [← hT']; exact Finset.mem_image_of_mem _ hw
  · have hw'' : (w' : CTorus d L N₁' m₁ K) ∈ T' := hw'
    rw [← hT', Finset.mem_image] at hw''
    obtain ⟨x2, hx2T, hx2⟩ := hw''
    exact ⟨⟨x2, levelGS_mem_Ω_one hj1 hj x2⟩, hx2T, Subtype.ext hx2⟩

include hj1 in
/-- **D1 (FL-1, `decSol_green_rows_transport`): the rows of the decoupled Green operator of the
mixed pair on a component, on two tori.**  For the cover `C = coverOf (levelGS (j + 1))` and the
operator `H = levelGS j` of each torus, let `Y ⊇ T` be sets of sites of the box of radius `R`
(`Y' = bm '' Y`, `T' = bm '' T`; in the application `T = S_Y^F`).  Suppose, on each torus, every
interaction cube with a non-zero factor lies inside `T` or avoids it, and meets `Y` only inside
`T`; the factors agree on the cubes inside `T`; `1 - 𝒦_s` is invertible on each torus; the
admissible potentials and the sources agree on `T`.  Then for `y ∈ Y`,
`(G_s(A) f)(y) = (G_{s'}(A') f')(bm y)`.  On `T` this is `Gs2_boxMap_rows`; on `Y \ T` both sides
vanish (`Gs2_apply_eq_zero_of_not_mem`).  Margin: `4 R + 12 L^(j+1+m₁) + 3 L^K + 5 < N₁ L^m₁ L^K`
(and for `N₁'`). -/
theorem decSol_green_rows_transport {a : ℕ → ℝ} {ν Kc Cx : ℝ}
    (SA : Dec2.CoverBase CA HA a ν Kc Cx) (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {Y T : Finset (CTorus d L N₁ m₁ K)}
    {Y' T' : Finset (CTorus d L N₁' m₁ K)} (hY' : Y.image bm = Y') (hT' : T.image bm = T')
    (hTY : T ⊆ Y) {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → α x = α' (ιb x))
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hU : IsUnit (1 - Dec2.Kcal CA HA a ν α s)) (hU' : IsUnit (1 - Dec2.Kcal CB HB a ν α' s'))
    (hdich : ∀ q ∈ (CA).cubeIdx, (CA).sProd s q ≠ 0 →
      SubI HA (intBox q) T ∨ DisjI HA (intBox q) T)
    (hdich' : ∀ q ∈ (CB).cubeIdx, (CB).sProd s' q ≠ 0 →
      SubI HB (intBox q) T' ∨ DisjI HB (intBox q) T')
    (hrow : ∀ q ∈ (CA).cubeIdx, (CA).sProd s q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ (CB).cubeIdx, (CB).sProd s' q ≠ 0 → ∀ x ∈ Y', x ∈ intBox q → x ∈ T')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA T, (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q)
    {f : (HA).Ω 1 → ℂ} {f' : (HB).Ω 1 → ℂ}
    (hf : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ T → f x = f' (ιb x))
    (y : (HA).Ω 1) (hy : (y : CTorus d L N₁ m₁ K) ∈ Y) :
    (Dec2.Gs CA HA a ν α s *ᵥ f) y = (Dec2.Gs CB HB a ν α' s' *ᵥ f') (ιb y) := by
  have hTR : ∀ x ∈ T, InBox d R ((N₁ * L ^ m₁) * L ^ K) x := fun x hx => hYR x (hTY hx)
  by_cases hyT : (y : CTorus d L N₁ m₁ K) ∈ T
  · exact Gs2_boxMap_rows hj1 hj hjp SA SB hT' hTR hn hn' hαA hαB hα hU hU' hdich hdich' hagree
      hf y hyT
  · have hy' : ((ιb y) : CTorus d L N₁' m₁ K) ∈ Y' := by
      rw [← hY']; exact Finset.mem_image_of_mem _ hy
    have hyT' : ((ιb y) : CTorus d L N₁' m₁ K) ∉ T' := by
      intro h
      rw [← hT', Finset.mem_image] at h
      obtain ⟨x2, hx2T, hx2⟩ := h
      apply hyT
      rw [← boxMap_inj (hm' := (by omega : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K)) (hTR x2 hx2T)
        (hYR _ hy) hx2]
      exact hx2T
    rw [Gs2_apply_eq_zero_of_not_mem SA hαA hrow f hy hyT,
      Gs2_apply_eq_zero_of_not_mem SB hαB hrow' f' hy' hyT']

end MixedCube

/-! ### The block set `S_Y^F` of a union of components of the incidence graph (one torus) -/

section Component

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ}
  {ν : ℝ}

/-- **The dichotomy for `S_Y^F`** (`Dec2.fp_dichT` for one factor vector): for a union `(Y, A)` of
components of the incidence graph and factors vanishing on the parameter cubes outside `𝒞`, every
interaction cube with a non-zero factor lies inside `S_Y^F` or meets no operator site of it. -/
theorem dich_SYF_of_inc {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : Dec2.IsIncUnion C H a ν X₁ 𝒞 Y A)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0) :
    ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 →
      SubI H (intBox q) (Dec2.SYF C H a ν X₁ 𝒞 Y) ∨
        DisjI H (intBox q) (Dec2.SYF C H a ν X₁ 𝒞 Y) :=
  fun _ hq hs => Dec2.fp_dichT hY (s' := s) (fun P hP hPC => ⟨hs0 P hP hPC, hs0 P hP hPC⟩) hq
    (Or.inl hs)

/-- **The rows of a component outside `S_Y^F`**: an interaction cube with a non-zero factor meets
the operator sites of `Y` only inside `S_Y^F` (`Dec2.fp_vanish`). -/
theorem row_SYF_of_inc {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : Dec2.IsIncUnion C H a ν X₁ 𝒞 Y A)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0) :
    ∀ q ∈ C.cubeIdx, C.sProd s q ≠ 0 → ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (x : CTorus d L N₁ m₁ K) ∈ intBox q →
        (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF C H a ν X₁ 𝒞 Y :=
  fun _ hq hs _ hxY hxq => Dec2.fp_vanish hY hs0 hq hs hxq hxY

end Component

section ComponentRows

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱp : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K) (hjp : j + 1 ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "CA" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "CB" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- `S_Y^F ⊆ Y` for the operator `levelGS j` (every site is an operator site). -/
theorem SYF_subset_levelGS {a : ℕ → ℝ} {ν : ℝ} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} : Dec2.SYF CA HA a ν X₁ 𝒞 Y ⊆ Y :=
  fun x hx => Dec2.SYF_subset_Y (H := HA) (x := ⟨x, levelGS_mem_Ω_one hj1 hj x⟩) hx

include hj1 in
/-- **D1 on the block set of a union of components of the incidence graph.**
`decSol_green_rows_transport` with `T = S_Y^F`: let `(Y, A)` and `(Y', A')` be unions of
components of the incidence graphs of the two tori, with `Y' = bm '' Y` and
`S_{Y'}^F = bm '' S_Y^F` (`hB'`, the image of the block set), all in the box of radius `R`; the
factors vanish on the parameter cubes outside `𝒞` (resp. `𝒞'`) and agree on the interaction cubes
inside `S_Y^F` (`hagree`).  Then for admissible potentials and sources corresponding on `S_Y^F`,
the rows of `G_s(A) f` on `Y` correspond. -/
theorem decSol_green_rows_SYF {a : ℕ → ℝ} {ν Kc Cx : ℝ}
    (SA : Dec2.CoverBase CA HA a ν Kc Cx) (SB : Dec2.CoverBase CB HB a ν Kc Cx)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hY : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → s P = 0)
    (hs0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → s' P = 0)
    (hY' : Y.image bm = Y')
    (hB' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (hαA : AdmPot HA α) (hαB : AdmPot HB α')
    (hU : IsUnit (1 - Dec2.Kcal CA HA a ν α s)) (hU' : IsUnit (1 - Dec2.Kcal CB HB a ν α' s'))
    (hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y → α x = α' (ιb x))
    {f : (HA).Ω 1 → ℂ} {f' : (HB).Ω 1 → ℂ}
    (hf : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y → f x = f' (ιb x))
    (y : (HA).Ω 1) (hy : (y : CTorus d L N₁ m₁ K) ∈ Y) :
    (Dec2.Gs CA HA a ν α s *ᵥ f) y = (Dec2.Gs CB HB a ν α' s' *ᵥ f') (ιb y) :=
  decSol_green_rows_transport hj1 hj hjp SA SB hY' hB' (SYF_subset_levelGS hj1 hj hjp) hYR hn hn'
    hαA hαB hα hU hU' (dich_SYF_of_inc hY hs0) (dich_SYF_of_inc hYc hs0')
    (fun q hq hs x hx hxq => row_SYF_of_inc hY hs0 q hq hs ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hx hxq)
    (fun q hq hs x hx hxq => row_SYF_of_inc hYc hs0' q hq hs ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hx
      hxq) hagree hf y hy

end ComponentRows

end Balaban.Polymer.TwoTorusStep
