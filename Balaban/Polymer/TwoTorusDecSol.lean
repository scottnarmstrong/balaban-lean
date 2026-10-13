/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDecBg
public import Balaban.Polymer.TwoTorusSYF
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
* `decSol_rows_transport` (D2): for candidate multipliers corresponding on `B_F = S_Y^F` and data
  `(φ₀, α₀, δΨ, f₁)` corresponding on `B_F` (the base field on the row set `R(B_F)`), the rows of
  the fluctuation map `𝒩(δφ(δα))` correspond on `B_F` and the corrections `δφ(δα)` on `Y`
  (the collar of `levelGS j` is empty, so `pertSource` reads only `B_F`);
  `decSol_picard_rows_transport`: the rescaled maps `Smap` are conjugate on `B_F`.
* `decSol_component_unique` (D3): two fixed points of `Dec2.DecFixed` in the ball `c₆'` on the two
  tori agree on `B_F`, and their corrections on `Y`; the proof compares the Picard iterations from
  `0` (`fixed_agree_of_step_transport`, `smap_fixed_iterates`), with no whole-torus gluing.
* `decSol_value_twoTorus` (D4): the same for the values `Sol (s, e)` of maps with the defining
  property of the analytic solution of Theorem I-4a; `decSol_value_twoTorus_of_box` discharges the
  image of the block set (`SYF_image`) and the agreement of the cut weights (`hagree2_boxMap`).
* `decSol_data_of_decBg` (D5): the data agreement asked by D2 follows from the landed background
  comparison `decBg_component_unique` at level `j + 1` on the same component `Y`:
  `S_Y^F ⊆ S_Y` (`SYF_subset_SY_levelGS`) and `R(S_Y^F)` reads only `RowsDep (S_Y)`
  (`RowF_SYF_rowsDep`).
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

/-! ### The rows of the fluctuation map on two tori -/

section Generic2

/-- A fixed point of `Dec2.DecFixed` in the ball `|δα|₂ ≤ r` is the rescaling `δα = ξ / ℓ²` of the
unique fixed point `ξ` of `Smap` in the ball `‖ξ‖_∞ ≤ r` (the `Dec2` form of
`toAlpha_eq_of_decFixed`). -/
theorem toAlpha_eq_of_decFixed2 {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {s : Dec2.DecParams C} {ιU : Bool} {α₀ : H.Ω 1 → ℂ} {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Fs : H.Ω 1 × Fin N → ℂ} {r : ℝ} (hr : 0 ≤ r) {ξ δα : H.Ω 1 → ℂ}
    (huniq : ∀ ξ' ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) r,
      Smap H (Dec2.decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ Fs ξ' = ξ' → ξ' = ξ)
    (hf : Dec2.DecFixed C H a ν s ιU α₀ φ₀ Fs δα) (hsm : Small H δα r) :
    toAlpha H ξ = δα := by
  have hm : ofAlpha H δα ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) r := by
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hr).2 fun x => ?_
    rw [norm_ofAlpha]; exact hsm x
  have hf' : Smap H (Dec2.decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ Fs
      (ofAlpha H δα) = ofAlpha H δα := by
    funext x
    unfold Smap
    rw [toAlpha_ofAlpha]
    unfold Dec2.DecFixed at hf
    rw [hf]
    rfl
  rw [← huniq _ hm hf', toAlpha_ofAlpha]

end Generic2

section FlRows

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱp : ℝ} {j : ℕ}
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
/-- **The perturbation source of `levelGS j` on two tori.**  The collar of `levelGS j` is empty,
so `F_s = Q* a δΨ + 𝔟(δΨ) + f₁` at a site only reads `δΨ` and `f₁` at that site. -/
theorem pertSource_levelGS_boxMap (a : ℕ → ℝ) {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {δΨ' : CTorus d L N₁' m₁ K → Fin N → ℂ} {f₁ : (HA).Ω 1 × Fin N → ℂ}
    {f₁' : (HB).Ω 1 × Fin N → ℂ} (x : (HA).Ω 1)
    (hΨ : δΨ (x : CTorus d L N₁ m₁ K) = δΨ' (bm (x : CTorus d L N₁ m₁ K)))
    (hf : ∀ i, f₁ (x, i) = f₁' (ιb x, i)) (i : Fin N) :
    pertSource HB a δΨ' f₁' (ιb x, i) = pertSource HA a δΨ f₁ (x, i) := by
  have hc := not_mem_collar_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj1 hj
  have hc' := not_mem_collar_levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj1 hj
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply, hc, hc', ↓reduceIte, add_zero, Finset.sum_const_zero,
    layerIndex_levelGS hj1 hj]
  rw [hΨ, hf i]

include hj1 in
/-- **The Dirichlet operator with a potential, on two tori.**  The entries at two sites of the box
of radius `ρ` of `H_D(α)` correspond if the potentials agree at the row site (the potential only
enters on the diagonal).  Margin: `2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem dirichletOperator_pot_boxMap {ρ : ℕ} (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (HA).Ω 1 → ℂ} {α' : (HB).Ω 1 → ℂ} (x y : (HA).Ω 1) (hαx : α x = α' (ιb x))
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    dirichletOperator HB a ν α' (ιb x) (ιb y) = dirichletOperator HA a ν α x y := by
  rw [dirichletOperator_eq_add a ν α', dirichletOperator_eq_add a ν α]
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  rw [dirichletOperator_boxMap (α := 0) (α' := 0) hj1 hj a ν hn hn' (fun _ _ => rfl) x y hx hy]
  by_cases hxy : x = y
  · subst hxy
    simp [hαx]
  · have h2 : (ιb x : (HB).Ω 1) ≠ ιb y := fun h => hxy (Subtype.ext
      (boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K)) hx hy
        (congrArg Subtype.val h)))
    simp [hxy, h2]

include hj1 in
/-- **D2 (FL-2, `decSol_rows_transport`): the rows of the fluctuation map on two tori.**  For the
pair `(coverOf (levelGS (j + 1)), levelGS j)` on each torus, let `(Y, A)`, `(Y', A')` be unions of
components of the incidence graphs with `Y' = bm '' Y` and `S_{Y'}^F = bm '' S_Y^F` (`hB'`), all in
the box of radius `R`; let the factors vanish on the parameter cubes outside `𝒞` (resp. `𝒞'`) and
agree on the interaction cubes inside `B_F = S_Y^F` (`hagree`).  Let the data of the two
fluctuation problems correspond: the base potential `α₀` and the perturbation `δΨ`, `f₁` on `B_F`,
the base field `φ₀` on the row set `R(B_F)` (`RowF`) (the collar of `levelGS j` is empty, so no
collar condition enters).  For candidate multipliers `δα`, `δα'` corresponding on `B_F` with
`|α₀ + δα|₂, |α₀' + δα'|₂ ≤ γ₁/8`:

* the rows at `x ∈ B_F` of `𝒩(δφ(δα))` (the left side of `Dec2.DecFixed`) correspond;
* the corrections `δφ(δα) = G_s(α₀ + δα)(F_s - δα φ₀)` correspond at every site of `Y`.

Margin: `4 R + 12 L^(j+1+m₁) + 7 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem decSol_rows_transport {Kc Cx cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    {a : ℕ → ℝ} {ν : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : Dec2.DecParams CA} {s' : Dec2.DecParams CB} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hY : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    (hs0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → Dec2.extS CA s P = 0)
    (hs0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → Dec2.extS CB s' P = 0)
    (hY' : Y.image bm = Y')
    (hB' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd (Dec2.extS CB s') (Prod.map id bm q) = (CA).sProd (Dec2.extS CA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (ιU : Bool) {α₀ : (HA).Ω 1 → ℂ} {α₀' : (HB).Ω 1 → ℂ}
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ₀' δΨ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    {f₁ : (HA).Ω 1 × Fin N → ℂ} {f₁' : (HB).Ω 1 × Fin N → ℂ}
    (hαB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      α₀ x = α₀' (ιb x))
    (hφR : ∀ y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y), φ₀ y = φ₀' (bm y))
    (hΨB : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, δΨ x = δΨ' (bm x))
    (hfB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ∀ i : Fin N, f₁ (x, i) = f₁' (ιb x, i))
    {δα : (HA).Ω 1 → ℂ} {δα' : (HB).Ω 1 → ℂ}
    (hsm : Small HA (α₀ + δα) (gamma1 d / 8)) (hsm' : Small HB (α₀' + δα') (gamma1 d / 8))
    (hδ : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      δα x = δα' (ιb x)) :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      Nmap HA (dirichletOperator HA a ν α₀) ιU φ₀ (pertSource HA a δΨ f₁)
          (dphi HA (Dec2.decG CA HA a ν s) α₀ φ₀ (pertSource HA a δΨ f₁) δα) x =
        Nmap HB (dirichletOperator HB a ν α₀') ιU φ₀' (pertSource HB a δΨ' f₁')
          (dphi HB (Dec2.decG CB HB a ν s') α₀' φ₀' (pertSource HB a δΨ' f₁') δα') (ιb x)) ∧
    (∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi HA (Dec2.decG CA HA a ν s) α₀ φ₀ (pertSource HA a δΨ f₁) δα (y, i) =
        dphi HB (Dec2.decG CB HB a ν s') α₀' φ₀' (pertSource HB a δΨ' f₁') δα' (ιb y, i)) := by
  classical
  have hd0 : 0 < d := by have := SA.hd; omega
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hBY : Dec2.SYF CA HA a ν X₁ 𝒞 Y ⊆ Y := SYF_subset_levelGS hj1 hj hjp
  have hBR : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x :=
    fun x hx => hYR x (hBY hx)
  obtain ⟨-, hunit⟩ := hF.2.2 CA HA SA hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 CB HB SB hκ hM hs' N
  have hA := admPot_of_small hd0 hsm
  have hA' := admPot_of_small hd0 hsm'
  -- the source at the sites of `B_F`
  have hFs : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ∀ i : Fin N, pertSource HB a δΨ' f₁' (ιb x, i) = pertSource HA a δΨ f₁ (x, i) :=
    fun x hx i => pertSource_levelGS_boxMap hj1 hj a x (hΨB _ hx) (hfB x hx) i
  -- the correction on `Y`
  have hdphi : ∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi HA (Dec2.decG CA HA a ν s) α₀ φ₀ (pertSource HA a δΨ f₁) δα (y, i) =
        dphi HB (Dec2.decG CB HB a ν s') α₀' φ₀' (pertSource HB a δΨ' f₁') δα' (ιb y, i) := by
    intro y hy i
    unfold dphi Dec2.decG
    rw [liftOp_mulVec, liftOp_mulVec]
    refine decSol_green_rows_SYF hj1 hj hjp SA SB hY hYc hs0 hs0' hY' hB' hagree hYR (by omega)
      (by omega) hA hA' (hunit hA) (hunit' hA') (fun x hx => ?_) (fun x hx => ?_) y hy
    · simp only [Pi.add_apply]
      rw [hαB x hx, hδ x hx]
    · simp only [Fsrc]
      rw [← hFs x hx i, hδ x hx, hφR _ (Dec2.RowsFl.subset_RowF hx)]
  refine ⟨fun x hx => ?_, hdphi⟩
  have hxR := hBR _ hx
  have hres := resSites_levelGS_image (ϱ := ϱ) (m₁ := m₁) (N₁ := N₁) (N₁' := N₁') (ρ := R) hj1 hj
    (by omega) (by omega) hxR
  have hrb : ∀ y ∈ resSites HA (x : CTorus d L N₁ m₁ K),
      InBox d (R + L ^ K) ((N₁ * L ^ m₁) * L ^ K) y := fun y hy =>
    inBox_of_mem_resSites_levelGS hj1 hj (by omega) hxR hy
  have hxRow : (x : CTorus d L N₁ m₁ K) ∈
      Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y) := Dec2.RowsFl.subset_RowF hx
  rw [Nmap_explicit, Nmap_explicit]
  symm
  refine Nexp_transport ιU (fun y : (HA).Ω 1 => (y : CTorus d L N₁ m₁ K) ∈
      resSites HA (x : CTorus d L N₁ m₁ K))
    (fun y : (HB).Ω 1 => (y : CTorus d L N₁' m₁ K) ∈ resSites HB (bm (x : CTorus d L N₁ m₁ K)))
    (fun y => ιb y) (fun y1 y2 h1 h2 h => ?_) (fun y hy => ?_) (fun y' hy' => ?_)
    (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_) (fun i => (congrFun (hφR _ hxRow) i).symm)
    (fun i => hFs x hx i) (fun i => (hdphi x (hBY hx) i).symm) (fun y hy hne => ?_)
  · exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * (R + L ^ K) + 1 < (N₁' * L ^ m₁) * L ^ K))
      (hrb _ h1) (hrb _ h2) (congrArg Subtype.val h))
  · show bm (y : CTorus d L N₁ m₁ K) ∈ resSites HB (bm (x : CTorus d L N₁ m₁ K))
    have : bm (y : CTorus d L N₁ m₁ K) ∈ (↑(resSites HB (bm (x : CTorus d L N₁ m₁ K))) :
        Set (CTorus d L N₁' m₁ K)) := by
      rw [hres]; exact Set.mem_image_of_mem _ hy
    exact this
  · have : (y' : CTorus d L N₁' m₁ K) ∈ (↑(resSites HB (bm (x : CTorus d L N₁ m₁ K))) :
        Set (CTorus d L N₁' m₁ K)) := hy'
    rw [hres] at this
    obtain ⟨y0, hy0, hyy⟩ := this
    exact ⟨⟨y0, levelGS_mem_Ω_one hj1 hj y0⟩, hy0, Subtype.ext hyy⟩
  · by_contra hne
    exact hy (mem_resSites_of_entry_ne_zero (x := x) (y := y) hne)
  · by_contra hne
    exact hy (mem_resSites_of_entry_ne_zero (G := HB) (x := ιb x) (y := y) hne)
  · exact dirichletOperator_pot_boxMap (ρ := R + L ^ K) hj1 hj a ν (by omega) (by omega) x y
      (hαB x hx) (inBox_mono (by omega) hxR) (hrb _ hy)
  · have hyR := Dec2.RowsFl.row_mem_RowF hx α₀ hne
    exact ⟨fun i => (congrFun (hφR _ hyR) i).symm,
      fun i => (hdphi y (Dec2.RowsFl.RowF_SYF_subset_Y hyR) i).symm⟩

include hj1 in
/-- **The restricted Picard map of the fluctuation on two tori.**  Under the hypotheses of
`decSol_rows_transport` on the geometry and the data, with `|α₀|₂ ≤ δ₀`, `|α₀'|₂ ≤ δ₀'` and
`δ₀ + ρ, δ₀' + ρ ≤ γ₁/8`, the rescaled fluctuation maps `ξ ↦ ℓ² 𝒩(δφ(ξ/ℓ²))` (the maps `Smap` whose
fixed points are the multipliers of `Dec2.DecFixed`) are conjugate on `B_F`: for
`‖ξ‖_∞, ‖ξ'‖_∞ ≤ ρ` with `ξ = ξ' ∘ bm` on `B_F`, their values at `x ∈ B_F` and `bm x` agree.  In
particular the value on `B_F` only depends on the argument on `B_F`. -/
theorem decSol_picard_rows_transport {Kc Cx cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    {a : ℕ → ℝ} {ν : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : Dec2.DecParams CA} {s' : Dec2.DecParams CB} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hY : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    (hs0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → Dec2.extS CA s P = 0)
    (hs0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → Dec2.extS CB s' P = 0)
    (hY' : Y.image bm = Y')
    (hB' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd (Dec2.extS CB s') (Prod.map id bm q) = (CA).sProd (Dec2.extS CA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (ιU : Bool) {α₀ : (HA).Ω 1 → ℂ} {α₀' : (HB).Ω 1 → ℂ}
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ₀' δΨ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    {f₁ : (HA).Ω 1 × Fin N → ℂ} {f₁' : (HB).Ω 1 × Fin N → ℂ}
    (hαB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      α₀ x = α₀' (ιb x))
    (hφR : ∀ y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y), φ₀ y = φ₀' (bm y))
    (hΨB : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, δΨ x = δΨ' (bm x))
    (hfB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ∀ i : Fin N, f₁ (x, i) = f₁' (ιb x, i))
    {δ₀ δ₀' ρ : ℝ} (hα0 : Small HA α₀ δ₀) (hα0' : Small HB α₀' δ₀')
    (hρ : δ₀ + ρ ≤ gamma1 d / 8) (hρ' : δ₀' + ρ ≤ gamma1 d / 8)
    {ξ : (HA).Ω 1 → ℂ} {ξ' : (HB).Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hξ' : ∀ x, ‖ξ' x‖ ≤ ρ)
    (hξξ : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ξ x = ξ' (ιb x)) :
    ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      Smap HA (Dec2.decG CA HA a ν s) (dirichletOperator HA a ν α₀) ιU α₀ φ₀
          (pertSource HA a δΨ f₁) ξ x =
        Smap HB (Dec2.decG CB HB a ν s') (dirichletOperator HB a ν α₀') ιU α₀' φ₀'
          (pertSource HB a δΨ' f₁') ξ' (ιb x) := by
  intro x hx
  have hspA := spacing_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj1 hj
  have hspB := spacing_levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj1 hj
  have hsm : Small HA (α₀ + toAlpha HA ξ) (gamma1 d / 8) := fun z =>
    ((Small.add hα0 (small_toAlpha HA ξ hξ)) z).trans hρ
  have hsm' : Small HB (α₀' + toAlpha HB ξ') (gamma1 d / 8) := fun z =>
    ((Small.add hα0' (small_toAlpha HB ξ' hξ')) z).trans hρ'
  have hα : ∀ z : (HA).Ω 1, (z : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      toAlpha HA ξ z = toAlpha HB ξ' (ιb z) := fun z hz => by
    unfold toAlpha; rw [hξξ z hz, hspA, hspB]
  unfold Smap
  rw [hspA, hspB]
  congr 1
  exact (decSol_rows_transport hj1 hj hjp hF SA SB hκ hM hs hs' hY hYc hs0 hs0' hY' hB' hagree
    hYR hn hn' ιU hαB hφR hΨB hfB hsm hsm' hα).1 x hx

include hj1 in
/-- **D3 (FL-3, `decSol_component_unique`): component comparison of the decoupled fluctuation on
two tori.**  Let `δα`, `δα'` be fixed points of `Dec2.DecFixed` in the ball `|δα|₂ ≤ c₆'` for data
satisfying the hypotheses `DecHyp` of Theorem I-4a on the two tori (with `δ₀, δ₁, δ₀', δ₁' ≤ δ*'`),
and suppose the hypotheses of `decSol_rows_transport` on the geometry and the data.  Then the
multipliers correspond on `B_F = S_Y^F` and the corrections `δφ` correspond on `Y`.

Proof: the Picard iterations from `0` of the rescaled maps of the two tori correspond on `B_F` at
every step (`decSol_picard_rows_transport`), and converge to the rescaled multipliers by the landed
contraction `smap_fixed_iterates` (rate `1/2` in the ball `c₆'`); no whole-torus gluing is used. -/
theorem decSol_component_unique {Kc Cx cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    {a : ℕ → ℝ} {ν : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : Dec2.DecParams CA} {s' : Dec2.DecParams CB} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hY : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    (hs0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → Dec2.extS CA s P = 0)
    (hs0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → Dec2.extS CB s' P = 0)
    (hY' : Y.image bm = Y')
    (hB' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd (Dec2.extS CB s') (Prod.map id bm q) = (CA).sProd (Dec2.extS CA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (ιU : Bool) {α₀ : (HA).Ω 1 → ℂ} {α₀' : (HB).Ω 1 → ℂ}
    {φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ₀' δΨ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    {f₁ : (HA).Ω 1 × Fin N → ℂ} {f₁' : (HB).Ω 1 × Fin N → ℂ} {δ₀ δ₁ δ₀' δ₁' : ℝ}
    (Hh : DecHyp HA a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (Hh' : DecHyp HB a ν ιU α₀' φ₀' δΨ' f₁' δ₀' δ₁')
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁' : δ₁' ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hαB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      α₀ x = α₀' (ιb x))
    (hφR : ∀ y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y), φ₀ y = φ₀' (bm y))
    (hΨB : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, δΨ x = δΨ' (bm x))
    (hfB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ∀ i : Fin N, f₁ (x, i) = f₁' (ιb x, i))
    {δα : (HA).Ω 1 → ℂ} {δα' : (HB).Ω 1 → ℂ}
    (hfix : Dec2.DecFixed CA HA a ν s ιU α₀ φ₀ (pertSource HA a δΨ f₁) δα)
    (hsm : Small HA δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed CB HB a ν s' ιU α₀' φ₀' (pertSource HB a δΨ' f₁') δα')
    (hsm' : Small HB δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      δα' (ιb x) = δα x) ∧
    (∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi HB (Dec2.decG CB HB a ν s') α₀' φ₀' (pertSource HB a δΨ' f₁') δα' (ιb y, i) =
        dphi HA (Dec2.decG CA HA a ν s) α₀ φ₀ (pertSource HA a δΨ f₁) δα (y, i)) := by
  classical
  have hd0 : 0 < d := by have := SA.hd; omega
  have hBG := hF.2.1
  set Bc : ℝ := famConst d L BG κ with hBc
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ Bc := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  have hC' := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh'.δ₀_nn Hh'.δ₁_nn hδ₀' hδ₁'
  obtain ⟨⟨hfam, -⟩, -⟩ := hF.2.2 CA HA SA hκ hM hs N
  obtain ⟨⟨hfam', -⟩, -⟩ := hF.2.2 CB HB SB hκ hM hs' N
  obtain ⟨ξ, -, -, hξuniq, hit⟩ := smap_fixed_iterates hfam Hh.setup hC
  obtain ⟨ξ', -, -, hξuniq', hit'⟩ := smap_fixed_iterates hfam' Hh'.setup hC'
  have e1 : toAlpha HA ξ = δα := toAlpha_eq_of_decFixed2 hC.ρ_nn hξuniq hfix hsm
  have e2 : toAlpha HB ξ' = δα' := toAlpha_eq_of_decFixed2 hC.ρ_nn hξuniq' hfix' hsm'
  have hpoly : δ₀ + c6' d L N Bc Γ ≤ Γ := by linarith [hC.poly, hC.ρ_nn]
  have hpoly' : δ₀' + c6' d L N Bc Γ ≤ Γ := by linarith [hC'.poly, hC'.ρ_nn]
  -- the iterations correspond on `B_F`
  have hagreeξ : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ξ x = ξ' (ιb x) := by
    refine fixed_agree_of_step_transport (fun x => ιb x)
      (T := fun x : (HA).Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y)
      (fun u v hu hv huv x hx => ?_) hit hit' hC.ρ_nn
    exact decSol_picard_rows_transport hj1 hj hjp hF SA SB hκ hM hs hs' hY hYc hs0 hs0' hY' hB'
      hagree hYR hn hn' ιU hαB hφR hΨB hfB Hh.alpha0 Hh'.alpha0 hpoly hpoly' hu hv huv x hx
  have hspA := spacing_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj1 hj
  have hspB := spacing_levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (ϱ := ϱ) hj1 hj
  have hα : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      δα x = δα' (ιb x) := by
    intro x hx
    rw [← e1, ← e2]
    unfold toAlpha
    rw [hagreeξ x hx, hspA, hspB]
  -- the corrections on `Y`
  have hsmA : Small HA (α₀ + δα) Γ := fun z => ((Small.add Hh.alpha0 hsm) z).trans hpoly
  have hsmB : Small HB (α₀' + δα') Γ := fun z => ((Small.add Hh'.alpha0 hsm') z).trans hpoly'
  have hrows := decSol_rows_transport hj1 hj hjp hF SA SB hκ hM hs hs' hY hYc hs0 hs0' hY' hB'
    hagree hYR hn hn' ιU hαB hφR hΨB hfB hsmA hsmB hα
  exact ⟨fun x hx => (hα x hx).symm, fun y hy i => (hrows.2 y hy i).symm⟩

include hj1 in
/-- **D4 (FL-4, `decSol_value_twoTorus`): the values of the decoupled fluctuation on two tori.**
Let `Sol`, `Sol'` be maps with the defining property of the analytic solution of Theorem I-4a on
the pair of each torus (the form of `Dec2.i4a_analytic` and of the hypothesis `hSol` of
`point_facts_fl`): on parameters with `|s_P| < e^κ` and data `e` with the strict inequalities
`StrictDataM`, `(Sol (s, e)).1 = δφ((Sol (s, e)).2)`, `(Sol (s, e)).2` is a fixed point of
`Dec2.DecFixed` in the ball `c₆'`, with the bounds and the uniqueness.  Under the hypotheses of
`decSol_rows_transport` on the geometry and on the data `e = (φ₀, α₀, δΨ, f₁)`, `e'`, the values
correspond: the multipliers `(Sol p).2` on `B_F = S_Y^F` and the corrections `(Sol p).1` on `Y`. -/
theorem decSol_value_twoTorus {Kc Cx cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    {a : ℕ → ℝ} {ν : ℝ} (SA : Dec2.CoverBase CA HA a ν Kc Cx)
    (SB : Dec2.CoverBase CB HB a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (ιU : Bool) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams CA × Edat HA N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams CB × Edat HB N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams CA × Edat HA N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM HA N ιU δ₀ δ₁ p.2 →
        (Sol p).1 = dphi HA (Dec2.decG CA HA a ν p.1) p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed CA HA a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small HA (Sol p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small HA (Sol p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds HA (Sol p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small HA δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          Dec2.DecFixed CA HA a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HA a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams CB × Edat HB N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM HB N ιU δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi HB (Dec2.decG CB HB a ν p.1) p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed CB HB a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small HB (Sol' p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small HB (Sol' p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds HB (Sol' p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small HB δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          Dec2.DecFixed CB HB a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HB a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {s : Dec2.DecParams CA} {s' : Dec2.DecParams CB} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ) {e : Edat HA N} {e' : Edat HB N}
    (he : StrictDataM HA N ιU δ₀ δ₁ e) (he' : StrictDataM HB N ιU δ₀ δ₁ e')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hY : Dec2.IsIncUnion CA HA a ν X₁ 𝒞 Y A) (hYc : Dec2.IsIncUnion CB HB a ν X₁' 𝒞' Y' A')
    (hs0 : ∀ P ∈ (CA).parCubes X₁, P ∉ 𝒞 → Dec2.extS CA s P = 0)
    (hs0' : ∀ P ∈ (CB).parCubes X₁', P ∉ 𝒞' → Dec2.extS CB s' P = 0)
    (hY' : Y.image bm = Y')
    (hB' : (Dec2.SYF CA HA a ν X₁ 𝒞 Y).image bm = Dec2.SYF CB HB a ν X₁' 𝒞' Y')
    (hagree : ∀ q ∈ Dec2.innerCentres CA HA (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      (CB).sProd (Dec2.extS CB s') (Prod.map id bm q) = (CA).sProd (Dec2.extS CA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hαB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      e.2.1 x = e'.2.1 (ιb x))
    (hφR : ∀ y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y), e.1 y = e'.1 (bm y))
    (hΨB : ∀ x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y, e.2.2.1 x = e'.2.2.1 (bm x))
    (hfB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      ∀ i : Fin N, e.2.2.2 (x, i) = e'.2.2.2 (ιb x, i)) :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      (Sol' (s', e')).2 (ιb x) = (Sol (s, e)).2 x) ∧
    (∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      (Sol' (s', e')).1 (ιb y, i) = (Sol (s, e)).1 (y, i)) := by
  set Bc : ℝ := famConst d L BG κ with hBc
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hle1 : δ₀ ≤ 1 := hδ₀.trans (by
    have := (min_le_right (min (cTau' d L N Bc / 3) (Γ / 4))
      (min (min 1 (c6' d L N Bc Γ / (2 * cN' d L N Bc))) (cTau' d L N Bc / (3 * cF d L))))
    exact this.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have Hh := StrictDataM.hyp SA.toGreen h0 h1 hle1 he
  have Hh' := StrictDataM.hyp SB.toGreen h0 h1 hle1 he'
  obtain ⟨hfld, hfix, hsm, -⟩ := hSol (s, e) hs he
  obtain ⟨hfld', hfix', hsm', -⟩ := hSol' (s', e') hs' he'
  obtain ⟨hα, hcorr⟩ := decSol_component_unique hj1 hj hjp hF SA SB hκ hM (fun P => (hs P).le)
    (fun P => (hs' P).le) hY hYc hs0 hs0' hY' hB' hagree hYR hn hn' ιU Hh Hh' hδ₀ hδ₁ hδ₀ hδ₁
    hαB hφR hΨB hfB hfix hsm hfix' hsm'
  refine ⟨hα, fun y hy i => ?_⟩
  rw [hfld, hfld']
  exact hcorr y hy i

end FlRows

/-! ### The geometric inputs and the data of the fluctuation -/

section Corollaries

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱp : ℝ} {j : ℕ}
variable (hj1 : 1 ≤ j) (hj : j ≤ K) (hjp : j + 1 ≤ K)

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "PA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱp)
  (j + 1) hjp
local notation "PB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱp)
  (j + 1) hjp
local notation "CA" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "CB" => coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
  (ϱ := ϱp) (j + 1) hjp)
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ K))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := K) (ϱ := ϱ) hj1 hj _)

include hj1 in
/-- **The cut weights of the cover of level `j + 1` on the inner cubes** (`hagree` of
`decSol_green_rows_transport`).  For a set `T` inside `Y` (in the box of radius `ρ`), the cut
weights `s_z = ∏_{P ∈ 𝒬(z)} s_P` of the cover `coverOf (levelGS (j + 1))` agree at the image of
every centre whose interaction cube lies in `T`, if the parameters agree at the cubes of the box
of radius `ρ₁ = ρ + (3 L^(j+1+m₁) + 3 L^(j+3)) + L^(j+1+m₁)` (the landed `sProd_boxMap` at level
`j + 1`).  Margin: `2 ρ₁ + 5 L · cellSide L 0 m₁ (j+1) < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem hagree2_boxMap {ρ : ℕ}
    (hn : 2 * (ρ + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (j + 1)) < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (j + 1)) < (N₁' * L ^ m₁) * L ^ K)
    {T Y : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ cubeIdx PA,
      InBox d (ρ + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁))
        ((N₁ * L ^ m₁) * L ^ K) P.2 → s' (Prod.map id bm P) = s P) :
    ∀ q ∈ Dec2.innerCentres CA HA T, (CB).sProd s' (Prod.map id bm q) = (CA).sProd s q := by
  intro q hq
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (j + 1)
  obtain ⟨y0, rfl, -, hy0T, -⟩ := inner2_base_mem hj1 hj hjp hq
  have hqc : ((j + 1, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ cubeIdx PA := (Finset.mem_filter.1 hq).1
  have hy0 := hY _ (hTY hy0T)
  exact sProd_boxMap (by omega) hjp hn hn' hqc hy0 fun P hP => hs P
    (Qset_subset_cubeIdx _ hP) (by
      obtain ⟨y1, rfl, -, hy1⟩ := qset_base_inBox (ϱ := ϱp) hjp (by omega) hy0 hP
      exact hy1)

include hj1 in
/-- **D4 with the geometric inputs discharged.**  `decSol_value_twoTorus` for the image sets
`X₁' = bm '' X₁`, `𝒞' = Prod.map id bm '' 𝒞`, `Y' = bm '' Y` of sets in the box of radius `R`
(same separation parameter `ϱ` for the cover and the operator, as in W633): the image of the
block set is `SYF_image`, and the agreement of the cut weights on the inner cubes of `S_Y^F` is
`hagree2_boxMap`, from parameters that correspond at the cubes of the box of radius
`R₁ = R + (3 L^(j+1+m₁) + 3 L^(j+3)) + L^(j+1+m₁)` (`hsP`).  Margins:
`4 R + 12 L^(j+1+m₁) + 7 L^K + 5 < N₁ L^m₁ L^K`, `2 R₁ + 5 L · cellSide L 0 m₁ (j+1) < N₁ L^m₁ L^K`
and `2 (R + 3 L^(j+1+m₁) + L^j) + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem decSol_value_twoTorus_of_box {Kc Cx cstar BG : ℝ} (hF : Dec2.FamSpec d L Kc Cx cstar BG)
    {a : ℕ → ℝ} {ν : ℝ}
    (SA : Dec2.CoverBase (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp)) HA a ν Kc Cx)
    (SB : Dec2.CoverBase (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp)) HB a ν Kc Cx) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (ιU : Bool) {δ₀ δ₁ : ℝ}
    (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp)) × Edat HA N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp)) × Edat HB N → ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := K) (ϱ := ϱ) (j + 1) hjp)) × Edat HA N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM HA N ιU δ₀ δ₁ p.2 →
        (Sol p).1 = dphi HA (Dec2.decG (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := K) (ϱ := ϱ) (j + 1) hjp)) HA a ν p.1) p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
          (ϱ := ϱ) (j + 1) hjp)) HA a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HA a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small HA (Sol p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small HA (Sol p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds HA (Sol p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small HA δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
            (ϱ := ϱ) (j + 1) hjp)) HA a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HA a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁)
        (k := K) (ϱ := ϱ) (j + 1) hjp)) × Edat HB N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM HB N ιU δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi HB (Dec2.decG (coverOf (levelGS (d := d) (L := L) (N₁ := N₁')
          (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjp)) HB a ν p.1) p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
          (ϱ := ϱ) (j + 1) hjp)) HB a ν p.1 ιU p.2.2.1 p.2.1
          (pertSource HB a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small HB (Sol' p).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
        Small HB (Sol' p).2 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        SupBounds HB (Sol' p).1 (cK2' d L N (famConst d L BG κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small HB δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
            (ϱ := ϱ) (j + 1) hjp)) HB a ν p.1 ιU p.2.2.1 p.2.1
            (pertSource HB a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {s : Dec2.DecParams (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp))}
    {s' : Dec2.DecParams (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp))}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {e : Edat HA N} {e' : Edat HB N}
    (he : StrictDataM HA N ιU δ₀ δ₁ e) (he' : StrictDataM HB N ιU δ₀ δ₁ e')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} {A' : Finset (ℕ × CTorus d L N₁' m₁ K)}
    (hY : Dec2.IsIncUnion (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp)) HA a ν X₁ 𝒞 Y A)
    (hYc : Dec2.IsIncUnion (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
      (ϱ := ϱ) (j + 1) hjp)) HB a ν (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm) A')
    (hs0 : ∀ P ∈ (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ)
      (j + 1) hjp)).parCubes X₁, P ∉ 𝒞 → Dec2.extS _ s P = 0)
    (hs0' : ∀ P ∈ (coverOf (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ)
      (j + 1) hjp)).parCubes (X₁.image bm), P ∉ 𝒞.image (Prod.map id bm) → Dec2.extS _ s' P = 0)
    {R : ℕ} (hXR : ∀ x ∈ X₁, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hCR : ∀ P ∈ 𝒞, InBox d R ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hsP : ∀ P ∈ cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ)
        (j + 1) hjp),
      InBox d (R + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁))
        ((N₁ * L ^ m₁) * L ^ K) P.2 → Dec2.extS _ s' (Prod.map id bm P) = Dec2.extS _ s P)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hnS : 2 * (R + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (j + 1)) < (N₁ * L ^ m₁) * L ^ K)
    (hnS' : 2 * (R + (3 * L ^ (j + 1 + m₁) + 3 * L ^ (j + 1 + 2)) + L ^ (j + 1 + m₁)) +
      5 * (L * cellSide L 0 m₁ (j + 1)) < (N₁' * L ^ m₁) * L ^ K)
    (hf : 2 * (R + 3 * L ^ (j + 1 + m₁) + L ^ j) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hf' : 2 * (R + 3 * L ^ (j + 1 + m₁) + L ^ j) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hαB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF (coverOf (levelGS (d := d)
        (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjp)) HA a ν X₁ 𝒞 Y →
      e.2.1 x = e'.2.1 (ιb x))
    (hφR : ∀ y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF (coverOf (levelGS (d := d) (L := L)
        (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjp)) HA a ν X₁ 𝒞 Y),
      e.1 y = e'.1 (bm y))
    (hΨB : ∀ x ∈ Dec2.SYF (coverOf (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
        (ϱ := ϱ) (j + 1) hjp)) HA a ν X₁ 𝒞 Y, e.2.2.1 x = e'.2.2.1 (bm x))
    (hfB : ∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF (coverOf (levelGS (d := d)
        (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjp)) HA a ν X₁ 𝒞 Y →
      ∀ i : Fin N, e.2.2.2 (x, i) = e'.2.2.2 (ιb x, i)) :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF (coverOf (levelGS (d := d) (L := L)
        (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) (j + 1) hjp)) HA a ν X₁ 𝒞 Y →
      (Sol' (s', e')).2 (ιb x) = (Sol (s, e)).2 x) ∧
    (∀ y : (HA).Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      (Sol' (s', e')).1 (ιb y, i) = (Sol (s, e)).1 (y, i)) :=
  decSol_value_twoTorus hj1 hj hjp hF SA SB hκ hM ιU h0 h1 hδ₀ hδ₁ hSol hSol' hs hs' he he' hY
    hYc hs0 hs0' rfl (SYF_image hj1 hj hjp a ν hnS hnS' hf hf' hXR hCR hYR)
    (hagree2_boxMap hj1 hj hjp hnS hnS' (SYF_subset_levelGS hj1 hj hjp) hYR hsP) hYR hn hn' hαB
    hφR hΨB hfB

/-! #### D5: the data of the fluctuation from the background comparison -/

include hj1 in
/-- The residual sites of `levelGS j` at a site lie among those of `levelGS (j + 1)`: the site,
its nearest neighbours, and its `j`-block, which lies in its `(j + 1)`-block. -/
theorem resSites_levelGS_subset_succ (x : CTorus d L N₁ m₁ K) :
    resSites HA x ⊆ resSites PA x := by
  intro y hy
  unfold resSites at hy ⊢
  rw [layerIndex_levelGS hj1 hj] at hy
  rw [layerIndex_levelGS (by omega) hjp]
  simp only [Finset.mem_insert, Finset.mem_union, GeneratingSet.mem_blk] at hy ⊢
  rcases hy with h | (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl (Balaban.Background.jBlock_mono (by omega) hjp h)))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr h)

include hj1 in
/-- **`S_Y^F ⊆ S_Y` for the step pair** (general `K`; the landed `SYF_subset_SY_level` has
`K = k + 1`).  For a union `Y` of nearest-neighbour components of `V(𝒞) ∩ Ω₁` of the background
generating set `levelGS (j + 1)`, the block set `S_Y^F` of the fluctuation pair
`(coverOf (levelGS (j + 1)), levelGS j)` lies in the block set `S_Y` of the background. -/
theorem SYF_subset_SY_levelGS {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting PA a ν) (hconn : HatConn PA)
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (PA).Ω 1) Y)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y) : x ∈ SY PA X₁ 𝒞 Y :=
  SYF_subset_SY (Dec2.coverLocal_self S) hconn
    (fun b _ => levelGS_mem_Ω_one (by omega) hjp b) hY hx

include hj1 in
/-- **The row sites of `S_Y^F` read only background data in `RowsDep (S_Y)`.**  Under the
hypotheses of `SYF_subset_SY_levelGS`, a site `y` of `R(S_Y^F)` (the rows of the operator of level
`j` at the sites of `S_Y^F`) lies in `Y`, and the approximate field of the background at `y` reads
the raw data only on `RowsDep (S_Y)`: `y` is a residual site of `levelGS (j + 1)` at a site of
`S_Y^F ⊆ S_Y`. -/
theorem RowF_SYF_rowsDep {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting PA a ν) (hconn : HatConn PA)
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (PA).Ω 1) Y)
    {y : CTorus d L N₁ m₁ K} (hy : y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y)) :
    y ∈ Y ∧ ∀ z ∈ approxDep PA y, RowsDep PA a ν (SY PA X₁ 𝒞 Y) z := by
  classical
  refine ⟨Dec2.RowsFl.RowF_SYF_subset_Y hy, fun z hz => ?_⟩
  unfold Dec2.RowsFl.RowF at hy
  obtain ⟨-, x, hx, hyx⟩ := Finset.mem_filter.1 hy
  have hres : y ∈ resSites HA (x : CTorus d L N₁ m₁ K) := by
    rcases hyx with rfl | ⟨w, hw, rfl⟩
    · exact mem_resSites_self _
    · exact mem_resSites_of_entry_ne_zero hw
  have hxS := SYF_subset_SY_levelGS hj1 hj hjp S hconn hY hx
  exact Or.inl ⟨⟨x, levelGS_mem_Ω_one (by omega) hjp _⟩, hxS,
    approxDep_subset_resDep (resSites_levelGS_subset_succ hj1 hj hjp _ hres) hz⟩

include hj1 in
/-- **D5: the data of the fluctuation problem from the background comparison.**  Let `(φ, α)`,
`(φ', α')` be the decoupled background fields (`IsDecBg` in the ball `ρ₄`) of the background
generating set `levelGS (j + 1)` on the two tori, under the hypotheses of the landed
`decBg_component_unique` (at level `j + 1`; `Y` a union of nearest-neighbour components of
`V(𝒞) ∩ Ω₁`, data agreeing on `RowsDep (S_Y)`).  Then the data of the fluctuation problem of the
pair `(coverOf (levelGS (j + 1)), levelGS j)` built from them (`flEdat`: base potential
`flAlpha α`, base field `barField Ψ φ`) correspond as `decSol_rows_transport` asks: the base
potential on `S_Y^F` (because `S_Y^F ⊆ S_Y`, `SYF_subset_SY_levelGS`) and the base field on
`R(S_Y^F)` (because `R(S_Y^F) ⊆ Y` and the background field at these sites reads only the data on
`RowsDep (S_Y)`, `RowF_SYF_rowsDep`).  No data beyond `RowsDep (S_Y)` is needed. -/
theorem decSol_data_of_decBg {c BG : ℝ} (hS : DecSpecs d L c BG) {a : ℕ → ℝ} {ν : ℝ}
    (SA : DGSetting PA a ν) (SB : DGSetting PB a ν) (hconn : HatConn PA)
    (hconn' : HatConn PB) (HBg : BgHyp d L K ϱp a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams PA} {s' : DecParams PB} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δ ε δ' ε' : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hδ0' : 0 < δ') (hδε' : δ' ≤ ε')
    (hε' : ε' ≤ bgC0 d L N) (hδ' : δ' ≤ c7 d L N BG κ)
    (hνε' : ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2)
    {D : BgData PA N} {D' : BgData PB N} (hDd : InDomainC PA ν δ ε D)
    (hDd' : InDomainC PB ν δ' ε' D')
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞' : Finset (ℕ × CTorus d L N₁' m₁ K)} {X₁' Y' : Finset (CTorus d L N₁' m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ (PA).Ω 1) Y)
    (hYc : IsNnComp ((Vset X₁' 𝒞').filter fun x => x ∈ (PB).Ω 1) Y')
    (hs0 : ∀ P ∈ parCubes PA X₁, P ∉ 𝒞 → extS PA s P = 0)
    (hs0' : ∀ P ∈ parCubes PB X₁', P ∉ 𝒞' → extS PB s' P = 0)
    (hY' : Y.image bm = Y') (hB' : (SY PA X₁ 𝒞 Y).image bm = SY PB X₁' 𝒞' Y')
    (hagree : ∀ q ∈ innerCentres PA (SY PA X₁ 𝒞 Y),
      sProd PB (extS PB s') (Prod.map id bm q) = sProd PA (extS PA s) q)
    {R : ℕ} (hYR : ∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 4 * R + 12 * L ^ (j + 1 + m₁) + 7 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hD : RawBoxAgree {z | RowsDep PA a ν (SY PA X₁ 𝒞 Y) z} (rawOf D) (rawOf D'))
    {φ : (PA).Ω 1 × Fin N → ℂ} {α : (PA).Ω 1 → ℂ} {φ' : (PB).Ω 1 × Fin N → ℂ}
    {α' : (PB).Ω 1 → ℂ} (h : IsDecBg PA a ν (rho4 d L N BG κ) s D φ α)
    (h' : IsDecBg PB a ν (rho4 d L N BG κ) s' D' φ' α') :
    (∀ x : (HA).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF CA HA a ν X₁ 𝒞 Y →
      flAlpha PA HA α x = flAlpha PB HB α' (ιb x)) ∧
    (∀ y ∈ Dec2.RowsFl.RowF HA a ν (Dec2.SYF CA HA a ν X₁ 𝒞 Y),
      barField PA D.Ψ φ y = barField PB D'.Ψ φ' (bm y)) := by
  obtain ⟨h1, -, h3, -⟩ := decBg_component_unique (by omega) hjp hS SA SB hconn hconn' HBg hκ hM
    hs hs' hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hDd hDd' hY hYc hs0 hs0' hY' hB' hagree hYR
    hn hn' hD h h'
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have hxS := SYF_subset_SY_levelGS hj1 hj hjp SA hconn hY hx
    have e1 := h1 ⟨x, levelGS_mem_Ω_one (by omega) hjp _⟩ hxS
    simp only [flAlpha, levelGS_mem_Ω_one (by omega) hjp, dite_true]
    exact e1.symm
  · obtain ⟨hyY, hdep⟩ := RowF_SYF_rowsDep hj1 hj hjp SA hconn hY hy
    funext i
    have e3 := h3 ⟨y, levelGS_mem_Ω_one (by omega) hjp _⟩ hyY (fun z hz => hD z (hdep z hz)) i
    simp only [barField, levelGS_mem_Ω_one (by omega) hjp, dite_true]
    exact e3.symm

end Corollaries

end Balaban.Polymer.TwoTorusStep
