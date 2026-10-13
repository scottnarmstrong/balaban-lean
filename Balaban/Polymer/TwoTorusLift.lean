/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusDecCov
public import Balaban.Fluctuation.InteractionHatV
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Free blocks and the unit-point lift on two tori

For the top level `levelGS (k + 1)` of two fine tori identified on a centred box by `boxMap`
(`bm` on the fine tori, `bU` on the unit lattices):

* `coreBox_base_inBox`, `mem_coreBox_boxMap_iff`: the cube `C_z` of a centre `z` in centred
  coordinates, and its base point;
* `core_boxMap_iff`: a site `y` of the box lies in `Core(s)` iff `bm y` lies in `Core(s')`, when the
  parameters correspond on the cubes whose base point lies in a slightly larger box;
* `freeBlk_boxMap`: the free-block condition `FreeBlk` of a unit point corresponds under the box
  maps; `decCov_rows_transport_free'` is `decCov_rows_transport_free` with the premise `hfree'`
  removed;
* `liftC_boxMap`, `hatLift_boxMap`: the lift to the fine torus of a unit-point field corresponds.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### The cube `C_z` in centred coordinates -/

section Core

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

omit [NeZero N₁'] in
/-- The base point of a centre whose cube `C_z` contains a site of the box of radius `ρ₀` lies in
the box of radius `ρ₀ + 2 L^(j+m₁)`. -/
theorem coreBox_base_inBox {ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hn : 2 * (ρ₀ + 2 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hx : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) x)
    (h : x ∈ coreBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) :
    InBox d (ρ₀ + 2 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) y0 := by
  unfold coreBox at h
  rw [mem_boxSet] at h
  intro μ
  obtain ⟨p, hp⟩ := h μ
  obtain ⟨k1, hk1⟩ := dvd_valMinAbs_sub_val (x μ)
  have hP : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  simp only at hp
  set n : ℕ := (N₁ * L ^ m₁) * L ^ K with hnn
  have hk1r : ((x μ).valMinAbs : ℝ) - (x μ).val = (n : ℝ) * k1 := by exact_mod_cast hk1
  have hxr : |((x μ).valMinAbs : ℝ)| ≤ ρ₀ := by exact_mod_cast hx μ
  let t : ℤ := ((y0 μ).val : ℤ) - (p - k1) * (n : ℤ)
  have htc : ((t : ℤ) : ZMod n) = y0 μ := by
    simp [t]
  have htr : (t : ℝ) = ((y0 μ).val : ℝ) - (p - k1) * n := by
    simp only [t]; push_cast; ring
  refine inBox_of_int hn _ t htc ?_
  have h1 : |(t : ℝ)| ≤ ((ρ₀ + 2 * L ^ (j + m₁) : ℕ) : ℝ) := by
    rw [abs_lt] at hp
    rw [abs_le] at hxr ⊢
    push_cast
    constructor <;> nlinarith [hp.1, hp.2, hxr.1, hxr.2]
  exact_mod_cast h1

/-- **The cube `C_z` of a centre, on two tori.**  For `y0` in the box of radius `ρ₀`, a site of the
box of radius `ρ₀ + (3 L^(j+m₁) + 3 L^(j+2))` lies in `C_z` iff its image lies in `C` of the image
centre.  Margin: `2 (ρ₀ + 3 L^(j+m₁) + 3 L^(j+2)) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem mem_coreBox_boxMap_iff {ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (hx : InBox d (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K) x) :
    x ∈ coreBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      bm x ∈ coreBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) :=
    inBox_boxMap (by omega) hy0
  have hP : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hP2 : (0 : ℝ) ≤ (L : ℝ) ^ (j + 2) := by positivity
  have hE : (ρ₀ : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2 + 3 / 2 * (L : ℝ) ^ (j + m₁) ≤
      ((ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2)) : ℕ) : ℝ) := by
    push_cast; linarith
  have key : ∀ {m : ℕ} [NeZero m] (z : CTorus d L m m₁ K) (hz : InBox d ρ₀ (m * L ^ m₁ * L ^ K) z),
      2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (m * L ^ m₁) * L ^ K →
      ∀ w : CTorus d L m m₁ K, w ∈ coreBox ((j, z) : ℕ × CTorus d L m m₁ K) ↔
        InBox d (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((m * L ^ m₁) * L ^ K) w ∧
          ∀ μ, |((w μ).valMinAbs : ℝ) - (z μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2| <
            3 / 2 * (L : ℝ) ^ (j + m₁) := by
    intro m _ z hz hnm w
    unfold coreBox
    rw [mem_boxSet]
    exact inBoxR_iff hz hnm hE
  rw [key _ hy0 hn, key _ hy0' hn']
  have hy1 := valMinAbs_boxMap (m' := (N₁' * L ^ m₁) * L ^ K) (by omega : 2 * ρ₀ + 1 < _) hy0
  have hR : ∀ μ, (bm x μ).valMinAbs = (x μ).valMinAbs := valMinAbs_boxMap hn' hx
  constructor
  · rintro ⟨-, h2⟩
    refine ⟨inBox_boxMap hn' hx, fun μ => ?_⟩
    rw [hR μ, hy1 μ]; exact h2 μ
  · rintro ⟨-, h2⟩
    refine ⟨hx, fun μ => ?_⟩
    have := h2 μ
    rw [hR μ, hy1 μ] at this; exact this

end Core

/-! ### The core of the cut weights on two tori -/

section CoreImage

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
variable (hj1 : 1 ≤ j) (hj : j ≤ K)
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "ρ₁" ρ => ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2)) + L ^ (j + m₁)
local notation "cs" => L * cellSide L 0 m₁ j

include hj1 in
/-- **The cut weights agree at the centres of the box** when the parameters correspond on the
cubes whose base point lies in the box of radius `ρ₁`. -/
theorem sProd_eq_of_agree {ρ : ℕ}
    (hn : 2 * (ρ₁ ρ) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁ ρ) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ cubeIdx GA, InBox d (ρ₁ ρ) ((N₁ * L ^ m₁) * L ^ K) P.2 →
      s' (Prod.map id bm P) = s P)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx GA)
    (hq0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) q.2) :
    sProd GB s' (Prod.map id bm q) = sProd GA s q := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hq
  refine sProd_boxMap hj1 hj hn hn' hq hq0 fun P hP => hs P (Qset_subset_cubeIdx _ hP) ?_
  obtain ⟨y1, rfl, -, hy1⟩ := qset_base_inBox (ϱ := ϱ) hj (by omega) hq0 hP
  exact hy1

include hj1 in
/-- **A site of the box lies in `Core(s)` iff its image lies in `Core(s')`.**  The site is in the
box of radius `r`, `r + 2 L^(j+m₁) ≤ ρ`, and the parameters correspond on the cubes whose base
point lies in the box of radius `ρ₁ = ρ + (3 L^(j+m₁) + 3 L^(j+2)) + L^(j+m₁)`.  Margin:
`2 ρ₁ + 5 L · cellSide L 0 m₁ j < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem core_boxMap_iff {ρ r : ℕ} (hρ : r + 2 * L ^ (j + m₁) ≤ ρ)
    (hn : 2 * (ρ₁ ρ) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁ ρ) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ cubeIdx GA, InBox d (ρ₁ ρ) ((N₁ * L ^ m₁) * L ^ K) P.2 →
      s' (Prod.map id bm P) = s P)
    {y : CTorus d L N₁ m₁ K} (hy : InBox d r ((N₁ * L ^ m₁) * L ^ K) y) :
    y ∈ Core GA s ↔ bm y ∈ Core GB s' := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hE : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hE' : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁' * L ^ m₁) * L ^ K := by
    omega
  have hyρ : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y := inBox_mono (by omega) hy
  have hyE : InBox d (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K) y :=
    inBox_mono (by omega) hyρ
  have hy' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm y) := inBox_boxMap (by omega) hyρ
  have hf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := K)
    (ρ := ρ) (ϱ := ϱ) hj1 hj (by omega) (by omega)
  unfold Core
  constructor
  · intro h
    obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.1 h
    obtain ⟨hzc, hzs⟩ := Finset.mem_filter.1 hz
    obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hzc
    have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 :=
      inBox_mono hρ (coreBox_base_inBox (by omega) hy hyz)
    have hsp := sProd_eq_of_agree hj1 hj hn hn' hs hzc hy0
    have hzB : Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ∈ cubeIdx GB := by
      have hm : Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ∈
          (cubeIdx GB).filter (fun q => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2) := by
        rw [hf]
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hzc, hy0⟩)
      exact (Finset.mem_filter.1 hm).1
    refine Finset.mem_biUnion.2 ⟨Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K),
      Finset.mem_filter.2 ⟨hzB, ?_⟩, ?_⟩
    · rw [hsp]; exact hzs
    · exact (mem_coreBox_boxMap_iff hy0 hE hE' hyE).1 hyz
  · intro h
    obtain ⟨z', hz', hyz'⟩ := Finset.mem_biUnion.1 h
    obtain ⟨hz'c, hz's⟩ := Finset.mem_filter.1 hz'
    obtain ⟨y1, rfl, hb1⟩ := exists_of_mem_cubeIdx hj hz'c
    have hy1 : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) y1 :=
      inBox_mono hρ (coreBox_base_inBox (by omega) (inBox_boxMap (by omega) hy) hyz')
    have hmem : ((j, y1) : ℕ × CTorus d L N₁' m₁ K) ∈
        (cubeIdx GB).filter (fun q => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2) :=
      Finset.mem_filter.2 ⟨hz'c, hy1⟩
    rw [hf] at hmem
    obtain ⟨q0, hq0m, hq0e⟩ := Finset.mem_image.1 hmem
    obtain ⟨hq0c, hq0b⟩ := Finset.mem_filter.1 hq0m
    obtain ⟨y2, rfl, hb2⟩ := exists_of_mem_cubeIdx hj hq0c
    have hbm : bm y2 = y1 := congrArg Prod.snd hq0e
    have hsp := sProd_eq_of_agree hj1 hj hn hn' hs hq0c hq0b
    have hsp' : sProd GB s' ((j, y1) : ℕ × CTorus d L N₁' m₁ K) =
        sProd GA s ((j, y2) : ℕ × CTorus d L N₁ m₁ K) := by
      rw [← hq0e]; exact hsp
    refine Finset.mem_biUnion.2 ⟨(j, y2), Finset.mem_filter.2 ⟨hq0c, ?_⟩, ?_⟩
    · rw [← hsp']; exact (Finset.mem_filter.1 hz').2
    · refine (mem_coreBox_boxMap_iff hq0b hE hE' hyE).2 ?_
      rw [hbm]; exact hyz'

end CoreImage

/-! ### The free-block condition on two tori -/

section Top

open MeasureTheory Set

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bU" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) ((N₁' * L ^ m₁) * L ^ (k + 1 - k))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ιu" b:max => Subtype.mk (bU (b : UnitTorus d L N₁ m₁ k))
  (mem_unitPts_levelTop (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (ϱ := ϱ) _)
set_option hygiene false in
local notation "ρ₀" R => R + L ^ (k + 1) + 2 * L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "ρ₁" R => (R + L ^ (k + 1) + 2 * L ^ (k + 1 + m₁)) +
  (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "cs" => L * cellSide L 0 m₁ (k + 1)

omit [NeZero N₁] in
/-- **The margin of the free-block condition implies the margins of the unit lattice.** -/
theorem freeBlk_margin {R : ℕ}
    (hn : 2 * (ρ₁ R) + 5 * cs < (N₁ * L ^ m₁) * L ^ (k + 1)) :
    2 * R + 5 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (k + 1)
  have hK : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have h2 : 1 ≤ L ^ (k + 1 + 2) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have h3 : cellSide L 0 m₁ (k + 1) = L ^ (k + 1 + m₁) := cellSide_zero
  omega

/-- **The free-block condition on two tori.**  Let `xb` be a site of the box of radius `R` in the
`(k+1)`-block of the unit point `b`.  If the parameters `s`, `s'` correspond on the cubes whose
base point lies in the box of radius `ρ₁ = R + L^(k+1) + 2 L^(k+1+m₁) + (3 L^(k+1+m₁) +
3 L^(k+1+2)) + L^(k+1+m₁)`, then the `(k+1)`-block of `b` avoids the core of `s` iff the block of
its image `ιu b` avoids the core of `s'`.  Margin: `2 ρ₁ + 5 L · cellSide L 0 m₁ (k+1) <
N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem freeBlk_boxMap {R : ℕ}
    (hn : 2 * (ρ₁ R) + 5 * cs < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ₁ R) + 5 * cs < (N₁' * L ^ m₁) * L ^ (k + 1))
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hs : ∀ P ∈ cubeIdx GA, InBox d (ρ₁ R) ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 →
      s' (Prod.map id bm P) = s P)
    {b : unitPts GA} {xb : CTorus d L N₁ m₁ (k + 1)}
    (hxbR : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) xb)
    (hxb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) xb) :
    FreeBlk GA s s b ↔ FreeBlk GB s' s' (ιu b) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ (k + 1)
  have hK : L ^ (k + 1) ≤ L ^ (k + 1 + m₁) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_add_right _ _)
  have h2 : 1 ≤ L ^ (k + 1 + 2) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have h3 : cellSide L 0 m₁ (k + 1) = L ^ (k + 1 + m₁) := cellSide_zero
  have hnu := freeBlk_margin (N₁ := N₁) (m₁ := m₁) hn
  have hnu' := freeBlk_margin (N₁ := N₁') (m₁ := m₁) hn'
  have hR1 : 2 * (R + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hR1' : 2 * (R + L ^ (k + 1)) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1) := by
    omega
  have hxbR' : InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (bm xb) := inBox_boxMap (by omega) hxbR
  have hx0R := inBox_mono (Nat.le_add_right R (L ^ (k + 1))) hxbR
  have hx0R' := inBox_mono (Nat.le_add_right R (L ^ (k + 1))) hxbR'
  obtain ⟨y0, hy0, hy0x, hy0R⟩ := unit_anchor (ϱ := ϱ) (by omega) hxbR b hxb
  have hιu0 := unitImage_val (N₁' := N₁') hR1 b hy0 hy0R
  have hblk0 : unitBlock1 (((ιu b) : unitPts GB) : UnitTorus d L N₁' m₁ k) =
      jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm xb) := by
    rw [hιu0, unitBlock1_unitBlock]
    exact (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hy0R hx0R).1 hy0x
  have hcore : ∀ y : CTorus d L N₁ m₁ (k + 1),
      InBox d (R + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) y →
        (y ∈ Core GA s ↔ bm y ∈ Core GB s') := fun y hy =>
    core_boxMap_iff (ϱ := ϱ) (j := k + 1) (K := k + 1) (Nat.le_add_left 1 k) le_rfl
      (r := R + L ^ (k + 1)) le_rfl hn hn' hs hy
  constructor
  · intro hF y' hy'
    rw [unitBlock1_unitBlock] at hy'
    have hy'' : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (y' : CTorus d L N₁' m₁ (k + 1)) =
        jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm xb) := hy'.trans hblk0
    have hy'R := inBox_of_jBlock_eq (m := k + 1) le_rfl (by omega) hxbR' hy''
    have hback : bm (bm' (y' : CTorus d L N₁' m₁ (k + 1))) = y' := boxMap_boxMap (by omega) hy'R
    have hyR : InBox d (R + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
        (bm' (y' : CTorus d L N₁' m₁ (k + 1))) := inBox_boxMap (by omega) hy'R
    have hjb : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) (bm' (y' : CTorus d L N₁' m₁ (k + 1))) =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) xb := by
      refine (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hyR hx0R).2 ?_
      rw [hback]; exact hy''
    obtain ⟨c1, -⟩ := hF ⟨bm' (y' : CTorus d L N₁' m₁ (k + 1)),
      levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl _⟩ (by
        show unitBlock1 (unitBlock (bm' (y' : CTorus d L N₁' m₁ (k + 1)))) = _
        rw [unitBlock1_unitBlock, hjb, hxb])
    have hn1 : (y' : CTorus d L N₁' m₁ (k + 1)) ∉ Core GB s' := by
      intro h
      apply c1
      refine (hcore _ hyR).2 ?_
      rw [hback]; exact h
    exact ⟨hn1, hn1⟩
  · intro hF y hy
    rw [unitBlock1_unitBlock, hxb] at hy
    have hyR := inBox_of_jBlock_eq (m := k + 1) le_rfl (by omega) hxbR hy
    have hjb : jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm (y : CTorus d L N₁ m₁ (k + 1))) =
        jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bm xb) :=
      (jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hR1 hR1' hyR hx0R).1 hy
    obtain ⟨c1, -⟩ := hF ⟨bm (y : CTorus d L N₁ m₁ (k + 1)),
      levelGS_mem_Ω_one (Nat.le_add_left 1 k) le_rfl _⟩ (by
        show unitBlock1 (unitBlock (bm (y : CTorus d L N₁ m₁ (k + 1)))) = _
        rw [unitBlock1_unitBlock, hjb, hblk0])
    have hn1 : (y : CTorus d L N₁ m₁ (k + 1)) ∉ Core GA s :=
      fun h => c1 ((hcore _ hyR).1 h)
    exact ⟨hn1, hn1⟩

/-- **`decCov_rows_transport_free` without the premise `hfree'`.**  At a unit point `b` whose
`(k+1)`-block avoids the core of `s`, the second-torus condition `hfree'` follows from the
agreement of the parameters on the cubes whose base point lies in the box of radius `ρ₁`
(`freeBlk_boxMap`).  The margin of `freeBlk_boxMap` replaces `hnu`, `hnu'`. -/
theorem decCov_rows_transport_free' {a : ℕ → ℝ} {aT x₀ ν : ℝ} {α : (GA).Ω 1 → ℂ}
    {α' : (GB).Ω 1 → ℂ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    {s' : ℕ × CTorus d L N₁' m₁ (k + 1) → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ} {R : ℕ}
    (hn : 2 * (ρ₁ R) + 5 * cs < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (ρ₁ R) + 5 * cs < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hs : ∀ P ∈ cubeIdx GA, InBox d (ρ₁ R) ((N₁ * L ^ m₁) * L ^ (k + 1)) P.2 →
      s' (Prod.map id bm P) = s P)
    {b : unitPts GA} {xb : CTorus d L N₁ m₁ (k + 1)}
    (hxbR : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) xb)
    (hxb : unitBlock1 (b : UnitTorus d L N₁ m₁ k) = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) xb)
    (hfree : FreeBlk GA s s b)
    (h : unitPts GA × Fin N → ℂ) (h' : unitPts GB × Fin N → ℂ)
    (hh : ∀ b3 : unitPts GA, unitBlock1 (b3 : UnitTorus d L N₁ m₁ k) =
      unitBlock1 (b : UnitTorus d L N₁ m₁ k) → ∀ i, h' (ιu b3, i) = h (b3, i)) (i : Fin N) :
    (decCov GB a aT x₀ ν α' s' φ' (unitQ GB) (unitP GB) *ᵥ h') (ιu b, i) =
      (decCov GA a aT x₀ ν α s φ (unitQ GA) (unitP GA) *ᵥ h) (b, i) :=
  decCov_rows_transport_free (freeBlk_margin (N₁ := N₁) (m₁ := m₁) hn)
    (freeBlk_margin (N₁ := N₁') (m₁ := m₁) hn') hxbR hxb hfree
    ((freeBlk_boxMap hn hn' hs hxbR hxb).1 hfree) h h' hh i

/-! ### The lift of a unit-point field -/

/-- **The unit point of the image of a site of the box**: `unitPt hGB (bm x) = ιu (unitPt hGA x)`.
Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem unitPt_boxMap {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel GA (k + 1)) (hGB : IsLevel GB (k + 1))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    unitPt hGB (bm x) = ιu (unitPt hGA x) :=
  Subtype.ext (unitBlock_boxMap hn hx)

/-- **The lift of a unit-point field, on two tori.**  If `v' ∘ ιu = v` on the unit point of the
block of a site `x` of the box, then the lifts to the fine tori agree at `x` and at `bm x`:
`(liftC … v') (bm x) = (liftC … v) x`.  Margin: `2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem liftC_boxMap {ρ : ℕ} (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel GA (k + 1)) (hGB : IsLevel GB (k + 1))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {v : unitPts GA × Fin N → ℂ} {v' : unitPts GB × Fin N → ℂ}
    (hv : ∀ i, v' (ιu (unitPt hGA x), i) = v (unitPt hGA x, i)) (i : Fin N) :
    liftC hGB v' (bm x) i = liftC hGA v x i := by
  rw [liftC_apply, liftC_apply, unitPt_boxMap hn hGA hGB hx]
  exact hv i

/-- **The fluctuation of a hat variable on two tori.**  If the rows of `C^{1/2}(1) ψ̂` and
`C'^{1/2}(1) ψ̂'` correspond at the unit point of the block of a site `x` of the box, then
`hatLift` of the two correspond at `x` and `bm x`.  Margin:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)`. -/
theorem hatLift_boxMap {a₁ ν : ℝ} {ρ : ℕ}
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hGA : IsLevel GA (k + 1)) (hGB : IsLevel GB (k + 1)) (cc : ℂ)
    (D : BgData GA N) (D' : BgData GB N)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {ψh : unitPts GA × Fin N → ℂ} {ψh' : unitPts GB × Fin N → ℂ}
    (hrow : ∀ i, (hatCovSqrt GB a₁ ν D' *ᵥ ψh') (ιu (unitPt hGA x), i) =
      (hatCovSqrt GA a₁ ν D *ᵥ ψh) (unitPt hGA x, i)) (i : Fin N) :
    hatLift GB a₁ ν hGB cc D' ψh' (bm x) i = hatLift GA a₁ ν hGA cc D ψh x i := by
  unfold hatLift
  refine liftC_boxMap hn hGA hGB hx (fun i' => ?_) i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hrow i']

end Top

end Balaban.Polymer.TwoTorusStep
