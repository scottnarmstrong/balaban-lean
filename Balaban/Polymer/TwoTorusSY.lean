/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGreenRows
public import Balaban.Polymer.TwoTorusDomainFamilies
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The block set `S_Y` and the cut weights on two tori

For the whole-lattice generating sets `levelGS j` of two step tori identified on a centred box by
`boxMap`, this file shows that the sets of the decoupled comparison correspond:

* `qset_image`: the parameter cubes `𝒬(z)` of a centre in the box;
* `sProd_boxMap`, `sProd_boxMap_extS`: the cut weights `s_z = ∏_{P ∈ 𝒬(z)} s_P` agree when the
  parameters agree on `𝒬(z)`, in particular for parameters transported through the correspondence
  of `ParIdx`;
* `hagree_boxMap`: the agreement of the weights on the centres of `innerCentres` of a set `T` of the box;
* `ZY_image`, `SY_image`: the centres `Z_Y` and the block set `S_Y` of a component `Y` correspond.

Notation of the margins: `ρ` is the radius of the centred box that contains the data; with
`a = L^(j+m₁)` the thickened interaction cube has half-width `hatRad ≤ 3a + 3L^(j+2) - a/2`, and
`ρ₁ = ρ + (3a + 3L^(j+2)) + a` is the radius that contains the base points of all cubes meeting
a thickened cube of a centre in the box.  The margin is `2 ρ₁ + 5 L · cellSide L 0 m₁ j < N₁ L^m₁ L^K`
(and for `N₁'`), where `cellSide L 0 m₁ j = L^(j+m₁)`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background

/-! ### The thickened interaction cube in centred coordinates -/

section OneTorus

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {j : ℕ}

/-- **A periodic box around a centre, in centred coordinates.**  If the base point `y0` is in the
box of radius `ρ₀`, `2 E + 1 < N₁ L^m₁ L^K` and `ρ₀ + (L^(j+m₁) - 1)/2 + R ≤ E`, the periodic box of
half-width `R` around the centre of the cube consists of the sites of the box of radius `E` whose
centred coordinates are within `R` of the centre `y0 + (L^(j+m₁) - 1)/2`. -/
theorem inBoxR_iff {ρ₀ E : ℕ} {R : ℝ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * E + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hE : (ρ₀ : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2 + R ≤ E) :
    Balaban.Localization.InBox m₁ j y0 R x ↔
      InBox d E ((N₁ * L ^ m₁) * L ^ K) x ∧
        ∀ μ, |((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2| < R := by
  have hP : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  set n : ℕ := (N₁ * L ^ m₁) * L ^ K with hnn
  have key : ∀ μ : Fin d,
      (∃ p : ℤ, |((x μ).val : ℝ) + p * (n : ℝ) - (((y0 μ).val : ℝ) +
        ((L : ℝ) ^ (j + m₁) - 1) / 2)| < R) ↔
      (|(x μ).valMinAbs| ≤ (E : ℤ) ∧ |((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs -
        ((L : ℝ) ^ (j + m₁) - 1) / 2| < R) := by
    intro μ
    obtain ⟨k0, hk0⟩ := dvd_valMinAbs_sub_val (y0 μ)
    obtain ⟨k1, hk1⟩ := dvd_valMinAbs_sub_val (x μ)
    have hk0r : ((y0 μ).valMinAbs : ℝ) - (y0 μ).val = n * k0 := by exact_mod_cast hk0
    have hk1r : ((x μ).valMinAbs : ℝ) - (x μ).val = n * k1 := by exact_mod_cast hk1
    have hy1 : |((y0 μ).valMinAbs : ℝ)| ≤ ρ₀ := by exact_mod_cast hy0 μ
    constructor
    · rintro ⟨p, hp⟩
      set t : ℤ := ((x μ).val : ℤ) + (p + k0) * (n : ℤ) with ht
      have htc : ((t : ℤ) : ZMod n) = x μ := by
        rw [ht]; push_cast; simp [hnn]
      have htr : (t : ℝ) = (x μ).val + (p + k0) * n := by rw [ht]; push_cast; ring
      have hc0 : (0 : ℝ) ≤ ((L : ℝ) ^ (j + m₁) - 1) / 2 := by linarith
      have hb1 : |(t : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2| < R := by
        have : (t : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2 =
            ((x μ).val : ℝ) + p * n - (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) := by
          rw [htr]; linear_combination (-1) * hk0r
        rw [this]; exact hp
      have hbt : |t| ≤ (E : ℤ) := by
        have h1 : |(t : ℝ)| ≤ E := by
          rw [abs_lt] at hb1
          rw [abs_le] at hy1 ⊢
          constructor <;> linarith [hb1.1, hb1.2, hy1.1, hy1.2]
        exact_mod_cast h1
      have hvm : (x μ).valMinAbs = t := by
        rw [← htc]
        exact valMinAbs_intCast_of_abs_le (r := E) hn hbt
      rw [hvm]
      exact ⟨hbt, hb1⟩
    · rintro ⟨-, hb⟩
      refine ⟨k1 - k0, ?_⟩
      have : ((x μ).val : ℝ) + ((k1 - k0 : ℤ) : ℝ) * n - (((y0 μ).val : ℝ) +
          ((L : ℝ) ^ (j + m₁) - 1) / 2) = ((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs -
          ((L : ℝ) ^ (j + m₁) - 1) / 2 := by
        push_cast
        linear_combination (-1) * hk1r + hk0r
      rw [this]; exact hb
  unfold Balaban.Localization.InBox Balaban.Polymer.InBox
  rw [← forall_and]
  exact forall_congr' fun μ => key μ

theorem hatRad_add_le {ρ₀ : ℕ} :
    (ρ₀ : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2 + hatRad L m₁ j ≤
      ((ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2)) : ℕ) : ℝ) := by
  unfold hatRad
  have hP : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have h2 : (L : ℝ) ^ 2 * (L : ℝ) ^ j = (L : ℝ) ^ (j + 2) := by ring
  push_cast
  nlinarith [h2]

/-- **The thickened interaction cube in centred coordinates.**  For `y0` in the box of radius `ρ₀`
and `2 (ρ₀ + 3 L^(j+m₁) + 3 L^(j+2)) + 1 < N₁ L^m₁ L^K`, the thickened cube `□̂_z` of the centre
`z = (j, y0)` consists of the sites of the box of radius `ρ₀ + 3 L^(j+m₁) + 3 L^(j+2)` whose centred
coordinates are within `hatRad` of the centre `y0 + (L^(j+m₁) - 1)/2`. -/
theorem mem_hatBox_iff {ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K) :
    x ∈ hatBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      InBox d (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K) x ∧
        ∀ μ, |((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2| <
          hatRad L m₁ j := by
  unfold hatBox
  rw [mem_boxSet]
  exact inBoxR_iff hy0 hn hatRad_add_le

/-- The parameter cubes `𝒬(z)`: the centres of the cover whose patch meets `□̂_z`. -/
theorem mem_Qset_hat {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {q q' : ℕ × CTorus d L N₁ m₁ K} :
    q' ∈ Qset G q ↔ q' ∈ cubeIdx G ∧ ∃ y, y ∈ Pset m₁ q' ∧ y ∈ hatBox q := by
  rw [mem_Qset]
  simp only [hatBox, mem_boxSet]
  exact Iff.rfl

/-- A site of the patch of a centre of the box lies in a slightly larger box. -/
theorem pset_inBox {y1 : CTorus d L N₁ m₁ K} (hj : j ≤ K) (hb : CubeBase (K := K) m₁ j y1)
    {r : ℕ} (hy1 : InBox d r ((N₁ * L ^ m₁) * L ^ K) y1)
    (hn : 2 * (r + L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : x ∈ Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K)) :
    InBox d (r + L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x := by
  rw [pset_eq_box hj hb] at hx
  exact inBox_of_mem_box_right hn hy1 hx

/-- **The base points of the parameter cubes.**  A cube of `𝒬(z)` for a centre `z = (j, y0)` of the
box of radius `ρ₀` is a centre `(j, y1)` of `levelGS j` whose base point lies in the box of radius
`ρ₀ + (3 L^(j+m₁) + 3 L^(j+2)) + L^(j+m₁)`. -/
theorem qset_base_inBox (hj : j ≤ K) {ρ₀ : ℕ}
    (hn : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2)) + L ^ (j + m₁)) + 1 <
      (N₁ * L ^ m₁) * L ^ K)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    {q' : ℕ × CTorus d L N₁ m₁ K}
    (hq' : q' ∈ Qset (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) :
    ∃ y1, q' = (j, y1) ∧ CubeBase (K := K) m₁ j y1 ∧
      InBox d (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2)) + L ^ (j + m₁))
        ((N₁ * L ^ m₁) * L ^ K) y1 := by
  obtain ⟨hc, y, hyP, hyH⟩ := mem_Qset_hat.1 hq'
  obtain ⟨y1, rfl, hb⟩ := exists_of_mem_cubeIdx hj hc
  have hyE := ((mem_hatBox_iff (j := j) hy0 (by omega)).1 hyH).1
  rw [pset_eq_box hj hb] at hyP
  exact ⟨y1, rfl, hb, inBox_of_mem_box_left hn hyE hyP⟩

/-- The base point of a centre of `Z_Y` lies in `Y`, since it lies in its thickened cube. -/
theorem ZY_base_mem (hj1 : 1 ≤ j) (hj : j ≤ K) {X₁ : Finset (CTorus d L N₁ m₁ K)}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {Y : Finset (CTorus d L N₁ m₁ K)}
    {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : z ∈ ZY (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
      X₁ 𝒞 Y) : z.2 ∈ Y := by
  have h := (Finset.mem_filter.1 hz).2.2
  exact h ⟨z.2, levelGS_mem_Ω_one hj1 hj z.2⟩ (box_subset_hatBox z (base_mem_intBox z))

/-- For `levelGS j`, `Ω₁` is the whole torus. -/
theorem subI_levelGS_iff (hj1 : 1 ≤ j) (hj : j ≤ K) {B Y : Finset (CTorus d L N₁ m₁ K)} :
    SubI (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) B Y ↔
      ∀ x, x ∈ B → x ∈ Y :=
  ⟨fun h x hx => h ⟨x, levelGS_mem_Ω_one hj1 hj x⟩ hx, fun h _x hx => h _ hx⟩

end OneTorus


/-! ### Two tori -/

section TwoTori

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
variable (hj1 : 1 ≤ j) (hj : j ≤ K)
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj

omit [NeZero N₁'] [NeZero L] in
theorem cellSide_zero : cellSide L 0 m₁ j = L ^ (j + m₁) := by
  unfold cellSide; rfl

/-- **The thickened interaction cube, on two tori.**  For `y0` in the box of radius `ρ₀`, a site of
the box of radius `ρ₀ + (3 L^(j+m₁) + 3 L^(j+2))` lies in `□̂_z` iff its image lies in `□̂` of the
image centre.  Margin: `2 (ρ₀ + 3 L^(j+m₁) + 3 L^(j+2)) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem mem_hatBox_boxMap_iff {ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (hx : InBox d (ρ₀ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K) x) :
    x ∈ hatBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      bm x ∈ hatBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) :=
    inBox_boxMap (by omega) hy0
  rw [mem_hatBox_iff hy0 hn, mem_hatBox_iff hy0' hn']
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

section Margin

variable {ρ : ℕ}

local notation "ρ₁" => ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2)) + L ^ (j + m₁)
local notation "cs" => L * cellSide L 0 m₁ j

include hj1 in
/-- The membership `(j, y1) ∈ 𝒬(j, y0)` on the first torus is equivalent to the membership of the
image centres on the second torus.  Margin: `2 ρ₁ + 5 L · cellSide L 0 m₁ j < N₁ L^m₁ L^K`
(and for `N₁'`). -/
theorem qset_mem_iff
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {y0 y1 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hb1 : CubeBase (K := K) m₁ j y1) (hy1 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) y1) :
    ((j, y1) : ℕ × CTorus d L N₁ m₁ K) ∈ Qset GA ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) ∈ Qset GB ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hqA : ((j, y1) : ℕ × CTorus d L N₁ m₁ K) ∈ cubeIdx GA :=
    (mem_cubeIdx_levelGS hj _).2 ⟨rfl, hj1, hb1⟩
  have hqB : ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) ∈ cubeIdx GB :=
    (mem_cubeIdx_levelGS hj _).2 ⟨rfl, hj1, cubeBase_boxMap hj hb1⟩
  have hy0' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm y0) := inBox_boxMap (by omega) hy0
  have hpimg : bm '' Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) =
      Pset m₁ ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) :=
    pset_image_q (m₀ := 0) hj hn hqA hy1
  have hE : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hE' : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  rw [mem_Qset_hat, mem_Qset_hat]
  constructor
  · rintro ⟨-, y, hyP, hyH⟩
    refine ⟨hqB, bm y, ?_, ?_⟩
    · have : bm y ∈ bm '' Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) := ⟨y, hyP, rfl⟩
      rw [hpimg] at this; exact this
    · exact (mem_hatBox_boxMap_iff hy0 hE hE' ((mem_hatBox_iff hy0 hE).1 hyH).1).1 hyH
  · rintro ⟨-, y', hyP', hyH'⟩
    have hP' : y' ∈ bm '' Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) := by
      rw [hpimg]; exact hyP'
    obtain ⟨y, hyP, rfl⟩ := hP'
    have hyB : InBox d (ρ₁ + L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) y :=
      pset_inBox hj hb1 hy1 (by omega) hyP
    have hyE' := ((mem_hatBox_iff hy0' hE').1 hyH').1
    have hyE : InBox d (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K) y :=
      fun μ => by
        rw [← valMinAbs_boxMap (m' := (N₁' * L ^ m₁) * L ^ K) (by omega : 2 * (ρ₁ + L ^ (j + m₁)) + 1 < _) hyB μ]
        exact hyE' μ
    exact ⟨hqA, y, hyP, (mem_hatBox_boxMap_iff hy0 hE hE' hyE).2 hyH'⟩

include hj1 in
/-- **T1 (`qset_image`).**  For a centre `q` of `levelGS j` with base point in the box of radius
`ρ`, the parameter cubes `𝒬(q)` of the second torus are the images of those of the first torus:
`Qset GB (Prod.map id bm q) = (Qset GA q).image (Prod.map id bm)`.  Margin
`2 ρ₁ + 5 L · cellSide L 0 m₁ j < N₁ L^m₁ L^K` (and for `N₁'`), `ρ₁ = ρ + (3 L^(j+m₁) +
3 L^(j+2)) + L^(j+m₁)`. -/
theorem qset_image
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx GA)
    (hq0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) q.2) :
    Qset GB (Prod.map id bm q) = (Qset GA q).image (Prod.map id bm) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hq
  have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 := hq0
  have hy0' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm y0) := inBox_boxMap (by omega) hy0
  have hf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := K) (ρ := ρ₁) (ϱ := ϱ) hj1 hj (by omega) (by omega)
  ext q'
  constructor
  · intro hq'
    obtain ⟨y1', rfl, hb1', hy1'⟩ := qset_base_inBox (ϱ := ϱ) hj (by omega) hy0' hq'
    have hmem : ((j, y1') : ℕ × CTorus d L N₁' m₁ K) ∈ (cubeIdx GB).filter
        (fun q => InBox d (ρ₁) ((N₁' * L ^ m₁) * L ^ K) q.2) :=
      Finset.mem_filter.2 ⟨(mem_Qset_hat.1 hq').1, hy1'⟩
    rw [hf] at hmem
    obtain ⟨q0, hq0m, hq0e⟩ := Finset.mem_image.1 hmem
    obtain ⟨hq0c, hq0b⟩ := Finset.mem_filter.1 hq0m
    obtain ⟨y1, rfl, hb1⟩ := exists_of_mem_cubeIdx hj hq0c
    refine Finset.mem_image.2 ⟨(j, y1), ?_, hq0e⟩
    have hy1 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) y1 := hq0b
    have hbm : bm y1 = y1' := by
      have := congrArg Prod.snd hq0e
      simpa using this
    rw [qset_mem_iff hj1 hj hn hn' hy0 hb1 hy1, hbm]
    exact hq'
  · intro hq'
    obtain ⟨q0, hq0m, rfl⟩ := Finset.mem_image.1 hq'
    obtain ⟨y1, rfl, hb1, hy1⟩ := qset_base_inBox (ϱ := ϱ) hj (by omega) hy0 hq0m
    exact (qset_mem_iff hj1 hj hn hn' hy0 hb1 hy1).1 hq0m

include hj1 in
/-- **T2 (`sProd_boxMap`).**  The cut weights `s_z = ∏_{P ∈ 𝒬(z)} s_P` of a centre in the box agree
on the two tori when the parameters correspond on `𝒬(z)`. -/
theorem sProd_boxMap
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx GA)
    (hq0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) q.2)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ Qset GA q, s' (Prod.map id bm P) = s P) :
    sProd GB s' (Prod.map id bm q) = sProd GA s q := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hq
  have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 := hq0
  have hbase : ∀ P ∈ Qset GA ((j, y0) : ℕ × CTorus d L N₁ m₁ K),
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2 := by
    intro P hP
    obtain ⟨y1, rfl, -, hy1⟩ := qset_base_inBox (ϱ := ϱ) hj (by omega) hy0 hP
    exact hy1
  unfold sProd
  rw [qset_image hj1 hj hn hn' hq hq0, Finset.prod_image]
  · exact Finset.prod_congr rfl hs
  · intro P hP P2 hP2 h
    exact injOn_idxMap (N₁' := N₁') (ρ := ρ₁) (by omega) (hbase P hP) (hbase P2 hP2) h

include hj1 hj ϱ in
/-- The patch `𝒫(P)` of a centre `P` of the box lies in `X₁` iff that of the image centre lies in
the image of `X₁`. -/
theorem cubeP_subset_iff
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {y1 : CTorus d L N₁ m₁ K} (hb1 : CubeBase (K := K) m₁ j y1)
    (hy1 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) y1) :
    cubeP ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) ⊆ X₁.image bm ↔
      cubeP ((j, y1) : ℕ × CTorus d L N₁ m₁ K) ⊆ X₁ := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hqA : ((j, y1) : ℕ × CTorus d L N₁ m₁ K) ∈ cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
      (ϱ := ϱ) j hj) :=
    (mem_cubeIdx_levelGS hj _).2 ⟨rfl, hj1, hb1⟩
  have hpimg : bm '' Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) =
      Pset m₁ ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) :=
    pset_image_q (m₀ := 0) hj hn hqA hy1
  constructor
  · intro h x hx
    have hxP : x ∈ Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) := mem_cubeP.1 hx
    have hx' : bm x ∈ cubeP ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) := by
      rw [mem_cubeP]
      have : bm x ∈ bm '' Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) := ⟨x, hxP, rfl⟩
      rw [hpimg] at this; exact this
    obtain ⟨x0, hx0, hxe⟩ := Finset.mem_image.1 (h hx')
    have hxB : InBox d (ρ₁ + L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x :=
      pset_inBox hj hb1 hy1 (by omega) hxP
    have hx0B : InBox d (ρ₁ + L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x0 :=
      inBox_mono (by omega) (hX x0 hx0)
    have := boxMap_inj (hm' := (by omega : 2 * (ρ₁ + L ^ (j + m₁)) + 1 <
      (N₁' * L ^ m₁) * L ^ K)) hx0B hxB hxe
    exact this ▸ hx0
  · intro h x' hx'
    have hx'P : x' ∈ bm '' Pset m₁ ((j, y1) : ℕ × CTorus d L N₁ m₁ K) := by
      rw [hpimg]; exact mem_cubeP.1 hx'
    obtain ⟨x, hxP, rfl⟩ := hx'P
    exact Finset.mem_image_of_mem _ (h (mem_cubeP.2 hxP))

include hj1 in
/-- The parameter cubes `𝔓` (cubes not contained in `X₁`) correspond. -/
theorem map_mem_parCubes_iff
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ cubeIdx GA)
    (hP0 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2) :
    Prod.map id bm P ∈ parCubes GB (X₁.image bm) ↔ P ∈ parCubes GA X₁ := by
  obtain ⟨y1, rfl, hb1⟩ := exists_of_mem_cubeIdx hj hP
  have hPB : ((j, bm y1) : ℕ × CTorus d L N₁' m₁ K) ∈ cubeIdx GB :=
    (mem_cubeIdx_levelGS hj _).2 ⟨rfl, hj1, cubeBase_boxMap hj hb1⟩
  unfold parCubes
  rw [Finset.mem_filter, Finset.mem_filter]
  have := cubeP_subset_iff (ϱ := ϱ) hj1 hj hn hn' hX hb1 hP0
  exact ⟨fun h => ⟨hP, fun h2 => h.2 (this.2 h2)⟩, fun h => ⟨hPB, fun h2 => h.2 (this.1 h2)⟩⟩

omit [NeZero N₁] [NeZero N₁'] in
/-- A cube of `𝒞` or its image: membership of an image centre in the image family. -/
theorem map_mem_image_iff
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    {P : ℕ × CTorus d L N₁ m₁ K} (hP0 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2) :
    Prod.map id bm P ∈ 𝒞.image (Prod.map id bm) ↔ P ∈ 𝒞 := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  constructor
  · intro h
    obtain ⟨P0, hP0C, he⟩ := Finset.mem_image.1 h
    have := injOn_idxMap (N₁' := N₁') (ρ := ρ₁) (by omega) (inBox_mono (by omega) (hC P0 hP0C) :
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P0.2) hP0 he
    exact this ▸ hP0C
  · exact fun h => Finset.mem_image_of_mem _ h

/-- The thickened cube of a centre of the box lies in `Y` iff that of the image centre lies in the
image of `Y`. -/
theorem hatBox_subset_iff
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {Y : Finset (CTorus d L N₁ m₁ K)} (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    (∀ x', x' ∈ hatBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) → x' ∈ Y.image bm) ↔
      (∀ x, x ∈ hatBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) → x ∈ Y) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hy0' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm y0) := inBox_boxMap (by omega) hy0
  have hE : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁ * L ^ m₁) * L ^ K := by omega
  have hE' : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 < (N₁' * L ^ m₁) * L ^ K := by omega
  constructor
  · intro h x hx
    have hxE := ((mem_hatBox_iff hy0 hE).1 hx).1
    obtain ⟨x0, hx0, hxe⟩ := Finset.mem_image.1
      (h (bm x) ((mem_hatBox_boxMap_iff hy0 hE hE' hxE).1 hx))
    have := boxMap_inj (hm' := (by omega : 2 * (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) + 1 <
      (N₁' * L ^ m₁) * L ^ K)) (inBox_mono (by omega) (hY x0 hx0)) hxE hxe
    exact this ▸ hx0
  · intro h x' hx'
    have hxE' := ((mem_hatBox_iff hy0' hE').1 hx').1
    have hxE : InBox d (ρ + (3 * L ^ (j + m₁) + 3 * L ^ (j + 2))) ((N₁ * L ^ m₁) * L ^ K)
        (bm' x') := inBox_boxMap hE hxE'
    have hbb : bm (bm' x') = x' := boxMap_boxMap hE hxE'
    have hx : bm' x' ∈ hatBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) := by
      rw [mem_hatBox_boxMap_iff hy0 hE hE' hxE, hbb]; exact hx'
    exact hbb ▸ Finset.mem_image_of_mem _ (h _ hx)

include hj1 in
/-- **The centres `Z_Y` correspond (pointwise).**  For a centre `z` of the box,
`z ∈ Z_Y` iff the image centre lies in `Z_{Y'}` of the images `X₁' = bm '' X₁`, `𝒞' = 𝒞`'s image,
`Y' = bm '' Y`. -/
theorem map_mem_ZY_iff
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {Y : Finset (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx GA)
    (hz0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) z.2) :
    Prod.map id bm z ∈ ZY GB (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm) ↔
      z ∈ ZY GA X₁ 𝒞 Y := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hzB : Prod.map id bm z ∈ cubeIdx GB := by
    have hf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁)
      (K := K) (ρ := ρ₁) (ϱ := ϱ) hj1 hj (by omega) (by omega)
    have : Prod.map id bm z ∈ (cubeIdx GB).filter
        (fun q => InBox d (ρ₁) ((N₁' * L ^ m₁) * L ^ K) q.2) := by
      rw [hf]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hz, inBox_mono (by omega) hz0⟩)
    exact (Finset.mem_filter.1 this).1
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hz
  have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 := hz0
  unfold ZY
  rw [Finset.mem_filter, Finset.mem_filter, subI_levelGS_iff hj1 hj, subI_levelGS_iff hj1 hj]
  have hh := hatBox_subset_iff hn hn' hY hy0
  have hQ := qset_image hj1 hj hn hn' hz hz0
  have hbase : ∀ P ∈ Qset GA ((j, y0) : ℕ × CTorus d L N₁ m₁ K),
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2 := by
    intro P hP
    obtain ⟨y1, rfl, -, hy1⟩ := qset_base_inBox (ϱ := ϱ) hj (by omega) hy0 hP
    exact hy1
  have hq : (∀ P' ∈ Qset GB (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K)),
      P' ∈ parCubes GB (X₁.image bm) → P' ∈ 𝒞.image (Prod.map id bm)) ↔
      ∀ P ∈ Qset GA ((j, y0) : ℕ × CTorus d L N₁ m₁ K), P ∈ parCubes GA X₁ → P ∈ 𝒞 := by
    rw [hQ]
    constructor
    · intro h P hP hPp
      have hPc := Qset_subset_cubeIdx _ hP
      exact (map_mem_image_iff hn' hC (hbase P hP)).1
        (h _ (Finset.mem_image_of_mem _ hP)
          ((map_mem_parCubes_iff hj1 hj hn hn' hX hPc (hbase P hP)).2 hPp))
    · intro h P' hP' hPp
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hP'
      have hPc := Qset_subset_cubeIdx _ hP
      exact (map_mem_image_iff hn' hC (hbase P hP)).2
        (h P hP ((map_mem_parCubes_iff hj1 hj hn hn' hX hPc (hbase P hP)).1 hPp))
  exact ⟨fun h => ⟨hz, hq.1 h.2.1, hh.1 h.2.2⟩, fun h => ⟨hzB, hq.2 h.2.1, hh.2 h.2.2⟩⟩

include hj1 in
/-- **`Z_Y` on two tori.**  For `X₁`, the family `𝒞` of centres and the set `Y` inside the box of
radius `ρ`, the centres `Z_{Y'}` of the images `X₁' = bm '' X₁`, `𝒞' = Prod.map id bm '' 𝒞`,
`Y' = bm '' Y` are the images of the centres `Z_Y`.  Margin `2 ρ₁ + 5 L · cellSide L 0 m₁ j <
N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem ZY_image
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {Y : Finset (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    ZY GB (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm) =
      (ZY GA X₁ 𝒞 Y).image (Prod.map id bm) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁)
    (K := K) (ρ := ρ) (ϱ := ϱ) hj1 hj (by omega) (by omega)
  ext z'
  constructor
  · intro hz'
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (ZY_base_mem hj1 hj hz')
    have hb : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) z'.2 := by
      rw [← hxe]; exact inBox_boxMap (by omega) (hY x hx)
    have hmem : z' ∈ (cubeIdx GB).filter
        (fun q => InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2) :=
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz').1, hb⟩
    rw [hf] at hmem
    obtain ⟨z, hzm, rfl⟩ := Finset.mem_image.1 hmem
    obtain ⟨hzc, hz0⟩ := Finset.mem_filter.1 hzm
    exact Finset.mem_image.2 ⟨z, (map_mem_ZY_iff hj1 hj hn hn' hX hC hY hzc hz0).1 hz', rfl⟩
  · intro hz'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    exact (map_mem_ZY_iff hj1 hj hn hn' hX hC hY (Finset.mem_filter.1 hz).1
      (hY _ (ZY_base_mem hj1 hj hz))).2 hz

include hj1 in
/-- **T3 (`SY_image`).**  The block set `S_Y` of the images is the image of `S_Y`:
`(SY GA X₁ 𝒞 Y).image bm = SY GB (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm)`, for
`X₁`, the base points of `𝒞` and `Y` in the box of radius `ρ`.  Margin
`2 ρ₁ + 5 L · cellSide L 0 m₁ j < N₁ L^m₁ L^K` (and for `N₁'`),
`ρ₁ = ρ + (3 L^(j+m₁) + 3 L^(j+2)) + L^(j+m₁)`. -/
theorem SY_image
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {Y : Finset (CTorus d L N₁ m₁ K)}
    (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hC : ∀ P ∈ 𝒞, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) P.2)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    (SY GA X₁ 𝒞 Y).image bm =
      SY GB (X₁.image bm) (𝒞.image (Prod.map id bm)) (Y.image bm) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  unfold SY
  rw [ZY_image hj1 hj hn hn' hX hC hY, Finset.biUnion_image, Finset.image_biUnion]
  refine Finset.biUnion_congr rfl fun z hz => ?_
  have hzc := (Finset.mem_filter.1 hz).1
  obtain ⟨y0, rfl, hb⟩ := exists_of_mem_cubeIdx hj hzc
  have hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0 := hY _ (ZY_base_mem hj1 hj hz)
  apply Finset.coe_injective
  rw [Finset.coe_image]
  exact (intBox_image (N₁' := N₁') (ρ₀ := ρ) (j := j) hy0 (by omega) (by omega))

include hj1 in
/-- **T2, parameters of `extS`.**  If the parameters correspond on the indices of `ParIdx` with
centre in the box of radius `ρ₁`, the extended parameter vectors `extS` of
`extParams` correspond at every centre of the box of radius `ρ₁`. -/
theorem extS_extParams_boxMap
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {X₁ : Set (CTorus d L N₁ m₁ K)} (hX : ∀ x ∈ X₁, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (σ : ParIdx GA X₁ → ℂ) (σ' : ParIdx GB (bm '' X₁) → ℂ)
    (hσ : ∀ (i : ParIdx GA X₁) (i' : ParIdx GB (bm '' X₁)),
      InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) i.1.1.2 → i'.1.1 = Prod.map id bm i.1.1 → σ' i' = σ i)
    {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ cubeIdx GA)
    (hP0 : InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2) :
    extS GB (extParams GB (bm '' X₁) σ') (Prod.map id bm P) =
      extS GA (extParams GA X₁ σ) P := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  have hPB : Prod.map id bm P ∈ cubeIdx GB := by
    have hf := cubeIdx_filter_image (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁)
      (K := K) (ρ := ρ₁) (ϱ := ϱ) hj1 hj (by omega) (by omega)
    have : Prod.map id bm P ∈ (cubeIdx GB).filter
        (fun q => InBox d (ρ₁) ((N₁' * L ^ m₁) * L ^ K) q.2) := by
      rw [hf]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hP, hP0⟩)
    exact (Finset.mem_filter.1 this).1
  have hX1 : ∀ x ∈ X₁, InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) x := fun x hx =>
    inBox_mono (by omega) (hX x hx)
  have hdis := pset_disjoint_iff (m₀ := 0) (N₁' := N₁') (ρ := ρ₁) hj hn hn' hP hP0 hX1
  simp only [extS, hP, hPB, dite_true]
  unfold extParams
  by_cases hd : Disjoint (Pset m₁ P) X₁
  · have hd' := hdis.2 hd
    simp only [hd, hd', dite_true]
    exact hσ ⟨⟨P, hP⟩, hd⟩ ⟨⟨_, hPB⟩, hd'⟩ hP0 rfl
  · have hd' : ¬ Disjoint (Pset m₁ (Prod.map id bm P)) (bm '' X₁) := fun h => hd (hdis.1 h)
    simp only [hd, hd', dite_false]

include hj1 in
/-- **T2 for the inner centres (`hagree` of `decBg_green_rows_transport`).**  For a set `T` inside
`Y` (which lies in the box of radius `ρ`), the cut weights agree at the image of every centre of
`innerCentres GA T`, if the parameters agree at the cubes of the box of radius `ρ₁`. -/
theorem hagree_boxMap
    (hn : 2 * (ρ₁) + 5 * cs < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₁) + 5 * cs < (N₁' * L ^ m₁) * L ^ K)
    {T Y : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {s' : ℕ × CTorus d L N₁' m₁ K → ℂ}
    (hs : ∀ P ∈ cubeIdx GA, InBox d (ρ₁) ((N₁ * L ^ m₁) * L ^ K) P.2 →
      s' (Prod.map id bm P) = s P) :
    ∀ q ∈ innerCentres GA T, sProd GB s' (Prod.map id bm q) = sProd GA s q := by
  intro q hq
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) 0 m₁ j
  obtain ⟨y0, rfl, hb, hy0T, -⟩ := inner_base_mem hj1 hj hq
  have hqc := (Finset.mem_filter.1 hq).1
  refine sProd_boxMap hj1 hj hn hn' hqc (hY _ (hTY hy0T)) fun P hP => hs P
    (Qset_subset_cubeIdx _ hP) ?_
  obtain ⟨y1, rfl, -, hy1⟩ := qset_base_inBox (ϱ := ϱ) hj (by omega) (hY _ (hTY hy0T)) hP
  exact hy1

end Margin

end TwoTori

end Balaban.Polymer.TwoTorusStep
