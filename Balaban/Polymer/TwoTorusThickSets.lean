/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusStepGeometry
public import Balaban.Localization.DecoupledBackgroundLocal
public import Balaban.Localization.I5Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The generating-set data of the step on two tori

For two step tori `CTorus d L N₁ m₁ K`, `CTorus d L N₁' m₁ K` identified on a centred box by
`Balaban.Polymer.boxMap`, this file shows that the data built from the whole-lattice generating
sets `levelGS j` (these are `lvTop`, `lvLow` of the level step) correspond: the periodized bump of
a block, the active blocks `active`, the layer index, the dependency sets `resDep` and the thick
sets `thickSet`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background

/-! ### The periodized bump in centred coordinates -/

section Bump

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

theorem perN_eq_bsp {r α : ℝ} (h : |α| + 3 / 2 ≤ r) : perN r α = bsp α := by
  unfold perN
  rw [finsum_eq_single _ (0 : ℤ)]
  · simp
  · intro p hp
    apply bsp_eq_zero
    have hp1 : (1 : ℝ) ≤ |(p : ℝ)| := by
      have : (1 : ℤ) ≤ |p| := Int.one_le_abs hp
      exact_mod_cast this
    have hr : 0 ≤ r := by have := abs_nonneg α; linarith
    have h1 : |(p : ℝ) * r| = |(p : ℝ)| * r := by rw [abs_mul, abs_of_nonneg hr]
    have h2 : r ≤ |(p : ℝ)| * r := by nlinarith
    have h3 : |(p : ℝ) * r| ≤ |α + p * r| + |α| := by
      have := abs_sub (α + p * r) α
      simpa using this
    linarith

theorem perFac_eq_perN (m : ℕ) (x y0 : Torus d (N₀ * L ^ k)) (μ : Fin d) (a b : ℤ)
    (ha : ((a : ℤ) : ZMod (N₀ * L ^ k)) = x μ) (hb : ((b : ℤ) : ZMod (N₀ * L ^ k)) = y0 μ) :
    perFac m y0 μ ((x μ).val : ℝ) =
      perN (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m)
        (((a : ℝ) - b - ((L : ℝ) ^ m - 1) / 2) / (L : ℝ) ^ m) := by
  rw [← perFac_lift m y0 x μ a ha]
  have hv : ((((y0 μ).val : ℕ) : ℤ) : ZMod (N₀ * L ^ k)) = ((b : ℤ) : ZMod (N₀ * L ^ k)) := by
    rw [hb]; simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hv
  obtain ⟨q, hq⟩ := hv
  have hq' : (b : ℝ) - ((y0 μ).val : ℝ) = ((N₀ * L ^ k : ℕ) : ℝ) * q := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hq
    simpa using this
  have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  unfold perFac bumpCentre
  have : (((a : ℝ) - (((y0 μ).val : ℝ) + ((L : ℝ) ^ m - 1) / 2)) / (L : ℝ) ^ m) =
      (((a : ℝ) - b - ((L : ℝ) ^ m - 1) / 2) / (L : ℝ) ^ m) +
        (q : ℤ) * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) := by
    push_cast at hq' ⊢
    field_simp
    linarith
  rw [this, perN_add_int_mul]

theorem bump_eq_prod_bsp {ρ ρ₂ : ℕ} (m : ℕ) (x y0 : Torus d (N₀ * L ^ k))
    (hx : InBox d ρ (N₀ * L ^ k) x) (hy : InBox d ρ₂ (N₀ * L ^ k) y0)
    (hn : ρ + ρ₂ + 3 * L ^ m ≤ N₀ * L ^ k) :
    bump m y0 x = ∏ μ, bsp ((((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs -
      ((L : ℝ) ^ m - 1) / 2) / (L : ℝ) ^ m) := by
  have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hLm : (1 : ℝ) ≤ (L : ℝ) ^ m := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact one_le_pow₀ this
  unfold bump
  refine Finset.prod_congr rfl fun μ _ => ?_
  rw [perFac_eq_perN m x y0 μ _ _ (by rw [ZMod.coe_valMinAbs]) (by rw [ZMod.coe_valMinAbs])]
  apply perN_eq_bsp
  have h1 : |((x μ).valMinAbs : ℝ)| ≤ ρ := by exact_mod_cast hx μ
  have h2 : |((y0 μ).valMinAbs : ℝ)| ≤ ρ₂ := by exact_mod_cast hy μ
  have h3 : (ρ : ℝ) + ρ₂ + 3 * (L : ℝ) ^ m ≤ ((N₀ * L ^ k : ℕ) : ℝ) := by exact_mod_cast hn
  rw [abs_le] at h1 h2
  have hA : |((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ m - 1) / 2| ≤
      ρ + ρ₂ + (L : ℝ) ^ m := by
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [abs_div, abs_of_pos hlam]
  calc _ = (|((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ m - 1) / 2| +
        3 / 2 * (L : ℝ) ^ m) / (L : ℝ) ^ m := by field_simp
    _ ≤ _ := by gcongr; linarith

/-- **The base point of a block whose bump is nonzero at `x` is near `x`.**  If `x` lies in the
centred box of radius `ρ` and `bump m y0 x ≠ 0`, then `y0` lies in the box of radius
`ρ + 2 L^m`. -/
theorem inBox_of_bump_ne_zero {ρ : ℕ} (m : ℕ) (x y0 : Torus d (N₀ * L ^ k))
    (hx : InBox d ρ (N₀ * L ^ k) x) (hn : 2 * (ρ + 2 * L ^ m) + 1 < N₀ * L ^ k)
    (h : bump m y0 x ≠ 0) : InBox d (ρ + 2 * L ^ m) (N₀ * L ^ k) y0 := by
  have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hLm : (1 : ℝ) ≤ (L : ℝ) ^ m := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    exact one_le_pow₀ this
  intro μ
  have hμ : perFac m y0 μ ((x μ).val : ℝ) ≠ 0 := (Finset.prod_ne_zero_iff.1 h) μ (Finset.mem_univ _)
  rw [perFac_eq_perN m x y0 μ _ (y0 μ).valMinAbs (by rw [ZMod.coe_valMinAbs])
    (by rw [ZMod.coe_valMinAbs])] at hμ
  obtain ⟨p, hp⟩ := exists_of_perN_ne_zero hμ
  set t : ℤ := (y0 μ).valMinAbs - p * ((N₀ * L ^ k : ℕ) : ℤ) with ht
  have hp' : |((x μ).valMinAbs : ℝ) - t - ((L : ℝ) ^ m - 1) / 2| < 3 / 2 * (L : ℝ) ^ m := by
    have e : (((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ m - 1) / 2) /
        (L : ℝ) ^ m + p * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) =
        (((x μ).valMinAbs : ℝ) - t - ((L : ℝ) ^ m - 1) / 2) / (L : ℝ) ^ m := by
      rw [ht]; push_cast; field_simp; ring
    rw [e, abs_div, abs_of_pos hlam, div_lt_iff₀ hlam] at hp
    linarith
  have h1 : |((x μ).valMinAbs : ℝ)| ≤ ρ := by exact_mod_cast hx μ
  have hte : |(t : ℝ)| ≤ ((ρ + 2 * L ^ m : ℕ) : ℝ) := by
    rw [abs_le] at h1 ⊢
    rw [abs_lt] at hp'
    push_cast
    constructor <;> nlinarith [h1.1, h1.2, hp'.1, hp'.2]
  have hti : |t| ≤ ((ρ + 2 * L ^ m : ℕ) : ℤ) := by exact_mod_cast hte
  have hcast : ((t : ℤ) : ZMod (N₀ * L ^ k)) = y0 μ := by
    have h0 : ((p * ((N₀ * L ^ k : ℕ) : ℤ) : ℤ) : ZMod (N₀ * L ^ k)) = 0 := by
      rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero]
    rw [ht, Int.cast_sub, h0, sub_zero, ZMod.coe_valMinAbs]
  have := valMinAbs_intCast_of_abs_le (m := N₀ * L ^ k) (r := ρ + 2 * L ^ m) hn hti
  rw [hcast] at this
  rw [this]; exact hti

/-- **The periodized bump on two tori.**  For `x` in the box of radius `ρ` and `y0` in the box of
radius `ρ₂`, the bump of the block of base `y0` at `x` is the same on both tori. -/
theorem bump_boxMap {N₀' ρ ρ₂ : ℕ} [NeZero N₀'] (m : ℕ) (x y0 : Torus d (N₀ * L ^ k))
    (hx : InBox d ρ (N₀ * L ^ k) x) (hy : InBox d ρ₂ (N₀ * L ^ k) y0)
    (hn : ρ + ρ₂ + 3 * L ^ m ≤ N₀ * L ^ k) (hn' : ρ + ρ₂ + 3 * L ^ m ≤ N₀' * L ^ k)
    (hx' : 2 * ρ + 1 < N₀' * L ^ k) (hy' : 2 * ρ₂ + 1 < N₀' * L ^ k) :
    bump m (boxMap (N₀ * L ^ k) (N₀' * L ^ k) y0) (boxMap (N₀ * L ^ k) (N₀' * L ^ k) x) =
      bump m y0 x := by
  rw [bump_eq_prod_bsp m _ _ (inBox_boxMap hx' hx) (inBox_boxMap hy' hy) hn',
    bump_eq_prod_bsp m _ _ hx hy hn]
  refine Finset.prod_congr rfl fun μ _ => ?_
  rw [valMinAbs_boxMap hx' hx, valMinAbs_boxMap hy' hy]

/-- Being the base point of a block of side `L^m` is preserved by `boxMap` when `L^m` divides
both torus sides. -/
theorem isBase_boxMap {N₀' : ℕ} [NeZero N₀'] {m : ℕ} (hm : m ≤ k)
    {y0 : Torus d (N₀ * L ^ k)} (hb : IsBase m y0) :
    IsBase m (boxMap (N₀ * L ^ k) (N₀' * L ^ k) y0) := by
  have h1 : L ^ m ∣ N₀ * L ^ k := Dvd.dvd.mul_left (pow_dvd_pow L hm) _
  have h2 : L ^ m ∣ N₀' * L ^ k := Dvd.dvd.mul_left (pow_dvd_pow L hm) _
  exact aligned_boxMap h1 h2 hb

end Bump

/-! ### Cells and neighbours stay in a slightly larger box -/

section BoxGrowth

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
theorem inBox_of_int {R : ℕ} (hn : 2 * R + 1 < n) (c : ZMod n) (t : ℤ) (hc : ((t : ℤ) : ZMod n) = c)
    (ht : |t| ≤ R) : |c.valMinAbs| ≤ R := by
  rw [← hc, valMinAbs_intCast_of_abs_le hn ht]; exact ht

/-- **A cell of side `a` through a point of the box lies in the box enlarged by `a`.** -/
theorem inBox_of_mem_cell {a ρ : ℕ} (hn : 2 * (ρ + a) + 1 < n) {x z : Torus d n}
    (hx : InBox d ρ n x) (hz : z ∈ box (cbase a x) a) : InBox d (ρ + a) n z := by
  obtain ⟨w, hw, rfl⟩ := hz
  intro μ
  have hxμ : (((x μ).val : ℕ) : ZMod n) = x μ := ZMod.natCast_zmod_val _
  have hdm := Nat.div_add_mod (x μ).val a
  have hr : (x μ).val % a < a := Nat.mod_lt _ (by have := hw μ; omega)
  refine inBox_of_int hn _ ((x μ).valMinAbs + (w μ : ℤ) - (((x μ).val % a : ℕ) : ℤ)) ?_ ?_
  · have h1 : (((a * ((x μ).val / a) : ℕ) : ZMod n)) + (((x μ).val % a : ℕ) : ZMod n) = x μ := by
      rw [← Nat.cast_add, hdm, hxμ]
    have h2 : (((x μ).valMinAbs : ℤ) : ZMod n) = x μ := ZMod.coe_valMinAbs _
    rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_natCast, h2]
    simp only [Pi.add_apply, cbase, natT_apply]
    linear_combination -h1
  · have h1 := abs_le.1 (hx μ)
    have h3 := hw μ
    rw [abs_le]
    push_cast
    constructor <;> omega

omit [NeZero n] in
theorem inBox_add_single {ρ : ℕ} (hn : 2 * (ρ + 1) + 1 < n) {x : Torus d n} (hx : InBox d ρ n x)
    (μ : Fin d) : InBox d (ρ + 1) n (x + Pi.single μ 1) := by
  intro ν
  have h2 : (((x ν).valMinAbs : ℤ) : ZMod n) = x ν := ZMod.coe_valMinAbs _
  have h1 := abs_le.1 (hx ν)
  by_cases hν : ν = μ
  · subst hν
    refine inBox_of_int hn _ ((x ν).valMinAbs + 1) ?_ ?_
    · simp only [Pi.add_apply, Pi.single_eq_same]; simp [h2]
    · rw [abs_le]; push_cast; constructor <;> omega
  · refine inBox_of_int hn _ ((x ν).valMinAbs) ?_ ?_
    · simp only [Pi.add_apply, Pi.single_eq_of_ne hν, add_zero]; exact h2
    · rw [abs_le]; constructor <;> omega

omit [NeZero n] in
theorem inBox_sub_single {ρ : ℕ} (hn : 2 * (ρ + 1) + 1 < n) {x : Torus d n} (hx : InBox d ρ n x)
    (μ : Fin d) : InBox d (ρ + 1) n (x - Pi.single μ 1) := by
  intro ν
  have h2 : (((x ν).valMinAbs : ℤ) : ZMod n) = x ν := ZMod.coe_valMinAbs _
  have h1 := abs_le.1 (hx ν)
  by_cases hν : ν = μ
  · subst hν
    refine inBox_of_int hn _ ((x ν).valMinAbs - 1) ?_ ?_
    · simp only [Pi.sub_apply, Pi.single_eq_same]; simp [h2]
    · rw [abs_le]; push_cast; constructor <;> omega
  · refine inBox_of_int hn _ ((x ν).valMinAbs) ?_ ?_
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne hν, sub_zero]; exact h2
    · rw [abs_le]; constructor <;> omega

omit [NeZero n] in
theorem inBox_mono {ρ ρ' : ℕ} (h : ρ ≤ ρ') {x : Torus d n} (hx : InBox d ρ n x) : InBox d ρ' n x :=
  fun μ => (hx μ).trans (by exact_mod_cast h)

omit [NeZero n] in
/-- A box `b + [0, s)^d` through a point of the box of radius `ρ` lies in the box of radius
`ρ + s` (base point `b`). -/
theorem inBox_of_mem_box_right {ρ s : ℕ} (hn : 2 * (ρ + s) + 1 < n) {b z : Torus d n}
    (hb : InBox d ρ n b) (hz : z ∈ box b s) : InBox d (ρ + s) n z := by
  obtain ⟨w, hw, rfl⟩ := hz
  intro μ
  have h2 : (((b μ).valMinAbs : ℤ) : ZMod n) = b μ := ZMod.coe_valMinAbs _
  have h1 := abs_le.1 (hb μ)
  have h3 := hw μ
  refine inBox_of_int hn _ ((b μ).valMinAbs + (w μ : ℤ)) ?_ ?_
  · simp only [Pi.add_apply, natT_apply]
    rw [Int.cast_add, h2, Int.cast_natCast]
  · rw [abs_le]; push_cast; constructor <;> omega

omit [NeZero n] in
/-- The base point of a box `b + [0, s)^d` containing a point of the box of radius `ρ` lies in the
box of radius `ρ + s`. -/
theorem inBox_of_mem_box_left {ρ s : ℕ} (hn : 2 * (ρ + s) + 1 < n) {b z : Torus d n}
    (hz : InBox d ρ n z) (hmem : z ∈ box b s) : InBox d (ρ + s) n b := by
  obtain ⟨w, hw, rfl⟩ := hmem
  intro μ
  have h2 : (((b + natT w : Torus d n) μ).valMinAbs : ZMod n) = (b + natT w : Torus d n) μ :=
    ZMod.coe_valMinAbs _
  have h1 := abs_le.1 (hz μ)
  have h3 := hw μ
  refine inBox_of_int hn _ (((b + natT w : Torus d n) μ).valMinAbs - (w μ : ℤ)) ?_ ?_
  · rw [Int.cast_sub, Int.cast_natCast, h2]; simp
  · rw [abs_le]; push_cast; constructor <;> omega

/-- Two points in the same cell of side `a` lie in the box over the cell base. -/
theorem sameCell_iff_mem_box {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a) {x y : Torus d n} :
    (∀ μ, (x μ).val / a = (y μ).val / a) ↔ x ∈ box (cbase a y) a := by
  constructor
  · intro h
    exact mem_box_cbase_of_sameCell ha0 (fun μ => h μ)
  · intro hx μ
    have hc := cbase_eq_of_mem_box ha (aligned_cbase y) hx
    have h1 := congrFun hc μ
    simp only [cbase] at h1
    have hlt : ∀ z : Torus d n, a * ((z μ).val / a) < n := fun z => lt_of_le_of_lt
      (Nat.mul_div_le _ _) (ZMod.val_lt _)
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt (hlt x), ZMod.val_natCast_of_lt (hlt y)] at h2
    exact Nat.eq_of_mul_eq_mul_left ha0 h2

end BoxGrowth

/-! ### The level generating sets and their blocks -/

section Level

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

/-- The only nonempty layer of `levelGS j` is the layer `j`. -/
theorem layer_levelGS (hj : j ≤ K) (m : ℕ) :
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).layer m =
      if m = j then Finset.univ else ∅ := by
  ext x
  simp only [GeneratingSet.layer, levelGS, Finset.mem_sdiff]
  split_ifs <;> first | omega | simp_all

/-- The block indices of `levelGS j`: the base points of the blocks of side `L^j`. -/
theorem mem_blockIdx_levelGS (hj : j ≤ K) (q : ℕ × CTorus d L N₁ m₁ K) :
    q ∈ blockIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) ↔
      q.1 = j ∧ 1 ≤ j ∧ IsBase q.1 q.2 := by
  rw [mem_blockIdx, layer_levelGS hj]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    by_cases h : q.1 = j
    · exact ⟨h, h ▸ h1, h4⟩
    · simp [h] at h3
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1 ▸ h2, h1 ▸ hj⟩, by simp [h1], h3⟩

theorem layerIndex_levelGS (hj1 : 1 ≤ j) (hj : j ≤ K) (x : CTorus d L N₁ m₁ K) :
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).layerIndex x = j :=
  GeneratingSet.layerIndex_eq _ hj1 hj (by
    have h := layer_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj j
    simp only [ite_true] at h
    rw [h]; exact Finset.mem_univ _)

theorem pow_facts (hj : j ≤ K) : 1 ≤ L ^ K ∧ L ^ j ≤ L ^ K :=
  ⟨Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L)),
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hj⟩

/-- **T1 (active blocks).**  The blocks active at a site `x` of the box of radius `ρ` of the first
torus correspond, through `Prod.map id boxMap`, to the blocks active at `boxMap x` on the second
torus.  The base points of the active blocks lie in the box of radius `ρ + 2 L^K`.  Margin:
`2 ρ + 5 L^K < N₁ L^m₁ L^K` (and the same for `N₁'`). -/
theorem active_levelGS_image {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 5 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ K < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    active (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) (bm x) =
      (active (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        x).image (Prod.map id bm) := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hx' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm x) := inBox_boxMap (by omega) hx
  ext ⟨m, y'⟩
  simp only [mem_active, mem_blockIdx_levelGS hj, Finset.mem_image]
  constructor
  · rintro ⟨⟨hm, h1, hb'⟩, hne⟩
    have hm : m = j := hm
    have hne : bump m y' (bm x) ≠ 0 := hne
    have hb' : IsBase m y' := hb'
    subst hm
    have hy' : InBox d (ρ + 2 * L ^ K) ((N₁' * L ^ m₁) * L ^ K) y' :=
      fun μ => (inBox_of_bump_ne_zero m (N₀ := N₁' * L ^ m₁) (k := K) _ _ hx' (by omega) hne μ).trans
        (by omega)
    have hyy : bm (bm' y') = y' := boxMap_boxMap (by omega) hy'
    have hxx : bm' (bm x) = x := boxMap_boxMap (by omega) hx
    refine ⟨(m, bm' y'), ⟨⟨rfl, h1, ?_⟩, ?_⟩, by simp [hyy]⟩
    · exact isBase_boxMap (N₀ := N₁' * L ^ m₁) (k := K) hj hb'
    · simp only
      have := bump_boxMap (N₀ := N₁' * L ^ m₁) (N₀' := N₁ * L ^ m₁) (k := K) m (bm x) y' hx' hy'
        (by omega) (by omega) (by omega) (by omega)
      rw [hxx] at this
      rw [this]; exact hne
  · rintro ⟨⟨m', y⟩, ⟨⟨hm, h1, hb⟩, hne⟩, he⟩
    have hm : m' = j := hm
    have hne : bump m' y x ≠ 0 := hne
    have hb : IsBase m' y := hb
    simp only [Prod.map, id, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [hm] at hne hb ⊢
    have hy : InBox d (ρ + 2 * L ^ K) ((N₁ * L ^ m₁) * L ^ K) y :=
      fun μ => (inBox_of_bump_ne_zero j (N₀ := N₁ * L ^ m₁) (k := K) _ _ hx (by omega) hne μ).trans
        (by omega)
    refine ⟨⟨rfl, h1, isBase_boxMap (N₀ := N₁ * L ^ m₁) (k := K) hj hb⟩, ?_⟩
    rw [bump_boxMap (N₀ := N₁ * L ^ m₁) (N₀' := N₁' * L ^ m₁) (k := K) j x y hx hy
      (by omega) (by omega) (by omega) (by omega)]
    exact hne

end Level

section Dep

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- `boxMap` commutes with the unit translation `+ e_μ` inside the box. -/
theorem boxMap_add_single {ρ : ℕ} (hn : 2 * (ρ + 1) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + 1) + 1 < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (μ : Fin d) :
    bm (x + Pi.single μ 1) = bm x + Pi.single μ 1 :=
  (step_boxMap_iff (r := ρ + 1) hn hn' (inBox_mono (Nat.le_succ ρ) hx)
    (inBox_add_single hn hx μ) μ).1 rfl

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
/-- `boxMap` commutes with the unit translation `- e_μ` inside the box. -/
theorem boxMap_sub_single {ρ : ℕ} (hn : 2 * (ρ + 1) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ + 1) + 1 < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (μ : Fin d) :
    bm (x - Pi.single μ 1) = bm x - Pi.single μ 1 := by
  have := (step_boxMap_iff (r := ρ + 1) hn hn'
    (inBox_sub_single hn hx μ) (inBox_mono (Nat.le_succ ρ) hx) μ).1 (by simp)
  exact eq_sub_of_add_eq this.symm

/-- **The dependency base points of a site.**  `approxDep` of the image site is the image of
`approxDep`.  Margin: `2 ρ + 5 L^K < N₁ L^m₁ L^K`. -/
theorem approxDep_levelGS_image {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 5 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ K < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    (↑(approxDep (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (bm x)) : Set (CTorus d L N₁' m₁ K)) =
      bm '' ↑(approxDep (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        x) := by
  unfold approxDep
  rw [active_levelGS_image hj1 hj hn hn' hx]
  simp only [Finset.coe_insert, Finset.coe_image, Set.image_insert_eq, Set.image_image,
    Prod.map_snd]

/-- **The residual sites.**  `resSites` of the image site is the image of `resSites`, for a site
of the box of radius `ρ`.  Margin: `2 ρ + 3 L^K < N₁ L^m₁ L^K`. -/
theorem resSites_levelGS_image {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 3 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    (↑(resSites (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (bm x)) : Set (CTorus d L N₁' m₁ K)) =
      bm '' ↑(resSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        x) := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hblk := blk_image (r := ρ + L ^ K) (j := j)
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
    (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) hj
    (by omega) x (fun z hz => inBox_mono (by omega)
      (inBox_of_mem_cell (a := L ^ j) (by omega) hx hz))
  have hplus : bm '' ((fun μ : Fin d => x + Pi.single μ 1) '' Set.univ) =
      (fun μ : Fin d => bm x + Pi.single μ 1) '' Set.univ := by
    rw [Set.image_image]
    congr 1; funext μ; exact boxMap_add_single (ρ := ρ) (by omega) (by omega) hx μ
  have hminus : bm '' ((fun μ : Fin d => x - Pi.single μ 1) '' Set.univ) =
      (fun μ : Fin d => bm x - Pi.single μ 1) '' Set.univ := by
    rw [Set.image_image]
    congr 1; funext μ; exact boxMap_sub_single (ρ := ρ) (by omega) (by omega) hx μ
  unfold resSites
  rw [layerIndex_levelGS hj1 hj, layerIndex_levelGS hj1 hj]
  simp only [Finset.coe_insert, Finset.coe_union, Finset.coe_image, Finset.coe_univ,
    Set.image_insert_eq, Set.image_union]
  rw [hblk, hplus, hminus]

/-- **T2 (dependency sets).**  `resDep` of the image site is the image of `resDep`, for a site of
the box of radius `ρ`.  Margin: `2 ρ + 7 L^K < N₁ L^m₁ L^K`; the dependency set lies in the box of
radius `ρ + 3 L^K`. -/
theorem resDep_levelGS_image {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 7 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 7 * L ^ K < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    (↑(resDep (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (bm x)) : Set (CTorus d L N₁' m₁ K)) =
      bm '' ↑(resDep (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        x) := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hres := resSites_levelGS_image (ϱ := ϱ) (m₁ := m₁) (N₁ := N₁) (N₁' := N₁') hj1 hj (by omega) (by omega) hx
  -- every residual site lies in the box of radius `ρ + L^K`
  have hbox : ∀ y ∈ resSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ)
      j hj) x, InBox d (ρ + L ^ K) ((N₁ * L ^ m₁) * L ^ K) y := by
    intro y hy
    unfold resSites at hy
    rw [layerIndex_levelGS hj1 hj] at hy
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hy
    rcases hy with rfl | (hy | ⟨μ, rfl⟩) | ⟨μ, rfl⟩
    · exact inBox_mono (by omega) hx
    · exact inBox_mono (by omega) (inBox_of_mem_cell (a := L ^ j) (by omega) hx
        (by simpa [GeneratingSet.mem_blk, jBlock_eq_iff_mem_box hj] using hy))
    · exact inBox_mono (by omega) (inBox_add_single (by omega) hx μ)
    · exact inBox_mono (by omega) (inBox_sub_single (by omega) hx μ)
  have hmem : ∀ y, y ∈ resSites (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K)
      (ϱ := ϱ) j hj) (bm x) ↔ ∃ y0 ∈ resSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := K) (ϱ := ϱ) j hj) x, bm y0 = y := by
    intro y
    have := Set.ext_iff.1 hres y
    simpa using this
  have hap : ∀ y0 ∈ resSites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := K) (ϱ := ϱ) j hj) x, ∀ z, z ∈ approxDep (levelGS (d := d) (L := L) (N₁ := N₁')
      (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) (bm y0) ↔ ∃ w ∈ approxDep (levelGS (d := d) (L := L)
      (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) y0, bm w = z := by
    intro y0 hy0 z
    have := Set.ext_iff.1 (approxDep_levelGS_image (ϱ := ϱ) (m₁ := m₁) (N₁ := N₁) (N₁' := N₁')
      (ρ := ρ + L ^ K) hj1 hj (by omega) (by omega) (hbox y0 hy0)) z
    simpa using this
  ext z
  simp only [resDep, Finset.coe_biUnion, Set.mem_iUnion, Set.mem_image, Finset.mem_coe,
    exists_prop]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨y0, hy0, rfl⟩ := (hmem y).1 hy
    obtain ⟨w, hw, rfl⟩ := (hap y0 hy0 z).1 hz
    exact ⟨w, ⟨y0, hy0, hw⟩, rfl⟩
  · rintro ⟨w, ⟨y0, hy0, hw⟩, rfl⟩
    exact ⟨bm y0, (hmem _).2 ⟨y0, hy0, rfl⟩, (hap y0 hy0 _).2 ⟨w, hw, rfl⟩⟩

/-- Every site lies in `Ω₁` of `levelGS j` (`j ≥ 1`). -/
theorem mem_Ω_one_levelGS (hj1 : 1 ≤ j) (hj : j ≤ K) (x : CTorus d L N₁ m₁ K) :
    x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 := by
  simp [levelGS, hj1]

/-- **T3 (thick sets).**  For a set `Y` inside the box of radius `ρ` of the first torus, the thick
set of the image of `Y` is the image of the thick set of `Y`.  Margin:
`2 ρ + 7 L^K < N₁ L^m₁ L^K` and the same for `N₁'`; the thick set lies in the box of radius
`ρ + 3 L^K`. -/
theorem thickSet_levelGS_image {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 7 * L ^ K < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 7 * L ^ K < (N₁' * L ^ m₁) * L ^ K) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : ∀ x ∈ Y, InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    thickSet (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (bm '' Y) =
      bm '' thickSet (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        Y := by
  have hdep := fun x (hx : x ∈ Y) => Set.ext_iff.1
    (resDep_levelGS_image (ϱ := ϱ) (m₁ := m₁) (N₁ := N₁) (N₁' := N₁') hj1 hj hn hn' (hY x hx))
  ext z
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨_, ⟨y, hy, rfl⟩, _, hz⟩)
    · exact ⟨y, Or.inl hy, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := (by simpa using (hdep y hy z).1 (by simpa using hz) :
        ∃ w, w ∈ resDep (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
          y ∧ bm w = z)
      exact ⟨w, Or.inr ⟨y, hy, mem_Ω_one_levelGS hj1 hj y, hw⟩, rfl⟩
  · rintro ⟨w, hw | ⟨y, hy, _, hwy⟩, rfl⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · refine Or.inr ⟨bm y, ⟨y, hy, rfl⟩, mem_Ω_one_levelGS hj1 hj _, ?_⟩
      have := (hdep y hy (bm w)).2 ⟨w, by simpa using hwy, rfl⟩
      simpa using this

end Dep

/-! ### Components of a set inside the box -/

section Component

variable {d n n' r : ℕ}

/-- The component of `X` in `V` goes into the component of the image, inside the box. -/
theorem componentOf_image_subset (hm : 2 * r + 1 < n) (hm' : 2 * r + 1 < n')
    {X V : Set (Torus d n)} (hV : ∀ x ∈ V, InBox d r n x) :
    boxMap n n' '' componentOf (latGraph d n) X V ⊆
      componentOf (latGraph d n') (boxMap n n' '' X) (boxMap n n' '' V) := by
  rintro _ ⟨z, ⟨y, hy, hpath⟩, rfl⟩
  refine ⟨boxMap n n' y, Set.mem_image_of_mem _ hy, ?_⟩
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    rename_i b c _
    refine ih.tail ⟨⟨fun h => hbc.1.1 (boxMap_inj (hm' := hm') (hV b hbc.2.1) (hV c hbc.2.2) h),
      (nbr_boxMap_iff hm hm' (hV b hbc.2.1) (hV c hbc.2.2)).1 hbc.1.2⟩,
      Set.mem_image_of_mem _ hbc.2.1, Set.mem_image_of_mem _ hbc.2.2⟩

/-- **Components correspond.**  For `X ⊆ V` inside the box, the component of `X` in `V` goes onto
the component of the image of `X` in the image of `V`. -/
theorem componentOf_image (hm : 2 * r + 1 < n) (hm' : 2 * r + 1 < n')
    {X V : Set (Torus d n)} (hXV : X ⊆ V) (hV : ∀ x ∈ V, InBox d r n x) :
    boxMap n n' '' componentOf (latGraph d n) X V =
      componentOf (latGraph d n') (boxMap n n' '' X) (boxMap n n' '' V) := by
  refine Set.Subset.antisymm (componentOf_image_subset hm hm' hV) fun z' hz' => ?_
  have hV' : ∀ x ∈ boxMap n n' '' V, InBox d r n' x := by
    rintro _ ⟨x, hx, rfl⟩; exact inBox_boxMap hm' (hV x hx)
  have hsub := componentOf_image_subset (r := r) (X := boxMap n n' '' X) hm' hm hV'
    (Set.mem_image_of_mem (boxMap n' n) hz')
  have hz'V : z' ∈ boxMap n n' '' V :=
    componentOf_subset _ (Set.image_mono hXV) hz'
  obtain ⟨w, hw, rfl⟩ := hz'V
  refine ⟨w, ?_, rfl⟩
  rw [boxMap_boxMap hm' (hV w hw), image_image_boxMap hm' (fun x hx => hV x (hXV hx)),
    image_image_boxMap hm' hV] at hsub
  exact hsub

end Component

/-! ### The decoupling index type -/

section Index

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j m₀ : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

omit [NeZero N₁] [NeZero N₁'] in
theorem side_facts (m₀ m₁ : ℕ) (j : ℕ) :
    0 < cellSide L m₀ m₁ j ∧ cellSide L m₀ m₁ j ≤ L * cellSide L m₀ m₁ j ∧
      L ^ (j + m₁) ≤ cellSide L m₀ m₁ j ∧ 1 ≤ L * cellSide L m₀ m₁ j := by
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  have hc := cellSide_pos (L := L) m₀ m₁ j
  refine ⟨hc, Nat.le_mul_of_pos_left _ hL, ?_, Nat.mul_pos hL hc⟩
  exact Nat.pow_le_pow_right hL (by omega)

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
theorem pow_dvd_side (hj : j ≤ K) (N : ℕ) : L ^ (j + m₁) ∣ (N * L ^ m₁) * L ^ K := by
  have : (N * L ^ m₁) * L ^ K = N * L ^ (m₁ + K) := by rw [pow_add]; ring
  rw [this]
  exact Dvd.dvd.mul_left (pow_dvd_pow L (by omega)) N

/-- The parameter cube `Pset` of a cube centre is the aligned box over its base point. -/
theorem pset_eq_box (hj : j ≤ K) {y0 : CTorus d L N₁ m₁ K} (hb : CubeBase (K := K) m₁ j y0) :
    Pset m₁ ((j, y0) : ℕ × CTorus d L N₁ m₁ K) = box y0 (L ^ (j + m₁)) := by
  have ha0 : 0 < L ^ (j + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hdv := pow_dvd_side (L := L) (m₁ := m₁) hj N₁
  have hc : cbase (L ^ (j + m₁)) y0 = y0 :=
    cbase_eq_of_mem_box hdv (a := L ^ (j + m₁)) (c := y0) hb (mem_box_self y0 ha0)
  ext x
  show (∀ μ, (x μ).val / L ^ (j + m₁) = (y0 μ).val / L ^ (j + m₁)) ↔ _
  rw [sameCell_iff_mem_box hdv ha0, hc]

section WithMargins

variable {ρ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (hj : j ≤ K)
  (hn : 2 * ρ + 5 * (L * cellSide L m₀ m₁ j) < (N₁ * L ^ m₁) * L ^ K)
  (hn' : 2 * ρ + 5 * (L * cellSide L m₀ m₁ j) < (N₁' * L ^ m₁) * L ^ K)

include hN hN' hj hn hn'

omit hN hN' hn' in
/-- **The patch `Pset` of a cube centre.**  The patch of the centre `(j, y0)` of the first torus,
with `y0` in the box of radius `ρ`, goes to the patch of the centre `(j, boxMap y0)`. -/
theorem pset_image {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hb : CubeBase (K := K) m₁ j y0) :
    bm '' Pset m₁ ((j, y0) : ℕ × CTorus d L N₁ m₁ K) =
      Pset m₁ ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  have hb' : CubeBase (K := K) m₁ j (bm y0) :=
    aligned_boxMap (pow_dvd_side hj N₁) (pow_dvd_side hj N₁') hb
  rw [pset_eq_box hj hb, pset_eq_box hj hb']
  exact image_box_boxMap (r := ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) (by omega)
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
    (fun x hx => inBox_mono (by omega) (inBox_of_mem_box_right (by omega) hy0 hx))

omit hN hN' hn hn' in
theorem mem_dcubes_levelGS (y0 : CTorus d L N₁ m₁ K) (b : CTorus d L N₁ m₁ K) :
    b ∈ Dcubes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) m₀
        ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      Aligned (cellSide L m₀ m₁ j) b ∧
        cellOf L m₀ m₁ ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ⊆ box b (L * cellSide L m₀ m₁ j) := by
  unfold Dcubes
  have h := layer_levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) hj j
  simp only [ite_true] at h
  simp only [Set.mem_ofPred_eq, h, Finset.coe_univ, Set.subset_univ, and_true]

omit hn' in
/-- Cubes `□'` of `D(P)` for `P = (j, y0)` with `y0` in the box of radius `ρ`: their points lie in
the box of radius `ρ + 2 S`, `S = L a_j`, and the corresponding cube is a cube of the second torus. -/
theorem dcubes_fwd {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0)
    {b : CTorus d L N₁ m₁ K}
    (hb : b ∈ Dcubes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) m₀
      ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) :
    (∀ z ∈ box b (L * cellSide L m₀ m₁ j),
      InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ K) z) ∧
    bm b ∈ Dcubes (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) m₀
      ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  rw [mem_dcubes_levelGS hj] at hb
  obtain ⟨hal, hsub⟩ := hb
  have hcellOf : ∀ (N : ℕ) [NeZero N] (y : CTorus d L N m₁ K),
      cellOf L m₀ m₁ ((j, y) : ℕ × CTorus d L N m₁ K) =
        box (cbase (cellSide L m₀ m₁ j) y) (cellSide L m₀ m₁ j) := fun _ _ _ => rfl
  have hy0cell : y0 ∈ cellOf L m₀ m₁ ((j, y0) : ℕ × CTorus d L N₁ m₁ K) := by
    rw [hcellOf]; exact mem_box_cbase hc0 y0
  have hbIn : InBox d (ρ + L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ K) b :=
    inBox_of_mem_box_left (by omega) hy0 (hsub hy0cell)
  have hzIn : ∀ z ∈ box b (L * cellSide L m₀ m₁ j),
      InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) ((N₁ * L ^ m₁) * L ^ K) z :=
    fun z hz => inBox_of_mem_box_right (by omega) hbIn hz
  refine ⟨hzIn, ?_⟩
  rw [mem_dcubes_levelGS hj]
  refine ⟨aligned_boxMap (cellSide_dvd (K := K) (m₁ := m₁) hN hj)
    (cellSide_dvd (K := K) (m₁ := m₁) hN' hj) hal, ?_⟩
  have hcellIn : ∀ x ∈ box (cbase (cellSide L m₀ m₁ j) y0) (cellSide L m₀ m₁ j),
      InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j)
        ((N₁ * L ^ m₁) * L ^ K) x :=
    fun x hx => inBox_mono (by omega) (inBox_of_mem_cell (by omega) hy0 hx)
  have himg : bm '' cellOf L m₀ m₁ ((j, y0) : ℕ × CTorus d L N₁ m₁ K) =
      cellOf L m₀ m₁ ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
    rw [hcellOf, hcellOf, image_box_boxMap (r := ρ + L * cellSide L m₀ m₁ j +
      L * cellSide L m₀ m₁ j) (by omega) hc0 hcellIn]
    rw [cbase_boxMap (r := ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j)
      (cellSide_dvd (K := K) (m₁ := m₁) hN hj) (cellSide_dvd (K := K) (m₁ := m₁) hN' hj) hc0
      (by omega) y0 hcellIn]
  rw [← himg, ← image_box_boxMap (r := ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j)
    (by omega) (by omega) hzIn]
  exact Set.image_mono hsub

/-- **The sites `D(P)` of a cube centre.**  For the centre `(j, y0)` of the first torus with `y0`
in the box of radius `ρ`, `D(P)` goes to `D(P')` for `P' = (j, boxMap y0)`. -/
theorem dsites_image {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    bm '' Dsites (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) m₀
        ((j, y0) : ℕ × CTorus d L N₁ m₁ K) =
      Dsites (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) m₀
        ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  obtain ⟨hc0, hcS, ha, hS⟩ := side_facts (L := L) m₀ m₁ j
  have hy0' : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm y0) := inBox_boxMap (by omega) hy0
  have hyy : bm' (bm y0) = y0 := boxMap_boxMap (by omega) hy0
  ext z
  constructor
  · rintro ⟨z0, hz0, rfl⟩
    simp only [Dsites, Set.mem_iUnion] at hz0 ⊢
    obtain ⟨b, hb, hz0⟩ := hz0
    obtain ⟨hzIn, hb'⟩ := dcubes_fwd hN hN' hj hn hy0 hb
    refine ⟨bm b, hb', ?_⟩
    rw [← image_box_boxMap (r := ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) (by omega)
      (by omega) hzIn]
    exact ⟨z0, hz0, rfl⟩
  · intro hz
    simp only [Dsites, Set.mem_iUnion] at hz
    obtain ⟨b', hb', hz⟩ := hz
    obtain ⟨hzIn', hb⟩ := dcubes_fwd (N₁ := N₁') (N₁' := N₁) hN' hN hj hn' hy0' hb'
    rw [hyy] at hb
    have hzin : InBox d (ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j)
        ((N₁' * L ^ m₁) * L ^ K) z := hzIn' z hz
    refine ⟨bm' z, ?_, boxMap_boxMap (by omega) hzin⟩
    simp only [Dsites, Set.mem_iUnion]
    refine ⟨bm' b', hb, ?_⟩
    rw [← image_box_boxMap (r := ρ + L * cellSide L m₀ m₁ j + L * cellSide L m₀ m₁ j) (by omega)
      (by omega) hzIn']
    exact ⟨z, hz, rfl⟩

end WithMargins

end Index

end Balaban.Polymer.TwoTorusStep
