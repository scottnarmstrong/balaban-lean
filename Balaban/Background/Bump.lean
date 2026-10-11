/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.BSpline
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Periodic bumps of blocks on the torus (LEMMA53-astra.md, §3)

For a layer-`m` block with base site `y0` (all coordinates divisible by `L ^ m`), the bump at `x`
is the product over coordinates of the periodized spline `perN` evaluated at the lift of `x` to
`[0, S)`.  The bump is independent of the lift of `x` (`perFac_lift`), and moving `x` along `±e_μ`
changes only the factor of coordinate `μ` (`bump_add_single`), which gives the first and second
difference bounds of `bump_diff1`, `bump_diff2`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Finset

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem perN_add_int_mul (r α : ℝ) (q : ℤ) : perN r (α + q * r) = perN r α := by
  unfold perN
  rw [← finsum_comp_equiv (Equiv.addRight q) (f := fun p : ℤ => bsp (α + p * r))]
  refine finsum_congr fun p => ?_
  simp only [Equiv.coe_addRight]
  congr 1
  push_cast; ring

/-- The centre of the cube of the base `y0` at scale `L ^ m`, coordinate `μ`. -/
noncomputable def bumpCentre (m : ℕ) (y0 : Torus d (N₀ * L ^ k)) (μ : Fin d) : ℝ :=
  ((y0 μ).val : ℝ) + ((L : ℝ) ^ m - 1) / 2

/-- One coordinate factor of the periodized bump, at the real position `t`. -/
noncomputable def perFac (m : ℕ) (y0 : Torus d (N₀ * L ^ k)) (μ : Fin d) (t : ℝ) : ℝ :=
  perN (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) ((t - bumpCentre m y0 μ) / (L : ℝ) ^ m)

/-- The periodized bump of the block of base `y0` and scale `L ^ m`, at the site `x`. -/
noncomputable def bump (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) : ℝ :=
  ∏ μ, perFac m y0 μ ((x μ).val : ℝ)

theorem one_le_sideRatio {m : ℕ} (hm : m ≤ k) :
    1 ≤ ((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hN : (1 : ℝ) ≤ N₀ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N₀)
  rw [le_div_iff₀ (by positivity)]
  push_cast
  have : (L : ℝ) ^ m ≤ (L : ℝ) ^ k := pow_le_pow_right₀ hL hm
  nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) k]

theorem perFac_nonneg {m : ℕ} (hm : m ≤ k) (y0 : Torus d (N₀ * L ^ k)) (μ : Fin d) (t : ℝ) :
    0 ≤ perFac m y0 μ t :=
  perN_nonneg (by linarith [one_le_sideRatio (N₀ := N₀) (L := L) hm]) _

theorem perFac_le {m : ℕ} (hm : m ≤ k) (y0 : Torus d (N₀ * L ^ k)) (μ : Fin d) (t : ℝ) :
    perFac m y0 μ t ≤ 4 :=
  perN_le (one_le_sideRatio hm) _

/-- Lift invariance of the periodized factor. -/
theorem perFac_lift (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) (t : ℤ)
    (ht : ((t : ℤ) : ZMod (N₀ * L ^ k)) = x μ) :
    perFac m y0 μ (t : ℝ) = perFac m y0 μ ((x μ).val : ℝ) := by
  have hv : (((x μ).val : ℕ) : ℤ) = t % ((N₀ * L ^ k : ℕ) : ℤ) := by
    rw [← ht]; exact ZMod.val_intCast t
  have hdecomp := Int.emod_add_mul_ediv t ((N₀ * L ^ k : ℕ) : ℤ)
  rw [← hv] at hdecomp
  set q : ℤ := t / ((N₀ * L ^ k : ℕ) : ℤ) with hq
  have htR : (t : ℝ) = ((x μ).val : ℝ) + q * ((N₀ * L ^ k : ℕ) : ℝ) := by
    have : ((((x μ).val : ℕ) : ℤ) + ((N₀ * L ^ k : ℕ) : ℤ) * q : ℤ) = t := hdecomp
    have h2 := congrArg (fun z : ℤ => (z : ℝ)) this
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h2
    linarith
  unfold perFac
  have hlam : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have : (((t : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m) =
      ((((x μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m) +
        q * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) := by
    rw [htR]; field_simp; ring
  rw [this]
  exact perN_add_int_mul _ _ _

theorem bump_add_single (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) (s : ℤ) :
    bump m y0 (x + Pi.single μ ((s : ℤ) : ZMod (N₀ * L ^ k))) =
      perFac m y0 μ (((x μ).val : ℝ) + s) *
        ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) := by
  unfold bump
  rw [← mul_prod_erase univ _ (mem_univ μ)]
  congr 1
  · have := perFac_lift m y0 (x + Pi.single μ ((s : ℤ) : ZMod (N₀ * L ^ k))) μ
      (((x μ).val : ℤ) + s) (by simp)
    simpa using this.symm
  · refine prod_congr rfl fun ν hν => ?_
    have : ν ≠ μ := (mem_erase.1 hν).1
    simp [Pi.single_eq_of_ne this]

omit [NeZero N₀] [NeZero L] in
theorem bump_eq_mul (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    bump m y0 x = perFac m y0 μ ((x μ).val : ℝ) *
      ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) := by
  unfold bump
  rw [← mul_prod_erase univ _ (mem_univ μ)]

theorem bump_nonneg {m : ℕ} (hm : m ≤ k) (y0 x : Torus d (N₀ * L ^ k)) : 0 ≤ bump m y0 x :=
  prod_nonneg fun μ _ => perFac_nonneg hm y0 μ _

theorem bump_le {m : ℕ} (hm : m ≤ k) (y0 x : Torus d (N₀ * L ^ k)) : bump m y0 x ≤ 4 ^ d := by
  calc bump m y0 x ≤ ∏ _μ : Fin d, (4 : ℝ) :=
        Finset.prod_le_prod₀ (fun μ _ => perFac_nonneg hm y0 μ _) fun μ _ => perFac_le hm y0 μ _
    _ = 4 ^ d := by simp

theorem rest_nonneg {m : ℕ} (hm : m ≤ k) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    0 ≤ ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) :=
  prod_nonneg fun ν _ => perFac_nonneg hm y0 ν _

theorem rest_le {m : ℕ} (hm : m ≤ k) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) ≤ 4 ^ d := by
  calc _ ≤ ∏ _ν ∈ univ.erase μ, (4 : ℝ) :=
        Finset.prod_le_prod₀ (fun ν _ => perFac_nonneg hm y0 ν _) fun ν _ => perFac_le hm y0 ν _
    _ = 4 ^ (univ.erase μ).card := by simp
    _ ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (by
        rw [card_erase_of_mem (mem_univ μ)]; simp)

/-- The first and second differences of a single factor. -/
theorem perFac_diff {m : ℕ} (hm : m ≤ k) (hlam : 2 ≤ L ^ m) (y0 : Torus d (N₀ * L ^ k))
    (μ : Fin d) (t : ℝ) :
    |perFac m y0 μ (t + 1) - perFac m y0 μ t| ≤ 150 / (L : ℝ) ^ m ∧
    |perFac m y0 μ (t - 1) - perFac m y0 μ t| ≤ 150 / (L : ℝ) ^ m ∧
    |perFac m y0 μ (t + 1) + perFac m y0 μ (t - 1) - 2 * perFac m y0 μ t| ≤
      20 / ((L : ℝ) ^ m) ^ 2 := by
  have hlam' : (2 : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlam
  have hlam0 : (0 : ℝ) < (L : ℝ) ^ m := by linarith
  have hs : |1 / (L : ℝ) ^ m| ≤ 1 / 2 := by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ hlam0 (by norm_num)]; linarith
  have hr := one_le_sideRatio (N₀ := N₀) (L := L) hm
  set α := (t - bumpCentre m y0 μ) / (L : ℝ) ^ m with hα
  have e1 : (t + 1 - bumpCentre m y0 μ) / (L : ℝ) ^ m = α + 1 / (L : ℝ) ^ m := by
    rw [hα]; field_simp; ring
  have e2 : (t - 1 - bumpCentre m y0 μ) / (L : ℝ) ^ m = α - 1 / (L : ℝ) ^ m := by
    rw [hα]; field_simp; ring
  have f0 : perFac m y0 μ t = perN (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) α := rfl
  have f1 : perFac m y0 μ (t + 1) = perN (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m)
      (α + 1 / (L : ℝ) ^ m) := by unfold perFac; rw [e1]
  have f2 : perFac m y0 μ (t - 1) = perN (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m)
      (α - 1 / (L : ℝ) ^ m) := by unfold perFac; rw [e2]
  have d1 := perN_diff1 hr α (1 / (L : ℝ) ^ m) hs
  have d1' := perN_diff1 hr α (-(1 / (L : ℝ) ^ m)) (by rwa [abs_neg])
  have d2 := perN_diff2 hr α (1 / (L : ℝ) ^ m) hs
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (L : ℝ) ^ m)] at d1
  rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (L : ℝ) ^ m)] at d1'
  refine ⟨?_, ?_, ?_⟩
  · rw [f0, f1]; refine d1.trans (le_of_eq ?_); field_simp
  · rw [f0, f2]
    rw [← sub_eq_add_neg] at d1'
    refine d1'.trans (le_of_eq ?_); field_simp
  · rw [f0, f1, f2]; refine d2.trans (le_of_eq ?_); field_simp


theorem bump_add_one (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    bump m y0 (x + Pi.single μ 1) = perFac m y0 μ (((x μ).val : ℝ) + 1) *
      ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) := by
  have := bump_add_single m y0 x μ 1
  simpa using this

theorem bump_sub_one (m : ℕ) (y0 x : Torus d (N₀ * L ^ k)) (μ : Fin d) :
    bump m y0 (x - Pi.single μ 1) = perFac m y0 μ (((x μ).val : ℝ) - 1) *
      ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) := by
  have h := bump_add_single m y0 x μ (-1)
  have e : x + Pi.single μ (((-1 : ℤ)) : ZMod (N₀ * L ^ k)) = x - Pi.single μ 1 := by
    rw [sub_eq_add_neg]; congr 1; simp [Pi.single_neg]
  rw [e] at h
  rw [h]
  simp [sub_eq_add_neg]

/-- First differences of the bump along a coordinate direction. -/
theorem bump_diff1 {m : ℕ} (hm : m ≤ k) (hlam : 2 ≤ L ^ m) (y0 x : Torus d (N₀ * L ^ k))
    (μ : Fin d) :
    |bump m y0 (x + Pi.single μ 1) - bump m y0 x| ≤ 150 * 4 ^ d / (L : ℝ) ^ m ∧
    |bump m y0 (x - Pi.single μ 1) - bump m y0 x| ≤ 150 * 4 ^ d / (L : ℝ) ^ m := by
  obtain ⟨h1, h2, -⟩ := perFac_diff hm hlam y0 μ ((x μ).val : ℝ)
  have hR0 := rest_nonneg hm y0 x μ
  have hR1 := rest_le hm y0 x μ
  have hlam0 : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (2 : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlam
    linarith
  constructor
  · rw [bump_add_one, bump_eq_mul m y0 x μ, ← sub_mul, abs_mul, abs_of_nonneg hR0]
    calc _ ≤ 150 / (L : ℝ) ^ m * 4 ^ d := mul_le_mul h1 hR1 hR0 (by positivity)
      _ = _ := by ring
  · rw [bump_sub_one, bump_eq_mul m y0 x μ, ← sub_mul, abs_mul, abs_of_nonneg hR0]
    calc _ ≤ 150 / (L : ℝ) ^ m * 4 ^ d := mul_le_mul h2 hR1 hR0 (by positivity)
      _ = _ := by ring

/-- Centred second differences of the bump along a coordinate direction. -/
theorem bump_diff2 {m : ℕ} (hm : m ≤ k) (hlam : 2 ≤ L ^ m) (y0 x : Torus d (N₀ * L ^ k))
    (μ : Fin d) :
    |bump m y0 (x + Pi.single μ 1) + bump m y0 (x - Pi.single μ 1) - 2 * bump m y0 x| ≤
      20 * 4 ^ d / ((L : ℝ) ^ m) ^ 2 := by
  obtain ⟨-, -, h3⟩ := perFac_diff hm hlam y0 μ ((x μ).val : ℝ)
  have hR0 := rest_nonneg hm y0 x μ
  have hR1 := rest_le hm y0 x μ
  have hlam0 : (0 : ℝ) < (L : ℝ) ^ m := by
    have : (2 : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlam
    linarith
  have e : bump m y0 (x + Pi.single μ 1) + bump m y0 (x - Pi.single μ 1) - 2 * bump m y0 x =
      (perFac m y0 μ (((x μ).val : ℝ) + 1) + perFac m y0 μ (((x μ).val : ℝ) - 1) -
        2 * perFac m y0 μ ((x μ).val : ℝ)) *
        ∏ ν ∈ univ.erase μ, perFac m y0 ν ((x ν).val : ℝ) := by
    rw [bump_add_one, bump_sub_one, bump_eq_mul m y0 x μ]; ring
  rw [e, abs_mul, abs_of_nonneg hR0]
  calc _ ≤ 20 / ((L : ℝ) ^ m) ^ 2 * 4 ^ d := mul_le_mul h3 hR1 hR0 (by positivity)
    _ = _ := by ring

/-! ### Bases, own-block lower bound, nearness -/

/-- `y0` is the base site of a layer-`m` block: all its coordinates are divisible by `L ^ m`. -/
def IsBase (m : ℕ) (y0 : Torus d (N₀ * L ^ k)) : Prop := ∀ μ, (y0 μ).val % L ^ m = 0

theorem val_div_eq_of_jBlock_eq {m : ℕ} (hm : m ≤ k) {x y : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k m x = jBlock d L N₀ k m y) (μ : Fin d) :
    (x μ).val / L ^ m = (y μ).val / L ^ m := by
  have h1 := congrFun h μ
  unfold jBlock at h1
  rw [Balaban.blockMap_apply, Balaban.blockMap_apply] at h1
  have e1 := Balaban.blockCoord_val (side_eq (N₀ := N₀) (L := L) (k := k) hm) (x μ)
  have e2 := Balaban.blockCoord_val (side_eq (N₀ := N₀) (L := L) (k := k) hm) (y μ)
  rw [h1] at e1
  omega

theorem bump_ge_of_jBlock_eq {m : ℕ} (hm : m ≤ k) {y0 x : Torus d (N₀ * L ^ k)}
    (hb : IsBase m y0) (h : jBlock d L N₀ k m x = jBlock d L N₀ k m y0) :
    (1 / 2 : ℝ) ^ d ≤ bump m y0 x := by
  have hlam : 0 < L ^ m := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) m
  calc (1 / 2 : ℝ) ^ d = ∏ _μ : Fin d, (1 / 2 : ℝ) := by simp
    _ ≤ bump m y0 x := by
      refine Finset.prod_le_prod₀ (fun μ _ => by norm_num) fun μ _ => ?_
      have hq := val_div_eq_of_jBlock_eq hm h μ
      have hy := hb μ
      have h1 : (y0 μ).val = L ^ m * ((x μ).val / L ^ m) := by
        rw [hq]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hy)).symm
      have h2 := Nat.div_mul_le_self (x μ).val (L ^ m)
      have h3 := Nat.lt_div_mul_add (a := (x μ).val) hlam
      have hr := one_le_sideRatio (N₀ := N₀) (L := L) hm
      have n1 : (y0 μ).val ≤ (x μ).val := by
        have e := mul_comm (L ^ m) ((x μ).val / L ^ m)
        rw [h1]; linarith
      have n2 : (x μ).val + 1 ≤ (y0 μ).val + L ^ m := by
        have e := mul_comm (L ^ m) ((x μ).val / L ^ m)
        rw [h1]; linarith
      have r1 : ((y0 μ).val : ℝ) ≤ ((x μ).val : ℝ) := by exact_mod_cast n1
      have r2 : ((x μ).val : ℝ) + 1 ≤ ((y0 μ).val : ℝ) + (L : ℝ) ^ m := by exact_mod_cast n2
      have hl0 : (0 : ℝ) < (L : ℝ) ^ m := by
        have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      have hα : |(((x μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m| ≤ 1 / 2 := by
        rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0, abs_le]
        unfold bumpCentre
        constructor <;> nlinarith
      unfold perFac
      refine le_trans (bsp_ge_half hα) (bsp_le_perN (by linarith) ?_)
      linarith [(abs_le.1 hα).1, (abs_le.1 hα).2, abs_le.2 ⟨(abs_le.1 hα).1, (abs_le.1 hα).2⟩]


theorem int_div_eq_of_bounds {lam q u : ℤ} (hlam : 0 < lam) (h1 : lam * q ≤ u)
    (h2 : u < lam * q + lam) : u / lam = q := by
  apply le_antisymm
  · have : u / lam < q + 1 := (Int.ediv_lt_iff_lt_mul hlam).2 (by nlinarith)
    omega
  · exact (Int.le_ediv_iff_mul_le hlam).2 (by nlinarith)

omit [NeZero N₀] [NeZero L] in
theorem natCast_val_eq_div_mul {m : ℕ} {y0 : Torus d (N₀ * L ^ k)} (hb : IsBase m y0) (μ : Fin d) :
    ((y0 μ).val : ℤ) = (L ^ m : ℕ) * (((y0 μ).val / L ^ m : ℕ) : ℤ) := by
  have := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb μ)))
  exact_mod_cast this.symm

/-- A nonzero bump comes with lifts of `x` and a point of the block within `L ^ m` in each
coordinate. -/
theorem exists_lift_near {m : ℕ} (hm : m ≤ k) {y0 x : Torus d (N₀ * L ^ k)} (hb : IsBase m y0)
    (hne : bump m y0 x ≠ 0) :
    ∃ t u : Fin d → ℤ, (∀ μ, ((t μ : ℤ) : ZMod (N₀ * L ^ k)) = x μ) ∧
      jBlock d L N₀ k m (castTorus u) = jBlock d L N₀ k m y0 ∧
      ∀ μ, (t μ - u μ).natAbs ≤ L ^ m := by
  have hlam : 0 < L ^ m := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) m
  have hlamR : (0 : ℝ) < (L : ℝ) ^ m := by exact_mod_cast hlam
  have hper : ∀ μ, ∃ p : ℤ, |(((x μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m +
      p * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m)| < 3 / 2 := fun μ =>
    exists_of_perN_ne_zero (Finset.prod_ne_zero_iff.1 hne μ (mem_univ μ))
  choose p hp using hper
  set t : Fin d → ℤ := fun μ => ((x μ).val : ℤ) + p μ * ((N₀ * L ^ k : ℕ) : ℤ) with ht
  have hS0 : (((N₀ * L ^ k : ℕ) : ℤ) : ZMod (N₀ * L ^ k)) = 0 := by
    rw [Int.cast_natCast]; exact ZMod.natCast_self _
  have hX : ∀ (z : Torus d (N₀ * L ^ k)) μ, (((z μ).val : ℤ) : ZMod (N₀ * L ^ k)) = z μ :=
    fun z μ => by rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val _
  have hbounds : ∀ μ, 2 * t μ - 2 * ((y0 μ).val : ℤ) - (((L ^ m : ℕ) : ℤ) - 1) <
        3 * ((L ^ m : ℕ) : ℤ) ∧ -(3 * ((L ^ m : ℕ) : ℤ)) <
        2 * t μ - 2 * ((y0 μ).val : ℤ) - (((L ^ m : ℕ) : ℤ) - 1) := by
    intro μ
    have h1 := hp μ
    have e : (((x μ).val : ℝ) - bumpCentre m y0 μ) / (L : ℝ) ^ m +
        p μ * (((N₀ * L ^ k : ℕ) : ℝ) / (L : ℝ) ^ m) =
        (((x μ).val : ℝ) - bumpCentre m y0 μ + p μ * ((N₀ * L ^ k : ℕ) : ℝ)) / (L : ℝ) ^ m := by
      field_simp
    rw [e, abs_div, abs_of_pos hlamR, div_lt_iff₀ hlamR, abs_lt] at h1
    have hT : ((t μ : ℤ) : ℝ) = ((x μ).val : ℝ) + p μ * ((N₀ * L ^ k : ℕ) : ℝ) := by
      simp [ht]
    unfold bumpCentre at h1
    constructor
    · have : (2 * ((t μ : ℤ) : ℝ) - 2 * (((y0 μ).val : ℤ) : ℝ) - ((((L ^ m : ℕ) : ℤ) : ℝ) - 1)) <
          3 * (((L ^ m : ℕ) : ℤ) : ℝ) := by
        push_cast at hT ⊢; push_cast at h1; linarith [h1.1, h1.2]
      exact_mod_cast this
    · have : -(3 * (((L ^ m : ℕ) : ℤ) : ℝ)) <
          (2 * ((t μ : ℤ) : ℝ) - 2 * (((y0 μ).val : ℤ) : ℝ) - ((((L ^ m : ℕ) : ℤ) : ℝ) - 1)) := by
        push_cast at hT ⊢; push_cast at h1; linarith [h1.1, h1.2]
      exact_mod_cast this
  set u : Fin d → ℤ := fun μ => max ((y0 μ).val : ℤ)
    (min (t μ) ((y0 μ).val + ((L ^ m : ℕ) : ℤ) - 1)) with hu
  refine ⟨t, u, ?_, ?_, ?_⟩
  · intro μ
    simp only [ht]
    rw [Int.cast_add, Int.cast_mul, hS0, mul_zero, add_zero, hX x μ]
  · have hy : (castTorus (fun μ => ((y0 μ).val : ℤ)) : Torus d (N₀ * L ^ k)) = y0 := by
      funext μ; rw [castTorus_apply]; exact hX y0 μ
    have key := jBlock_castTorus_eq (d := d) (L := L) (N₀ := N₀) (k := k) hm u
      (fun μ => ((y0 μ).val : ℤ)) fun μ => ?_
    · rwa [hy] at key
    have hq := natCast_val_eq_div_mul hb μ
    have hlamZ : (0 : ℤ) < ((L ^ m : ℕ) : ℤ) := by exact_mod_cast hlam
    set q : ℤ := (((y0 μ).val / L ^ m : ℕ) : ℤ) with hqdef
    have e1 : ((y0 μ).val : ℤ) / ((L ^ m : ℕ) : ℤ) = q :=
      int_div_eq_of_bounds hlamZ (by rw [← hq]) (by rw [← hq]; omega)
    rw [e1]
    refine int_div_eq_of_bounds hlamZ ?_ ?_
    · rw [← hq]; exact le_max_left _ _
    · rw [← hq]
      have : u μ ≤ (y0 μ).val + ((L ^ m : ℕ) : ℤ) - 1 :=
        max_le (by omega) (min_le_right _ _)
      omega
  · intro μ
    obtain ⟨b1, b2⟩ := hbounds μ
    have hlamZ : (0 : ℤ) < ((L ^ m : ℕ) : ℤ) := by exact_mod_cast hlam
    simp only [hu]
    generalize L ^ m = lamN at *
    omega

end Balaban.Background
