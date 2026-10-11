/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeAligned
public import Balaban.Background.Weights
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bumps of cubes (LOCALIZATION.md §1.2)

The cover of a cube-aligned generating set uses the cubes of side `M₁ ℓ_j = L ^ (j + m₁)`.  The
landed bump machinery (`Balaban.Background.bump`, W22) is stated for blocks of side `L ^ m` with
`m ≤ k` on the torus of side `N₀ L ^ k`; for cubes `j + m₁` may exceed the depth, so the cube
bump is the landed bump on the torus of side `N₁ L ^ (K + m₁)`, transported by `castT` from the
torus `(N₁ L ^ m₁) L ^ K` of a generating set with `N₀ = N₁ L ^ m₁` (the cubes tile the torus).

* `cubeBump m₁ j y0 x`: the periodized B-spline bump of the cube of base `y0` and layer `j`;
* `bump_ge_quarter_nbr`: the bump is at least `4⁻ᵈ` at `x`, `x ± e_μ` for `x` in the cell of its base
  (this gives the lower bound of the denominator at *every* neighbour, also at the wall);
* `cube_active_lift`, `card_cube_bases_le`: a nonzero bump has a point of the cube within
  `L ^ (j + m₁)` in each coordinate, and at most `3 ^ d` cubes of a layer are active at a point;
* `layer_bounds_cube`: layers of nearby sites differ by at most one (separation
  `ϱ ≥ 4 d L ^ (m₁ + 1)`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem cubeSide_eq (N₁ L m₁ K : ℕ) : (N₁ * L ^ m₁) * L ^ K = N₁ * L ^ (K + m₁) := by ring

/-- The identification of the torus `(N₁ L ^ m₁) L ^ K` with `N₁ L ^ (K + m₁)`. -/
def tor (m₁ : ℕ) (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) : Torus d (N₁ * L ^ (K + m₁)) :=
  castT (cubeSide_eq N₁ L m₁ K) x

omit [NeZero N₁] [NeZero L] in
theorem tor_val (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (μ : Fin d) :
    ((tor m₁ x) μ).val = (x μ).val := castT_val _ _ _

omit [NeZero N₁] [NeZero L] in
theorem tor_add_single (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (μ : Fin d) :
    tor m₁ (x + Pi.single μ 1) = tor m₁ x + Pi.single μ 1 := by
  unfold tor; rw [castT_add, castT_single]

omit [NeZero N₁] [NeZero L] in
theorem tor_sub_single (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (μ : Fin d) :
    tor m₁ (x - Pi.single μ 1) = tor m₁ x - Pi.single μ 1 := by
  unfold tor; rw [castT_sub, castT_single]

omit [NeZero N₁] [NeZero L] in
theorem tor_injective : Function.Injective (tor (d := d) (L := L) (N₁ := N₁) (K := K) m₁) :=
  castT_injective _

/-! ### Elementary bump bounds -/

theorem bsp_ge_quarter {t : ℝ} (h : |t| ≤ 3 / 4) : 1 / 4 ≤ bsp t := by
  rcases abs_le.1 h with ⟨h1, h2⟩
  rcases le_total t (-1 / 2) with h' | h'
  · rw [bsp_left (by linarith) h']; nlinarith
  rcases le_total t (1 / 2) with h'' | h''
  · rw [bsp_mid h' h'']; nlinarith
  · rw [bsp_right h'' (by linarith)]; nlinarith

section Quarter

variable {N₀ k : ℕ} [NeZero N₀]

theorem perFac_ge_quarter {m : ℕ} (hm : m ≤ k) {y0 : Torus d (N₀ * L ^ k)} (μ : Fin d) {t : ℝ}
    (h : |(t - bumpCentre m y0 μ) / (L : ℝ) ^ m| ≤ 3 / 4) : 1 / 4 ≤ perFac m y0 μ t :=
  le_trans (bsp_ge_quarter h)
    (bsp_le_perN (by linarith [one_le_sideRatio (N₀ := N₀) (L := L) hm]) (by linarith))

theorem cell_coord_bounds {m : ℕ} (hm : m ≤ k) {y0 x : Torus d (N₀ * L ^ k)}
    (hb : IsBase m y0) (h : jBlock d L N₀ k m x = jBlock d L N₀ k m y0) (ν : Fin d) :
    ((y0 ν).val : ℝ) ≤ (x ν).val ∧ ((x ν).val : ℝ) + 1 ≤ (y0 ν).val + (L : ℝ) ^ m := by
  have hlam : 0 < L ^ m := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) m
  have hq := val_div_eq_of_jBlock_eq hm h ν
  have hy := hb ν
  have h1 : (y0 ν).val = L ^ m * ((x ν).val / L ^ m) := by
    rw [hq]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hy)).symm
  have h2 := Nat.div_mul_le_self (x ν).val (L ^ m)
  have h3 := Nat.lt_div_mul_add (a := (x ν).val) hlam
  have n1 : (y0 ν).val ≤ (x ν).val := by
    have e := mul_comm (L ^ m) ((x ν).val / L ^ m)
    rw [h1]; linarith
  have n2 : (x ν).val + 1 ≤ (y0 ν).val + L ^ m := by
    have e := mul_comm (L ^ m) ((x ν).val / L ^ m)
    rw [h1]; linarith
  exact ⟨by exact_mod_cast n1, by exact_mod_cast n2⟩

/-- **Lower bound at the neighbours of a cell.**  If `x` is in the cell of the base `y0`, the bump
is at least `4⁻ᵈ` at `x + s e_μ`, `|s| ≤ 1` (in particular at `x` and `x ± e_μ`). -/
theorem bump_ge_quarter_nbr {m : ℕ} (hm : m ≤ k) (hlam : 2 ≤ L ^ m) {y0 x : Torus d (N₀ * L ^ k)}
    (hb : IsBase m y0) (h : jBlock d L N₀ k m x = jBlock d L N₀ k m y0) (μ : Fin d) (s : ℤ)
    (hs : |s| ≤ 1) :
    (1 / 4 : ℝ) ^ d ≤ bump m y0 (x + Pi.single μ ((s : ℤ) : ZMod (N₀ * L ^ k))) := by
  have hlam' : (2 : ℝ) ≤ (L : ℝ) ^ m := by exact_mod_cast hlam
  have hl0 : (0 : ℝ) < (L : ℝ) ^ m := by linarith
  calc (1 / 4 : ℝ) ^ d = ∏ _ν : Fin d, (1 / 4 : ℝ) := by simp
    _ ≤ _ := by
      refine Finset.prod_le_prod₀ (fun ν _ => by norm_num) fun ν _ => ?_
      set z := x + Pi.single μ ((s : ℤ) : ZMod (N₀ * L ^ k)) with hz
      obtain ⟨c1, c2⟩ := cell_coord_bounds hm hb h ν
      by_cases hν : ν = μ
      · subst hν
        have hlift := perFac_lift m y0 z ν (((x ν).val : ℤ) + s) (by simp [hz])
        rw [← hlift]
        push_cast
        refine perFac_ge_quarter hm ν ?_
        unfold bumpCentre
        rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0, abs_le]
        have hs' := abs_le.1 hs
        have hs1 : (-1 : ℝ) ≤ s := by exact_mod_cast hs'.1
        have hs2 : (s : ℝ) ≤ 1 := by exact_mod_cast hs'.2
        constructor <;> nlinarith
      · have : z ν = x ν := by simp [hz, Pi.single_eq_of_ne hν]
        rw [this]
        refine perFac_ge_quarter hm ν ?_
        unfold bumpCentre
        rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0, abs_le]
        constructor <;> nlinarith

end Quarter


/-! ### The cube bump -/

omit [NeZero N₁] [NeZero L] in
theorem castT_single_int {n n' : ℕ} (h : n = n') (μ : Fin d) (s : ℤ) :
    castT h (Pi.single μ ((s : ℤ) : ZMod n) : Torus d n) = Pi.single μ ((s : ℤ) : ZMod n') := by
  subst h; rfl

/-- The periodized bump of the cube of layer `j` and base `y0` (side `L ^ (j + m₁)`). -/
noncomputable def cubeBump (m₁ j : ℕ) (y0 x : Torus d ((N₁ * L ^ m₁) * L ^ K)) : ℝ :=
  bump (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (j + m₁) (tor m₁ y0) (tor m₁ x)

/-- `y0` is the base of a cube of layer `j`: its coordinates are divisible by `L ^ (j + m₁)`. -/
def CubeBase (m₁ j : ℕ) (y0 : Torus d ((N₁ * L ^ m₁) * L ^ K)) : Prop :=
  ∀ μ, (y0 μ).val % L ^ (j + m₁) = 0

omit [NeZero N₁] [NeZero L] in
theorem isBase_tor {j : ℕ} {y0 : Torus d ((N₁ * L ^ m₁) * L ^ K)} :
    IsBase (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (j + m₁) (tor m₁ y0) ↔
      CubeBase (K := K) m₁ j y0 := by
  unfold IsBase CubeBase
  simp only [tor_val]

omit [NeZero N₁] [NeZero L] in
theorem sameCell_tor {a : ℕ} {x y : Torus d ((N₁ * L ^ m₁) * L ^ K)} :
    SameCell a (tor m₁ x) (tor m₁ y) ↔ SameCell a x y := by
  unfold SameCell
  simp only [tor_val]

theorem cubeBump_nonneg {j : ℕ} (hj : j ≤ K) (y0 x : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    0 ≤ cubeBump m₁ j y0 x := bump_nonneg (by omega) _ _

theorem cubeBump_le {j : ℕ} (hj : j ≤ K) (y0 x : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    cubeBump m₁ j y0 x ≤ 4 ^ d := bump_le (by omega) _ _

theorem cubeBump_diff {j : ℕ} (hj : j ≤ K) (hlam : 2 ≤ L ^ (j + m₁))
    (y0 x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (μ : Fin d) :
    |cubeBump m₁ j y0 (x + Pi.single μ 1) - cubeBump m₁ j y0 x| ≤
        150 * 4 ^ d / (L : ℝ) ^ (j + m₁) ∧
    |cubeBump m₁ j y0 (x - Pi.single μ 1) - cubeBump m₁ j y0 x| ≤
        150 * 4 ^ d / (L : ℝ) ^ (j + m₁) ∧
    |cubeBump m₁ j y0 (x + Pi.single μ 1) + cubeBump m₁ j y0 (x - Pi.single μ 1) -
        2 * cubeBump m₁ j y0 x| ≤ 20 * 4 ^ d / ((L : ℝ) ^ (j + m₁)) ^ 2 := by
  have h1 := bump_diff1 (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (m := j + m₁) (by omega) hlam
    (tor m₁ y0) (tor m₁ x) μ
  have h2 := bump_diff2 (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (m := j + m₁) (by omega) hlam
    (tor m₁ y0) (tor m₁ x) μ
  unfold cubeBump
  rw [tor_add_single, tor_sub_single]
  exact ⟨h1.1, h1.2, h2⟩

theorem cubeBump_ge_quarter_nbr {j : ℕ} (hj : j ≤ K) (hlam : 2 ≤ L ^ (j + m₁))
    {y0 x z : Torus d ((N₁ * L ^ m₁) * L ^ K)} (hb : CubeBase m₁ j y0)
    (h : SameCell (L ^ (j + m₁)) x y0) (μ : Fin d)
    (hz : z = x ∨ z = x + Pi.single μ 1 ∨ z = x - Pi.single μ 1) :
    (1 / 4 : ℝ) ^ d ≤ cubeBump m₁ j y0 z := by
  have hcell : jBlock d L N₁ (K + m₁) (j + m₁) (tor m₁ x) = jBlock d L N₁ (K + m₁) (j + m₁) (tor m₁ y0) :=
    jBlock_eq_of_sameCell (sameCell_tor.2 h)
  have hbb := isBase_tor.2 hb
  have key := fun s : ℤ => bump_ge_quarter_nbr (d := d) (L := L) (N₀ := N₁) (k := K + m₁)
    (m := j + m₁) (by omega) hlam hbb hcell μ s
  have e : ∀ s : ℤ, tor m₁ (x + Pi.single μ ((s : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) =
      tor m₁ x + Pi.single μ ((s : ℤ) : ZMod (N₁ * L ^ (K + m₁))) := fun s => by
    unfold tor; rw [castT_add, castT_single_int]
  unfold cubeBump
  rcases hz with rfl | rfl | rfl
  · have := key 0 (by simp)
    rw [Int.cast_zero, Pi.single_zero, add_zero] at this
    exact this
  · have := key 1 (by simp)
    have e1 := e 1
    simp only [Int.cast_one] at e1 this
    rw [← e1] at this
    exact this
  · have := key (-1) (by simp)
    have e1 : tor m₁ x + Pi.single μ (((-1 : ℤ)) : ZMod (N₁ * L ^ (K + m₁))) =
        tor m₁ (x - Pi.single μ 1) := by
      rw [tor_sub_single, sub_eq_add_neg, ← Pi.single_neg]
      simp
    rw [← e1]
    exact this


/-! ### Lifts and counting -/

theorem cube_active_lift {j : ℕ} (hj : j ≤ K) {y0 x' : Torus d ((N₁ * L ^ m₁) * L ^ K)}
    (hb : CubeBase m₁ j y0) (h : cubeBump m₁ j y0 x' ≠ 0) :
    ∃ t u : Fin d → ℤ, (∀ μ, ((t μ : ℤ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) = x' μ) ∧
      SameCell (L ^ (j + m₁)) (intTorus u : Torus d ((N₁ * L ^ m₁) * L ^ K)) y0 ∧
      ∀ μ, (t μ - u μ).natAbs ≤ L ^ (j + m₁) := by
  obtain ⟨t, u, ht, hju, hd⟩ := exists_lift_near (d := d) (L := L) (N₀ := N₁) (k := K + m₁)
    (m := j + m₁) (by omega) (isBase_tor.2 hb) h
  refine ⟨t, u, ?_, ?_, hd⟩
  · have e : tor m₁ x' = intTorus t := funext fun μ => (ht μ).symm
    unfold tor at e
    have := congrArg (castT (cubeSide_eq N₁ L m₁ K).symm) e
    rw [castT_castT, castT_intTorus] at this
    intro μ
    rw [this]
    rfl
  · have hsc := sameCell_of_jBlock_eq (by omega : j + m₁ ≤ K + m₁) hju
    have hv : ∀ μ, ((intTorus u : Torus d (N₁ * L ^ (K + m₁))) μ).val =
        ((intTorus u : Torus d ((N₁ * L ^ m₁) * L ^ K)) μ).val := by
      intro μ
      have := castT_val (cubeSide_eq N₁ L m₁ K) (intTorus u : Torus d ((N₁ * L ^ m₁) * L ^ K)) μ
      rwa [castT_intTorus] at this
    intro μ
    have := hsc μ
    rw [hv μ, tor_val] at this
    exact this

open Classical in
/-- At most `3 ^ d` cubes of layer `j` have a nonzero bump at `x`. -/
theorem card_cube_bases_le {j : ℕ} (hj : j ≤ K) (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    ((Finset.univ : Finset (Torus d ((N₁ * L ^ m₁) * L ^ K))).filter
      (fun y0 => CubeBase m₁ j y0 ∧ cubeBump m₁ j y0 x ≠ 0)).card ≤ 3 ^ d := by
  set T : Finset (Torus d (N₁ * L ^ (K + m₁))) := (Finset.univ.filter
      (fun y0 => IsBase (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (j + m₁) y0 ∧
        bump (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (j + m₁) y0 (tor m₁ x) ≠ 0)) with hT
  calc _ ≤ T.card := Finset.card_le_card_of_injOn (tor m₁) (fun y0 hy => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
        rw [hT, Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, isBase_tor.2 hy.1, hy.2⟩) (tor_injective.injOn)
    _ ≤ 3 ^ d := card_active_bases_le (by omega) _

section Own

variable {N₀ k : ℕ} [NeZero N₀]

theorem ownBase_sameCell {n : ℕ} (x : Torus d (N₀ * L ^ k)) : SameCell (L ^ n) x (ownBase n x) := by
  intro μ
  rw [ownBase_val]
  exact (Nat.mul_div_cancel _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n)).symm

theorem ownBase_cubeBase {n : ℕ} (x : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    CubeBase m₁ n (ownBase (n + m₁) x) := fun μ => by
  rw [ownBase_val]; exact Nat.mul_mod_left _ _

end Own

end Balaban.Localization
