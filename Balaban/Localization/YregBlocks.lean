/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecLogCutFactor
import Mathlib.Tactic.Linarith

/-!
# The thickened interaction cubes as unions of cells; components of `Yreg` as unions of blocks

Settles the last proviso `UnionOfBlocks` of `DecLogCutFactor.lean` (DET-CUT-FACTOR).

**T1 (shape of one box).** For a centre `q = (j, y₀)` with `y₀` a multiple of `B = L ^ (j + m₁)`
the thickened cube `hatBox q` has half-width `5/2 B + 3 L² L^j` (open, sup distance) around the
centre `y₀ + (B - 1)/2`. On the integers this is the interval `[y₀ - 2B - 3L^(j+2), y₀ + 3B +
3L^(j+2) - 1]` in each coordinate. The half-integer in `5/2` is compensated by the centre
`(B - 1)/2`, so no parity of `L` enters. As `m₁ ≥ 2`, `y₀`, `B` and `3 L^(j+2)` are multiples of
`L^(j+2)`: `hatBox q` is a union of cells of side `L^(j+2)` (`hatBox_sameCell`).

**T2 (which blocks matter).** A site of layer `n` in `hatBox q` has `n ≤ q.1 + 1`
(`layer_le_of_mem_hatBox`). A top-layer site (`n = k + 1`) therefore lies only in boxes with
`q.1 ≥ k`, whose cells have side at least `L^(k+2)`, a multiple of the block side `L^(k+1)`. So
the part of a component of `Yreg` in the top layer is a union of `(k+1)`-blocks
(`hatBox_sameCell_top`, `unionOfTopBlocks_of_isNnComp`). Lower-layer sites of `Ω₁` need not be
unions of `(k+1)`-blocks (blocks of the lower layers are smaller, and `Ω₁` itself is only a union
of `1`-blocks), so the full `UnionOfBlocks G Y'` of `DecLogCutFactor.lean` is not what is true; but
it is not what is used: `unitQ`, `unitP` only see top-layer sites (`IsUnitLattice.layer`). The
property that is proved, and used, is `UnionOfTopBlocks` (the same statement for a top-layer site
`y`); it coincides with `UnionOfBlocks` when `Ω₁ = Ω_{k+1}`.

The decay bound and the count of cut sets are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Coord

/-- The elementary integer inequality behind the cell description of the thickened cube:
for `w = A m + r` with `0 ≤ r < A`, `|w - (A b - 1)/2| < 5/2 A b + 3 A` iff
`-(2b+3) ≤ m ≤ 3b+2`. -/
theorem abs_lt_hat_iff {A b : ℕ} (hA : 0 < A) (m r : ℤ) (hr0 : 0 ≤ r) (hrA : r < A) :
    |(((A : ℤ) * m + r : ℤ) : ℝ) - (((A : ℝ) * b - 1) / 2)| < 5 / 2 * ((A : ℝ) * b) + 3 * A ↔
      -((2 * b + 3 : ℕ) : ℤ) ≤ m ∧ m ≤ ((3 * b + 2 : ℕ) : ℤ) := by
  have hA' : (0 : ℤ) < A := by exact_mod_cast hA
  rw [abs_lt]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    have e1 : (0 : ℝ) < ((2 * (A * m + r) + 4 * A * b + 6 * A + 1 : ℤ) : ℝ) := by
      push_cast; linarith
    have e2 : (0 : ℝ) < ((6 * A * b + 6 * A - 1 - 2 * (A * m + r) : ℤ) : ℝ) := by
      push_cast; linarith
    have e1' : (0 : ℤ) < 2 * (A * m + r) + 4 * A * b + 6 * A + 1 := by exact_mod_cast e1
    have e2' : (0 : ℤ) < 6 * A * b + 6 * A - 1 - 2 * (A * m + r) := by exact_mod_cast e2
    constructor
    · by_contra hc
      push Not at hc
      have : m + (2 * b + 3) ≤ -1 := by linarith
      nlinarith
    · by_contra hc
      push Not at hc
      have : 3 * b + 3 ≤ m := by linarith
      nlinarith
  · rintro ⟨h1, h2⟩
    have f1 : (0 : ℤ) ≤ A * (m + (2 * b + 3)) := by
      apply mul_nonneg hA'.le; linarith
    have f2 : (0 : ℤ) ≤ A * ((3 * b + 2) - m) := by
      apply mul_nonneg hA'.le; linarith
    have g1 : ((0 : ℤ) : ℝ) ≤ ((A * (m + (2 * b + 3)) : ℤ) : ℝ) := by exact_mod_cast f1
    have g2 : ((0 : ℤ) : ℝ) ≤ ((A * ((3 * b + 2) - m) : ℤ) : ℝ) := by exact_mod_cast f2
    have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
    have hrA' : (r : ℝ) + 1 ≤ A := by exact_mod_cast (by omega : r + 1 ≤ (A : ℤ))
    push_cast at g1 g2
    constructor <;> nlinarith


end Coord

section Box

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

omit [NeZero N₁] in
/-- Coordinatewise form of `hatBox`: with cells of side `A = L ^ (j + 2)`, the coordinate of `x` lies
in the thickened interval iff the cell index of `x` is within `[-(2b+3), 3b+2]` of that of the base,
periodically; here `b = L ^ (m₁ - 2)`, so `B = A b`. -/
theorem hat_coord_iff {j : ℕ} (hj : j ≤ K) (hm : 2 ≤ m₁) {y0 x : CTorus d L N₁ m₁ K}
    (hb : CubeBase m₁ j y0) (μ : Fin d) :
    (∃ p : ℤ, |((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < hatRad L m₁ j) ↔
    ∃ p : ℤ, -((2 * L ^ (m₁ - 2) + 3 : ℕ) : ℤ) ≤
        (((x μ).val / L ^ (j + 2) : ℕ) : ℤ) + p * ((((N₁ * L ^ m₁) * L ^ K) / L ^ (j + 2) : ℕ) : ℤ)
          - (((y0 μ).val / L ^ (j + 2) : ℕ) : ℤ) ∧
      (((x μ).val / L ^ (j + 2) : ℕ) : ℤ) + p * ((((N₁ * L ^ m₁) * L ^ K) / L ^ (j + 2) : ℕ) : ℤ)
          - (((y0 μ).val / L ^ (j + 2) : ℕ) : ℤ) ≤ ((3 * L ^ (m₁ - 2) + 2 : ℕ) : ℤ) := by
  have hApos : 0 < L ^ (j + 2) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  obtain ⟨n, hn⟩ : L ^ (j + 2) ∣ (N₁ * L ^ m₁) * L ^ K := by
    have : L ^ (j + 2) ∣ L ^ m₁ * L ^ K := by
      rw [← pow_add]; exact pow_dvd_pow L (by omega)
    exact this.trans ⟨N₁, by ring⟩
  have hnn : ((N₁ * L ^ m₁) * L ^ K) / L ^ (j + 2) = n := by
    rw [hn]; exact Nat.mul_div_cancel_left _ hApos
  rw [hnn]
  set A : ℕ := L ^ (j + 2) with hAdef
  set b : ℕ := L ^ (m₁ - 2) with hbdef
  have hBA : L ^ (j + m₁) = A * b := by
    rw [hAdef, hbdef, ← pow_add]; congr 1; omega
  obtain ⟨c, hc⟩ : A ∣ (y0 μ).val := by
    have h1 : L ^ (j + m₁) ∣ (y0 μ).val := Nat.dvd_of_mod_eq_zero (hb μ)
    rw [hBA] at h1
    exact (Dvd.intro _ rfl).trans h1
  set a : ℕ := (x μ).val / A with ha
  set r : ℕ := (x μ).val % A with hr
  have hx : (x μ).val = A * a + r := (Nat.div_add_mod _ _).symm
  have hcdiv : (y0 μ).val / A = c := by rw [hc]; exact Nat.mul_div_cancel_left _ hApos
  rw [hcdiv]
  have hrA : r < A := Nat.mod_lt _ hApos
  have hrad : hatRad L m₁ j = 5 / 2 * ((A : ℝ) * b) + 3 * A := by
    unfold hatRad
    have h1 : ((L : ℝ) ^ (j + m₁)) = (A : ℝ) * b := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hBA
      simpa using this
    rw [h1]
    have h2 : (A : ℝ) = (L : ℝ) ^ (j + 2) := by rw [hAdef]; push_cast; rfl
    rw [h2]; ring
  refine exists_congr fun p => ?_
  rw [hrad]
  have hB : ((L : ℝ) ^ (j + m₁)) = (A : ℝ) * b := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hBA
    simpa using this
  have e : ((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) =
      (((A : ℤ) * ((a : ℤ) + p * n - c) + (r : ℤ) : ℤ) : ℝ) - (((A : ℝ) * b - 1) / 2) := by
    have hNr : (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) = (A : ℝ) * n := by
      have := congrArg (fun t : ℕ => (t : ℝ)) hn
      simpa using this
    have hxr : ((x μ).val : ℝ) = (A : ℝ) * a + r := by exact_mod_cast hx
    have hyr : ((y0 μ).val : ℝ) = (A : ℝ) * c := by exact_mod_cast hc
    rw [hNr, hxr, hyr, hB]; push_cast; ring
  rw [e, abs_lt_hat_iff hApos _ _ (by positivity) (by exact_mod_cast hrA)]

/-- **T1. The thickened cube is a union of cells of side `L ^ (j + 2)`** (`m₁ ≥ 2`). -/
theorem hatBox_sameCell {j : ℕ} (hj : j ≤ K) (hm : 2 ≤ m₁) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q.1 = j) (hb : CubeBase m₁ j q.2) {x x' : CTorus d L N₁ m₁ K}
    (h : SameCell (L ^ (j + 2)) x x') : x ∈ hatBox q ↔ x' ∈ hatBox q := by
  unfold hatBox
  rw [mem_boxSet, mem_boxSet]
  unfold InBox
  rw [hq]
  refine forall_congr' fun μ => ?_
  rw [hat_coord_iff hj hm hb, hat_coord_iff hj hm hb, h μ]

end Box

end Balaban.Localization
