/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerDataCell
public import Balaban.Polymer.TwoTorusGapTowerRootFUnitBg
public import Balaban.Polymer.TwoTorusGapTowerRootFBoxArith

/-!
# The tower's root and site of a cell of the exact quarter box (blocker 7)

The cell lemmas of `TwoTorusGapTowerDataCell` for cells `a` with `4 |a_μ| ≤ K` (the cell box
`|a_μ| ≤ K / 4` reached by the fine quarter box of Root-F when `4 ∣ K`) instead of `4 |a_μ| < K`,
and the arithmetic of the recentring box for such cells.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section Cell

/-- Centred representatives of a point in the quarter box survive the box maps. -/
theorem valMinAbs_mul_cell_le {n D K : ℕ} [NeZero n] (hD : 0 < D) (h : n = D * K) (hK : 2 ≤ K)
    {a : ℤ} (ha : 4 * |a| ≤ (K : ℤ)) :
    (((a * (D : ℤ) : ℤ) : ZMod n)).valMinAbs = a * (D : ℤ) := by
  subst h
  have hn : 4 * a.natAbs ≤ K := by
    rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  refine valMinAbs_intCast_of_abs_le (r := (a.natAbs * D)) ?_ ?_
  · have h1 : 2 * a.natAbs + 2 ≤ K := by omega
    have : D * (2 * a.natAbs + 2) ≤ D * K := Nat.mul_le_mul_left D h1
    nlinarith
  · rw [abs_mul, Int.abs_eq_natAbs, Nat.abs_cast]
    push_cast
    exact le_refl _


set_option hygiene false in
local notation "zrP[" a "," n "," m "," k "]" =>
  (fun μ => ((a μ * ((L ^ (1 + m) : ℕ) : ℤ) : ℤ) : ZMod (n * L ^ m * L ^ (k + 1 - (k + 1)))) :
    RootIdx d L n m (k + 1))
set_option hygiene false in
local notation "xsP[" a "," n "," m "," k "]" =>
  (fun μ => ((a μ * ((cellSide L 1 m (k + 1) : ℕ) : ℤ) : ℤ) : ZMod ((n * L ^ m) * L ^ (k + 1))) :
    CTorus d L n m (k + 1))


section Points

variable {d L : ℕ} [NeZero L]

/-- The root of the cell `a` lies in the cell `a`. -/
theorem root_cell_eq_le {n m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ} (ha : ∀ μ, 4 * |a μ| ≤ (K : ℤ)) :
    (fun μ => ((((rootCube (m₀ := 1) (zrP[a, n, m, k])).1 μ).val / cellSide L 1 m (k + 1) : ℕ) :
      ZMod K).valMinAbs) = a := by
  funext μ
  have hD : 0 < L ^ (1 + m) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn := root_side_eq hside
  rw [rootIdx_cell_val]
  have := cellIndex_intCast_mul hD hn (a μ)
  rw [this]
  exact valMinAbs_intCast_of_abs_le (r := (a μ).natAbs) (by
    have : 4 * (a μ).natAbs ≤ K := by
      have := ha μ
      rcases abs_cases (a μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    omega) (by rw [Int.abs_eq_natAbs])

/-- The roots of two tori correspond under the box maps. -/
theorem root_box_eq_le {n n' m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ}
    (ha : ∀ μ, 4 * |a μ| ≤ (K : ℤ)) :
    (zrP[a, n', m, k]) = boxMap (n * L ^ m * L ^ (k + 1 - (k + 1)))
      (n' * L ^ m * L ^ (k + 1 - (k + 1))) (zrP[a, n, m, k]) := by
  funext μ
  have hD : 0 < L ^ (1 + m) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn := root_side_eq hside
  have := valMinAbs_mul_cell_le hD hn hK (ha μ)
  simp only [boxMap]
  rw [this]

/-- The site `a aK` lies in the cell `a`. -/
theorem site_cell_eq_le {n m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ} (ha : ∀ μ, 4 * |a μ| ≤ (K : ℤ)) :
    (fun μ => (((((xsP[a, n, m, k]) μ).val / cellSide L 1 m (k + 1) : ℕ) : ZMod K).valMinAbs)) =
      a := by
  funext μ
  have hD : 0 < cellSide L 1 m (k + 1) := cellSide_pos _ _ _
  have := cellIndex_intCast_mul hD hside (a μ)
  dsimp only
  rw [this]
  exact valMinAbs_intCast_of_abs_le (r := (a μ).natAbs) (by
    have : 4 * (a μ).natAbs ≤ K := by
      have := ha μ
      rcases abs_cases (a μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    omega) (by rw [Int.abs_eq_natAbs])

/-- The sites of two tori correspond under the box maps. -/
theorem site_box_eq_le {n n' m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ}
    (ha : ∀ μ, 4 * |a μ| ≤ (K : ℤ)) :
    (xsP[a, n', m, k]) = boxMap ((n * L ^ m) * L ^ (k + 1)) ((n' * L ^ m) * L ^ (k + 1))
      (xsP[a, n, m, k]) := by
  funext μ
  have hD : 0 < cellSide L 1 m (k + 1) := cellSide_pos _ _ _
  have := valMinAbs_mul_cell_le hD hside hK (ha μ)
  simp only [boxMap]
  rw [this]


end Points

/-- The arithmetic of the recentring box at the site `a aK` for `4 b ≤ K`: with
`Ds = A ((K - 26) / 25 + 1) - 1` and `61 ≤ K`, `2 ((r + b A) + r) + 1 < A K` for
`r = Ds + (Ds + 1) / 4`. -/
theorem recentre_arith_le {A K b Ds : ℕ} (hA : 0 < A) (hK : 61 ≤ K) (hb : 4 * b ≤ K)
    (hDs : Ds = A * ((K - 26) / 25 + 1) - 1) :
    2 * ((Ds + (Ds + 1) / 4 + b * A) + (Ds + (Ds + 1) / 4)) + 1 < A * K := by
  have hq : 25 * ((K - 26) / 25 + 1) + 1 ≤ K := by omega
  have hS : 0 < A * ((K - 26) / 25 + 1) := Nat.mul_pos hA (by omega)
  have h1 : 25 * (A * ((K - 26) / 25 + 1)) + A ≤ A * K := by
    nlinarith [Nat.mul_le_mul_left A hq]
  have h2 : 4 * (b * A) ≤ A * K := by nlinarith
  omega

end Cell

end Balaban.Polymer.TwoTorusStep
