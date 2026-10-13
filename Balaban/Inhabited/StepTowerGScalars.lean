/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerG
public import Balaban.Fluctuation.MarkedCommonLabels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scalar consequences of the general tower record

For `T : StepTowerG d L N κmin` the rate inequalities and the entropy-constant inequalities
that the mark records need at the constants `κ₀ = T.κ0`, `κ′ = T.κ'`, `κ_H = κ_G = 2 T.κdec - 1`,
`K_c = 2 (K₀ + 1)` and `K_c′ = K_c + rootUnionK d L T.m₀ T.m₁ T.κ0`.  Numbers and arithmetic only.
The fixed `d = L = 3`, `N = 2` statements of `MarksNumericsFromTower` are corollaries through
`StepTower.toG`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Polymer

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- `aEnt + 1 ≤ κ₀`. -/
theorem marks_hκ0 : aEnt d L + 1 ≤ T.κ0 := T.hκ0

/-- `aEnt + 2 ≤ κ₀`. -/
theorem marks_hκ0_two : aEnt d L + 2 ≤ T.κ0 := T.κ0_two

theorem marks_κdec_nonneg : 0 ≤ T.κdec := by
  have := T.κdec_lower; have := T.κ0_nonneg; linarith

/-- `0 ≤ κ′`. -/
theorem marks_hκ' : 0 ≤ T.κ' := by
  have := T.marks_κdec_nonneg; have := T.κ0_nonneg; rw [T.κ'_eq]; linarith

/-- `κ₀ ≤ κ′`. -/
theorem marks_κ0_le_κ' : T.κ0 ≤ T.κ' := by
  have := T.marks_κdec_nonneg; have := T.κ0_nonneg; rw [T.κ'_eq]; linarith

/-- `κ′ + 3κ₀ + c₁ + 3/2 ≤ κ_H = 2κ_dec - 1`. -/
theorem marks_hκ :
    T.κ' + 3 * T.κ0 + c1 d L + 3 / 2 ≤ 2 * T.κdec - 1 := by
  have := T.κdec_eq; have := T.κ0_nonneg; have := one_le_c1 d L; have := T.κdec_lower
  rw [T.κ'_eq]; linarith

/-- `κ_H ≤ κ_G` for `κ_G := κ_H = 2κ_dec - 1`. -/
theorem marks_hκG : 2 * T.κdec - 1 ≤ 2 * T.κdec - 1 := le_rfl

/-- `κ₀ ≤ κ_H`. -/
theorem marks_κ0_le_κH : T.κ0 ≤ 2 * T.κdec - 1 := by
  have := T.marks_hκ; have := T.marks_hκ'; have := T.κ0_nonneg; have := one_le_c1 d L
  linarith

/-- `κ′ ≤ κ_H`. -/
theorem marks_κ'_le_κH : T.κ' ≤ 2 * T.κdec - 1 := by
  have := T.marks_hκ; have := T.κ0_nonneg; have := one_le_c1 d L; linarith

/-- `κ_G = κ_H ≤ 2κ_dec`. -/
theorem marks_κG_le : 2 * T.κdec - 1 ≤ 2 * T.κdec := by linarith

/-- `0 ≤ κ_G`. -/
theorem marks_κG_nonneg : 0 ≤ 2 * T.κdec - 1 := by
  have := T.marks_κ0_le_κH; have := T.κ0_nonneg; linarith

/-- The entropy condition `aEnt + 1 ≤ 2κ_dec - 1 - κ₀`. -/
theorem marks_decay_entropy : aEnt d L + 1 ≤ 2 * T.κdec - 1 - T.κ0 := by
  have := T.marks_hκ; have := T.κ0_two; have := T.marks_hκ'; have := one_le_c1 d L
  have := T.κ0_nonneg; linarith

/-- `κ₀ ≤ κ_h` for the kernel rate `κ_h := κ′`. -/
theorem marks_hκh : T.κ0 ≤ T.κ' := T.marks_κ0_le_κ'

theorem marks_K0_pos : 0 < K0 d L T.κ0 := K0_pos d L T.κ0

/-- `K₀ + 1 ≤ K_c = 2 (K₀ + 1)`. -/
theorem marks_hKc_base : K0 d L T.κ0 + 1 ≤ 2 * (K0 d L T.κ0 + 1) := by
  have := T.marks_K0_pos; linarith

theorem marks_Kc_pos : 0 < 2 * (K0 d L T.κ0 + 1) := by
  have := T.marks_K0_pos; linarith

/-- `K₀ + 1 ≤ K_c′ = K_c + rootUnionK`. -/
theorem marks_hKc :
    K0 d L T.κ0 + 1 ≤ 2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0 :=
  T.marks_hKc_base.trans (commonK_ge (d := d) (L := L) (m₁ := T.m₁) T.m₀ T.κ0 _)

theorem marks_Kc'_pos : 0 < 2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0 :=
  lt_of_lt_of_le (by have := T.marks_K0_pos; linarith) T.marks_hKc

/-- The fields `hκ0` and `hKc` at the common system, in the form of `commonKc_ge`. -/
theorem marks_commonKc_ge :
    aEnt d L + 1 ≤ T.κ0 ∧
      K0 d L T.κ0 + 1 ≤ 2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0 :=
  commonKc_ge (d := d) (L := L) (m₁ := T.m₁) T.m₀ T.κ0_two T.marks_hKc_base

end StepTowerG

end Balaban.Inhabited
