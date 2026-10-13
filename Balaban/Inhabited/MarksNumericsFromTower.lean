/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepOutputPhysical
public import Balaban.Fluctuation.MarkedCommonLabels
public import Balaban.Inhabited.SourceActivityFromTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The numerical fields of the mark records at the shared tower

Numbers and arithmetic only.  For `T : StepTower κmin` the constants of the mark records
(`InterpMarks`, `E1MarksC`, `ParamMarkFamily`, `ObsMarks`, `StepActivityBound(C)`) are
`κ₀ = T.κ0`, `κ′ = T.κ'`, `κ_H = 2 T.κdec - 1`, `κ_G = κ_H` (the decay rate of the marks of
`MarkedSharpCount` is `2κ_dec - 1`), `K_c = 2 (K₀ + 1)` and, on the common label system of the
roots, the enlarged constant `K_c′ = K_c + rootUnionK`.

* `StepTower.marks_*`: the rate inequalities.
* `StepTower.marks_hKc`, `marks_Kc'_le_Ktot`, `marks_theta_le_stepTheta`: the entropy constant.
* `exists_beta0_marks`: one `β₀` after the tower, `A₁`, `p`, `C_E`, `C_F`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Polymer

/-- The enlarged entropy constant `K_c′ = K_c + rootUnionK` of the common label system. -/
noncomputable abbrev StepTower.marksKc' {κmin : ℝ} (T : StepTower κmin) : ℝ :=
  2 * (K0 3 3 T.κ0 + 1) + rootUnionK 3 3 1 T.m₁ T.κ0

section Rates

variable {κmin : ℝ} (T : StepTower κmin)

/-- `aEnt + 1 ≤ κ₀` (`hκ0` of `InterpMarks`, `StepActivityBound(C)`, `ParamMarkFamily` users). -/
theorem StepTower.marks_hκ0 : aEnt 3 3 + 1 ≤ T.κ0 := T.hκ0

/-- `aEnt + 2 ≤ κ₀` (`hκ0` of `commonAct`, `extendRootUnion`, `rootUnion_entropy`). -/
theorem StepTower.marks_hκ0_two : aEnt 3 3 + 2 ≤ T.κ0 := T.κ0_two

theorem StepTower.marks_κdec_nonneg : 0 ≤ T.κdec := by
  have := T.κdec_lower; have := T.κ0_nonneg; linarith

/-- `0 ≤ κ′` (`hκ'`). -/
theorem StepTower.marks_hκ' : 0 ≤ T.κ' := by
  have := T.marks_κdec_nonneg; have := T.κ0_nonneg; rw [T.κ'_eq]; linarith

/-- `κ₀ ≤ κ′`. -/
theorem StepTower.marks_κ0_le_κ' : T.κ0 ≤ T.κ' := by
  have := T.marks_κdec_nonneg; have := T.κ0_nonneg; rw [T.κ'_eq]; linarith

/-- `κ′ + 3κ₀ + c₁ + 3/2 ≤ κ_H = 2κ_dec - 1` (`hκ`). -/
theorem StepTower.marks_hκ :
    T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ 2 * T.κdec - 1 := by
  have := T.κdec_eq; have := T.κ0_nonneg; have := one_le_c1 3 3; have := T.κdec_lower
  rw [T.κ'_eq]; linarith

/-- `κ_H ≤ κ_G` for `κ_G := κ_H = 2κ_dec - 1` (`hκG`). -/
theorem StepTower.marks_hκG : 2 * T.κdec - 1 ≤ 2 * T.κdec - 1 := le_rfl

/-- `κ₀ ≤ κ_H` (`hκHge` of `marked_cubes_core`). -/
theorem StepTower.marks_κ0_le_κH : T.κ0 ≤ 2 * T.κdec - 1 := by
  have := T.marks_hκ; have := T.marks_hκ'; have := T.κ0_nonneg; have := one_le_c1 3 3
  linarith

/-- `κ′ ≤ κ_H`. -/
theorem StepTower.marks_κ'_le_κH : T.κ' ≤ 2 * T.κdec - 1 := by
  have := T.marks_hκ; have := T.κ0_nonneg; have := one_le_c1 3 3; linarith

/-- `κ_G = κ_H ≤ 2κ_dec`. -/
theorem StepTower.marks_κG_le : 2 * T.κdec - 1 ≤ 2 * T.κdec := by linarith

/-- `0 ≤ κ_G`. -/
theorem StepTower.marks_κG_nonneg : 0 ≤ 2 * T.κdec - 1 := by
  have := T.marks_κ0_le_κH; have := T.κ0_nonneg; linarith

/-- The entropy condition of `MarkedSharpCount` item 4 at `a'' = κ₀`:
`aEnt + 1 ≤ 2κ_dec - 1 - κ₀`. -/
theorem StepTower.marks_decay_entropy : aEnt 3 3 + 1 ≤ 2 * T.κdec - 1 - T.κ0 := by
  have := T.marks_hκ; have := T.κ0_two; have := T.marks_hκ'; have := one_le_c1 3 3
  have := T.κ0_nonneg; linarith

/-- `hκh` of `ObsMarks` for the kernel rate `κ_h := κ′`: `κ₀ ≤ κ_h`. -/
theorem StepTower.marks_hκh : T.κ0 ≤ T.κ' := T.marks_κ0_le_κ'

/-- `ObsMarks.hRσ`: `1 < R_σ` is not a tower field; the discs `R_σ = 17/16` of `MarkRealDiscSlice`
satisfy it. -/
theorem marks_hRσ : (1 : ℝ) < 17 / 16 := by norm_num

end Rates

section Entropy

variable {κmin : ℝ} (T : StepTower κmin)

theorem StepTower.marks_K0_pos : 0 < K0 3 3 T.κ0 := K0_pos 3 3 T.κ0

/-- `hKc` at `K_c = 2 (K₀ + 1)`: `K₀ + 1 ≤ K_c`. -/
theorem StepTower.marks_hKc_base : K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) := by
  have := T.marks_K0_pos; linarith

theorem StepTower.marks_Kc_pos : 0 < 2 * (K0 3 3 T.κ0 + 1) := by
  have := T.marks_K0_pos; linarith

/-- `hKc` at `K_c′ = K_c + rootUnionK`: `K₀ + 1 ≤ K_c′`. -/
theorem StepTower.marks_hKc : K0 3 3 T.κ0 + 1 ≤ T.marksKc' :=
  T.marks_hKc_base.trans (commonK_ge (d := 3) (L := 3) (m₁ := T.m₁) 1 T.κ0 _)

theorem StepTower.marks_Kc'_pos : 0 < T.marksKc' :=
  lt_of_lt_of_le (by have := T.marks_K0_pos; linarith) T.marks_hKc

/-- The fields `hκ0` and `hKc` at the common system, in the form of `commonKc_ge`. -/
theorem StepTower.marks_commonKc_ge :
    aEnt 3 3 + 1 ≤ T.κ0 ∧ K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) + rootUnionK 3 3 1 T.m₁ T.κ0 :=
  commonKc_ge (d := 3) (L := 3) (m₁ := T.m₁) 1 T.κ0_two T.marks_hKc_base

/-- `K_c′ ≤ K_tot` of the physical constants record. -/
theorem StepTower.marks_Kc'_le_Ktot (h : stepHullMin ≤ κmin) :
    T.marksKc' ≤ (stepOutputPhysical T h).Ktot := by
  have := rootUnionK_le_stepOutputPhysical T h
  have e : (stepOutputPhysical T h).Ktot = (stepOutputPhysical T h).Kc +
      (stepOutputPhysical T h).Kall := (stepOutputPhysical T h).Ktot_eq
  rw [e]
  show 2 * (K0 3 3 T.κ0 + 1) + rootUnionK 3 3 1 T.m₁ T.κ0 ≤ _ + _
  have e2 : (stepOutputPhysical T h).Kc = 2 * (K0 3 3 T.κ0 + 1) := rfl
  rw [e2]; linarith

/-- `Θ(K_tot) ≤ Θ(K_c′)`: the physical threshold implies the strengthened `hε` at `K_c′`. -/
theorem StepTower.marks_theta_le_stepTheta (h : stepHullMin ≤ κmin) :
    (stepOutputPhysical T h).theta ≤
      stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' :=
  commonStepTheta_le (d := 3) (L := 3) T.marks_Kc'_pos (T.marks_Kc'_le_Ktot h) _ _ _

end Entropy

section Smallness

private theorem marks_pow_le_pow_three {x : ℝ} (hx : 1 ≤ x) (p : ℕ) : x ^ p ≤ x ^ (3 * p) :=
  pow_le_pow_right₀ hx (by omega)

/-- **T3.**  One `β₀` after the tower: for `β ≥ β₀`, every `k` and `b = β 3^k`, every `ε_H` below
`C_E (log b)^{3p}/√b + C_F (log b)^p/√b` is at most `Θ(K_tot)` of the physical record, hence at most
`Θ(K_c′)` (the strengthened `hε` at the enlarged constant). -/
theorem exists_beta0_marks {κmin : ℝ} (T : StepTower κmin) (h : stepHullMin ≤ κmin) (p : ℕ)
    {CE CF : ℝ} (hCE : 0 ≤ CE) (hCF : 0 ≤ CF) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (β : ℝ) (k : ℕ), β₀ ≤ β → ∀ ε : ℝ,
      ε ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) →
      ε ≤ (stepOutputPhysical T h).theta ∧
      ε ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' := by
  obtain ⟨β₁, hβ₁, H⟩ := exists_beta0_stepOutput (stepOutputPhysical T h)
    (CU := CE + CF) (CR := 1) (s := 1 / 4) (p := (p : ℝ)) (by linarith) one_pos
    (by norm_num) (by norm_num)
  refine ⟨max 3 β₁, le_max_left _ _, fun β k hβ ε hε => ?_⟩
  have hβ3 : 3 ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : β₁ ≤ β := (le_max_right _ _).trans hβ
  have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hb : β ≤ β * 3 ^ k := by nlinarith
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hlog : 1 ≤ Real.log (β * 3 ^ k) := by
    rw [Real.le_log_iff_exp_le hb0]
    have := Real.exp_one_lt_three
    linarith
  set ℓ := Real.log (β * 3 ^ k) with hℓ
  set s := Real.sqrt (β * 3 ^ k) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hb0
  have hpow : ℓ ^ p ≤ ℓ ^ (3 * p) := marks_pow_le_pow_three hlog p
  have hpos : 0 ≤ ℓ ^ (3 * p) := by positivity
  have hrp : ℓ ^ (3 * (p : ℝ)) = ℓ ^ (3 * p) := by
    rw [show (3 * (p : ℝ)) = ((3 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hsum : CE * ℓ ^ (3 * p) / s + CF * ℓ ^ p / s ≤ (CE + CF) * ℓ ^ (3 * p) / s := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hs0.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hCF]
  have hnn : 0 ≤ (CE + CF) * ℓ ^ (3 * (p : ℝ)) / s := by rw [hrp]; positivity
  have key := (H β k hβ1 _ hnn le_rfl).2.2
  rw [hrp] at key
  have hεθ : ε ≤ (stepOutputPhysical T h).theta := hε.trans (hsum.trans key)
  exact ⟨hεθ, hεθ.trans (T.marks_theta_le_stepTheta h)⟩

end Smallness

end Balaban.Inhabited
