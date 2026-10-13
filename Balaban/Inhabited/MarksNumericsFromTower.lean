/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepOutputPhysical
public import Balaban.Inhabited.StepTowerGScalars
public import Balaban.Inhabited.StepOutputPhysicalG
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
theorem StepTower.marks_hκ0 : aEnt 3 3 + 1 ≤ T.κ0 := T.toG.marks_hκ0

/-- `aEnt + 2 ≤ κ₀` (`hκ0` of `commonAct`, `extendRootUnion`, `rootUnion_entropy`). -/
theorem StepTower.marks_hκ0_two : aEnt 3 3 + 2 ≤ T.κ0 := T.toG.marks_hκ0_two

theorem StepTower.marks_κdec_nonneg : 0 ≤ T.κdec := T.toG.marks_κdec_nonneg

/-- `0 ≤ κ′` (`hκ'`). -/
theorem StepTower.marks_hκ' : 0 ≤ T.κ' := T.toG.marks_hκ'

/-- `κ₀ ≤ κ′`. -/
theorem StepTower.marks_κ0_le_κ' : T.κ0 ≤ T.κ' := T.toG.marks_κ0_le_κ'

/-- `κ′ + 3κ₀ + c₁ + 3/2 ≤ κ_H = 2κ_dec - 1` (`hκ`). -/
theorem StepTower.marks_hκ :
    T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ 2 * T.κdec - 1 := T.toG.marks_hκ

/-- `κ_H ≤ κ_G` for `κ_G := κ_H = 2κ_dec - 1` (`hκG`). -/
theorem StepTower.marks_hκG : 2 * T.κdec - 1 ≤ 2 * T.κdec - 1 := T.toG.marks_hκG

/-- `κ₀ ≤ κ_H` (`hκHge` of `marked_cubes_core`). -/
theorem StepTower.marks_κ0_le_κH : T.κ0 ≤ 2 * T.κdec - 1 := T.toG.marks_κ0_le_κH

/-- `κ′ ≤ κ_H`. -/
theorem StepTower.marks_κ'_le_κH : T.κ' ≤ 2 * T.κdec - 1 := T.toG.marks_κ'_le_κH

/-- `κ_G = κ_H ≤ 2κ_dec`. -/
theorem StepTower.marks_κG_le : 2 * T.κdec - 1 ≤ 2 * T.κdec := T.toG.marks_κG_le

/-- `0 ≤ κ_G`. -/
theorem StepTower.marks_κG_nonneg : 0 ≤ 2 * T.κdec - 1 := T.toG.marks_κG_nonneg

/-- The entropy condition of `MarkedSharpCount` item 4 at `a'' = κ₀`:
`aEnt + 1 ≤ 2κ_dec - 1 - κ₀`. -/
theorem StepTower.marks_decay_entropy : aEnt 3 3 + 1 ≤ 2 * T.κdec - 1 - T.κ0 :=
  T.toG.marks_decay_entropy

/-- `hκh` of `ObsMarks` for the kernel rate `κ_h := κ′`: `κ₀ ≤ κ_h`. -/
theorem StepTower.marks_hκh : T.κ0 ≤ T.κ' := T.toG.marks_hκh

/-- `ObsMarks.hRσ`: `1 < R_σ` is not a tower field; the discs `R_σ = 17/16` of `MarkRealDiscSlice`
satisfy it. -/
theorem marks_hRσ : (1 : ℝ) < 17 / 16 := by norm_num

end Rates

section Entropy

variable {κmin : ℝ} (T : StepTower κmin)

theorem StepTower.marks_K0_pos : 0 < K0 3 3 T.κ0 := T.toG.marks_K0_pos

/-- `hKc` at `K_c = 2 (K₀ + 1)`: `K₀ + 1 ≤ K_c`. -/
theorem StepTower.marks_hKc_base : K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) :=
  T.toG.marks_hKc_base

theorem StepTower.marks_Kc_pos : 0 < 2 * (K0 3 3 T.κ0 + 1) := T.toG.marks_Kc_pos

/-- `hKc` at `K_c′ = K_c + rootUnionK`: `K₀ + 1 ≤ K_c′`. -/
theorem StepTower.marks_hKc : K0 3 3 T.κ0 + 1 ≤ T.marksKc' := T.toG.marks_hKc

theorem StepTower.marks_Kc'_pos : 0 < T.marksKc' := T.toG.marks_Kc'_pos

/-- The fields `hκ0` and `hKc` at the common system, in the form of `commonKc_ge`. -/
theorem StepTower.marks_commonKc_ge :
    aEnt 3 3 + 1 ≤ T.κ0 ∧ K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) + rootUnionK 3 3 1 T.m₁ T.κ0 :=
  T.toG.marks_commonKc_ge

namespace StepTowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)

/-- `K_c′ ≤ K_tot` for a constants record with `K_c = 2 (K₀ + 1)` and
`K_all = max (2 K₀) rootUnionK` at the cell level `m` (the record of `exists_outputConsts`
at `m = T.m₀`). -/
theorem marks_Kc'_le_Ktot (m : ℕ) (C : StepOutputConsts d L) (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L m T.m₁ T.κ0)) :
    2 * (K0 d L T.κ0 + 1) + rootUnionK d L m T.m₁ T.κ0 ≤ C.Ktot := by
  rw [C.Ktot_eq, hKc, hKall]
  have := le_max_right (2 * K0 d L T.κ0) (rootUnionK d L m T.m₁ T.κ0)
  linarith

/-- `Θ(K_tot) ≤ Θ(K_c′)` for a record with `κ_H = 2κ_dec - 1`, `κ₀`, `κ′` of the tower. -/
theorem marks_theta_le_stepTheta (m : ℕ) (C : StepOutputConsts d L) (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L m T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') :
    C.theta ≤
      stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L m T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' := by
  unfold StepOutputConsts.theta
  rw [hH, h0, h']
  have hpos : 0 < 2 * (K0 d L T.κ0 + 1) + rootUnionK d L m T.m₁ T.κ0 := by
    have := T.marks_K0_pos
    have := rootUnionK_nonneg (d := d) (L := L) (m₁ := T.m₁) m T.κ0
    linarith
  exact commonStepTheta_le hpos (T.marks_Kc'_le_Ktot m C hKc hKall) _ _ _

end StepTowerG

/-- `K_c′ ≤ K_tot` of the physical constants record. -/
theorem StepTower.marks_Kc'_le_Ktot (h : stepHullMin ≤ κmin) :
    T.marksKc' ≤ (stepOutputPhysical T h).Ktot :=
  T.toG.marks_Kc'_le_Ktot 1 (stepOutputPhysical T h) rfl rfl

/-- `Θ(K_tot) ≤ Θ(K_c′)`: the physical threshold implies the strengthened `hε` at `K_c′`. -/
theorem StepTower.marks_theta_le_stepTheta (h : stepHullMin ≤ κmin) :
    (stepOutputPhysical T h).theta ≤
      stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' :=
  T.toG.marks_theta_le_stepTheta 1 (stepOutputPhysical T h) rfl rfl rfl rfl rfl

end Entropy

section Smallness

private theorem marks_pow_le_pow_three {x : ℝ} (hx : 1 ≤ x) (p : ℕ) : x ^ p ≤ x ^ (3 * p) :=
  pow_le_pow_right₀ hx (by omega)

/-- **T3, general tower.**  One `β₀` after the tower: for `β ≥ β₀`, every `k` and
`b = β L^{k (d-2)}`, every `ε_H` below `C_E (log b)^{3p}/√b + C_F (log b)^p/√b` is at most
`Θ(K_tot)` of a constants record `C` with the rates and label constants of the tower, hence at most
`Θ(K_c′)` (the strengthened `hε` at the enlarged constant). -/
theorem StepTowerG.exists_beta0_marks {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (m : ℕ) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L m T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') (p : ℕ)
    {CE CF : ℝ} (hCE : 0 ≤ CE) (hCF : 0 ≤ CF) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (β : ℝ) (k : ℕ), β₀ ≤ β → ∀ ε : ℝ,
      ε ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) →
      ε ≤ C.theta ∧
      ε ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L m T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' := by
  obtain ⟨b₁, hb₁, h1⟩ := exists_one_lt_obsRg (p := (p : ℝ)) (CR := 1) (s := 1 / 4) one_pos
    (by norm_num)
  obtain ⟨b₂, hb₂, h2⟩ := exists_obsRg_mul_le (p := (p : ℝ)) (CR := 1) (s := 1 / 4)
    (CU := CE + CF) one_pos (by norm_num) (by linarith) C.theta_pos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  refine ⟨max 3 (max b₁ b₂), le_max_left _ _, fun β k hβ ε hε => ?_⟩
  have hβ3 : 3 ≤ β := (le_max_left _ _).trans hβ
  have hβ1 : b₁ ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβ2 : b₂ ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hb : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := by nlinarith
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hlog : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) := by
    rw [Real.le_log_iff_exp_le hb0]
    have := Real.exp_one_lt_three
    linarith
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hbdef
  set ℓ := Real.log b with hℓ
  set s := Real.sqrt b with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hb0
  have hpow : ℓ ^ p ≤ ℓ ^ (3 * p) := marks_pow_le_pow_three hlog p
  have hpos : 0 ≤ ℓ ^ (3 * p) := by positivity
  have hrp : ℓ ^ (3 * (p : ℝ)) = ℓ ^ (3 * p) := by
    rw [show (3 * (p : ℝ)) = ((3 * p : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hsum : CE * ℓ ^ (3 * p) / s + CF * ℓ ^ p / s ≤ (CE + CF) * ℓ ^ (3 * p) / s := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hs0.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hCF]
  have hnn : 0 ≤ (CE + CF) * ℓ ^ (3 * p) / s := by positivity
  have hb1 : 1 ≤ b := by linarith
  have hε' : (CE + CF) * ℓ ^ (3 * p) / s ≤ (CE + CF) * obsW (p : ℝ) b ^ 3 / s := by
    rw [obsW_cube (p : ℝ) b hb1, hrp]
  have hR := h1 b (hβ1.trans hb)
  have key := h2 b _ (hβ2.trans hb) hε'
  have hkey : (CE + CF) * ℓ ^ (3 * p) / s ≤ C.theta := by
    have := mul_le_mul_of_nonneg_right hR.le hnn
    linarith
  have hεθ : ε ≤ C.theta := hε.trans (hsum.trans hkey)
  exact ⟨hεθ, hεθ.trans (T.marks_theta_le_stepTheta m C hKc hKall hH h0 h')⟩

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
  obtain ⟨β₀, h3, H⟩ := T.toG.exists_beta0_marks 1 (stepOutputPhysical T h) rfl rfl rfl rfl rfl p
    hCE hCF
  refine ⟨β₀, h3, fun β k hβ ε hε => H β k hβ ε ?_⟩
  have e : ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  exact (by simpa [e] using hε)

end Smallness

end Balaban.Inhabited
