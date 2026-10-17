/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.D7ReserveArithmetic
public import Balaban.LargeField.R.RRemovedFactor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The residual loss `L_res` of the removed outcome: the arithmetic of (III.8.4) (W878)

`notes/phase1/LF4R-PLAN.md`, leaf 2.  Definition III.8.6 of the reconstruction: `C_R` is a constant
with
`[N/2 log 2 + N p₀ log λ + C_vol] (M crit_k)^d + D₀^d (N p₀ log λ + C_vol + C_Ẽ)
  + (C'_E λ + C'_E)(M crit_k)^d + C_♮ λ^{2d+1} + 10 ≤ C_R λ^{2d+1}`   (III.8.4)
for `λ = λ̂_k ≥ λ_*`, where `C_vol = log (v_N max {3, C₆}^N A₀^N)`.

`C_R` is the free typing constant `Typing.CR`; Definition III.8.6 ("the least such constant") is not
a landed definition, and none is added.  So the arithmetic is stated for any constant `C_R` that is
at least an explicit constant (`lres_lhs_le`), for `λ ≥ 1`; `C_vol` is a real number in the
statement (the value `log (v_N max {3, C₆}^N A₀^N)` is an instance).  The crit bound is the landed
`crit_le_critBar`.  Then `C_R ≤ A₂ λ^{p₂ - 2d - 1}` for `λ ≥ max {1, C_R/A₂}`
(`CR_le_A2_pow_of_large`, `p₂ ≥ 2d + 3`), which gives the hypothesis `hCR` of
`removed_kerBound_logC_of_window` (`CR_window_of_large`).
-/

@[expose] public section

namespace Balaban.LargeField

theorem lres_term1 {n pp x Cvol Q Z : ℝ} (hn : 0 ≤ n) (hpp : 0 ≤ pp) (hx : 1 ≤ x)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ Z) :
    (n / 2 * Real.log 2 + n * pp * Real.log x + Cvol) * Q ≤
      (n / 2 * Real.log 2 + n * pp + |Cvol|) * (x * Z) := by
  have hl2 : 0 ≤ n / 2 * Real.log 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have hNp : 0 ≤ n * pp := mul_nonneg hn hpp
  have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x)]
  have hA : n / 2 * Real.log 2 + n * pp * Real.log x + Cvol ≤
      (n / 2 * Real.log 2 + n * pp + |Cvol|) * x := by
    nlinarith [mul_nonneg hl2 (sub_nonneg.2 hx), mul_le_mul_of_nonneg_left hlx hNp,
      le_abs_self Cvol, mul_nonneg (abs_nonneg Cvol) (sub_nonneg.2 hx)]
  have hA0 : 0 ≤ n / 2 * Real.log 2 + n * pp + |Cvol| := by positivity
  have hZ : x * Q ≤ x * Z := mul_le_mul_of_nonneg_left hQ (by linarith)
  calc _ ≤ ((n / 2 * Real.log 2 + n * pp + |Cvol|) * x) * Q :=
        mul_le_mul_of_nonneg_right hA hQ0
    _ = (n / 2 * Real.log 2 + n * pp + |Cvol|) * (x * Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ hA0

theorem lres_term2 {n pp x Cvol CEt D U : ℝ} (hn : 0 ≤ n) (hpp : 0 ≤ pp) (hx : 1 ≤ x)
    (hD : 0 ≤ D) (hxU : x ≤ U) :
    D * (n * pp * Real.log x + Cvol + CEt) ≤ D * (n * pp + |Cvol| + |CEt|) * U := by
  have hNp : 0 ≤ n * pp := mul_nonneg hn hpp
  have hlx : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x)]
  have h1U : 1 ≤ U := hx.trans hxU
  have hB : n * pp * Real.log x + Cvol + CEt ≤ (n * pp + |Cvol| + |CEt|) * U := by
    nlinarith [mul_le_mul_of_nonneg_left hlx hNp, mul_le_mul_of_nonneg_left hxU hNp,
      le_abs_self Cvol, le_abs_self CEt, mul_nonneg (abs_nonneg Cvol) (sub_nonneg.2 h1U),
      mul_nonneg (abs_nonneg CEt) (sub_nonneg.2 h1U)]
  calc _ ≤ D * ((n * pp + |Cvol| + |CEt|) * U) := mul_le_mul_of_nonneg_left hB hD
    _ = _ := by ring

theorem lres_term3 {CE' x Q Z : ℝ} (hCE' : 0 ≤ CE') (hx : 1 ≤ x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Z) :
    (CE' * x + CE') * Q ≤ 2 * CE' * (x * Z) := by
  have h1 : CE' * x + CE' ≤ 2 * CE' * x := by nlinarith [mul_nonneg hCE' (sub_nonneg.2 hx)]
  have hZ0 : 0 ≤ Z := hQ0.trans hQ
  calc _ ≤ (2 * CE' * x) * Q := mul_le_mul_of_nonneg_right h1 hQ0
    _ ≤ (2 * CE' * x) * Z := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = _ := by ring

/-- The explicit constant of (III.8.4): with `a₁ = N/2 log 2 + N p₀ + |C_vol|`,
`cB = 2 c₀ R_base + 2 c₀ + 10` (so `crit̄(x) ≤ cB x²`),
`(a₁ + 2 C'_E) M^d cB^d + D₀^d (N p₀ + |C_vol| + |C_Ẽ|) + C_♮ + 10`. -/
theorem lres_lhs_le (S : Setting) (ok : S.Ok) {x : ℝ} (hx : 1 ≤ x) {crit : ℕ}
    (hcrit : (crit : ℝ) ≤ S.critBar x) (N : ℕ) {Cvol CEt CE' Cnat D0 CR : ℝ}
    (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ CR) :
    ((N : ℝ) / 2 * Real.log 2 + N * S.p0 * Real.log x + Cvol) * ((S.M : ℝ) * crit) ^ S.d +
      D0 ^ S.d * (N * S.p0 * Real.log x + Cvol + CEt) +
      (CE' * x + CE') * ((S.M : ℝ) * crit) ^ S.d + Cnat * x ^ (2 * S.d + 1) + 10 ≤
    CR * x ^ (2 * S.d + 1) := by
  have hRb := ok.Rb_pos
  have hc0 : (0 : ℝ) ≤ S.c0 := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := by linarith
  set cB : ℝ := 2 * S.c0 * S.Rb + 2 * S.c0 + 10 with hcB
  set U : ℝ := x ^ (2 * S.d + 1) with hU
  have hx2 : 1 ≤ x ^ 2 := one_le_pow₀ hx
  have hcr : (crit : ℝ) ≤ cB * x ^ 2 := by
    refine hcrit.trans ?_
    unfold Typing.critBar
    nlinarith [mul_nonneg hc0 (sub_nonneg.2 hx2)]
  have hcr0 : (0 : ℝ) ≤ crit := Nat.cast_nonneg _
  set W : ℝ := (S.M : ℝ) ^ S.d * cB ^ S.d with hW
  have hQ : ((S.M : ℝ) * crit) ^ S.d ≤ W * x ^ (2 * S.d) := by
    calc ((S.M : ℝ) * crit) ^ S.d ≤ ((S.M : ℝ) * (cB * x ^ 2)) ^ S.d := by gcongr
      _ = _ := by rw [hW, mul_pow, mul_pow, ← pow_mul]; ring
  have hQ0 : 0 ≤ ((S.M : ℝ) * crit) ^ S.d := by positivity
  have hxU : x ≤ U := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ U := pow_le_pow_right₀ hx (by omega)
  have h1U : 1 ≤ U := one_le_pow₀ hx
  have hxZ : x * (W * x ^ (2 * S.d)) = W * U := by rw [hU, pow_succ]; ring
  have t1 := lres_term1 (n := (N : ℝ)) (pp := (S.p0 : ℝ)) (Cvol := Cvol) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hx hQ0 hQ
  have t2 := lres_term2 (n := (N : ℝ)) (pp := (S.p0 : ℝ)) (Cvol := Cvol) (CEt := CEt)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hx (pow_nonneg hD0 S.d) hxU
  have t3 := lres_term3 hCE' hx hQ0 hQ
  rw [hxZ] at t1 t3
  have hCRU : (((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') * W +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10) * U ≤ CR * U :=
    mul_le_mul_of_nonneg_right hCR (by linarith)
  linarith [t1, t2, t3, hCRU]

/-- `C_R ≤ A₂ x^{p₂ - (2d+1)}` for `x ≥ 1` and `x ≥ C_R / A₂` (`p₂ ≥ 2d + 3`). -/
theorem CR_le_A2_pow_of_large {S : Setting} (ok : S.Ok) {x : ℝ} (hx : 1 ≤ x)
    (hxC : S.CR / S.A2 ≤ x) : S.CR ≤ S.A2 * x ^ (S.p2 - (2 * S.d + 1)) := by
  have hA := ok.A2_pos
  have hp := ok.p2_ge
  have h2 : x ≤ x ^ (S.p2 - (2 * S.d + 1)) := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ _ := pow_le_pow_right₀ hx (by omega)
  have : S.CR ≤ S.A2 * x := by
    rwa [div_le_iff₀ hA, mul_comm] at hxC
  exact this.trans (mul_le_mul_of_nonneg_left h2 hA.le)

/-- The hypothesis `hCR` of `removed_kerBound_logC_of_window`: `C_R λ^{2d+1} ≤ A₂ λ^{p₂}` for
`λ ≥ max {1, C_R/A₂}`. -/
theorem CR_window_of_large {S : Setting} (ok : S.Ok) {x : ℝ} (hx : 1 ≤ x)
    (hxC : S.CR / S.A2 ≤ x) : S.CR * x ^ (2 * S.d + 1) ≤ S.A2 * x ^ S.p2 :=
  CR_pow_le_A2_pow (by linarith) (by have := ok.p2_ge; omega) (CR_le_A2_pow_of_large ok hx hxC)

/-- **(III.8.4) at the scale `k`** with `λ = λ_k = S.lam k ≥ 1`, `crit = crit_k` (landed
`crit_le_critBar`) and the typing constant `C_R = S.CR` at least the explicit constant of
`lres_lhs_le`; and then, for `λ_k ≥ C_R/A₂`, the window arithmetic `C_R λ^{2d+1} ≤ A₂ λ^{p₂}`. -/
theorem lres_at_scale (S : Setting) (ok : S.Ok) (k : ℕ) (hx : 1 ≤ S.lam k) (N : ℕ)
    {Cvol CEt CE' Cnat D0 : ℝ} (hCE' : 0 ≤ CE') (hD0 : 0 ≤ D0)
    (hCR : ((N : ℝ) / 2 * Real.log 2 + N * S.p0 + |Cvol| + 2 * CE') *
        ((S.M : ℝ) ^ S.d * (2 * S.c0 * S.Rb + 2 * S.c0 + 10) ^ S.d) +
        D0 ^ S.d * (N * S.p0 + |Cvol| + |CEt|) + Cnat + 10 ≤ S.CR) :
    (((N : ℝ) / 2 * Real.log 2 + N * S.p0 * Real.log (S.lam k) + Cvol) *
        ((S.M : ℝ) * S.crit k) ^ S.d +
      D0 ^ S.d * (N * S.p0 * Real.log (S.lam k) + Cvol + CEt) +
      (CE' * S.lam k + CE') * ((S.M : ℝ) * S.crit k) ^ S.d +
      Cnat * S.lam k ^ (2 * S.d + 1) + 10 ≤ S.CR * S.lam k ^ (2 * S.d + 1)) ∧
    (S.CR / S.A2 ≤ S.lam k → S.CR * S.lam k ^ (2 * S.d + 1) ≤ S.A2 * S.lam k ^ S.p2) :=
  ⟨lres_lhs_le S ok hx (D7Reserve.crit_le_critBar ok k) N hCE' hD0 hCR,
    fun h => CR_window_of_large ok hx h⟩

end Balaban.LargeField
