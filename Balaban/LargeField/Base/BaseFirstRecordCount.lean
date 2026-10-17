module

public import Balaban.LargeField.Base.BaseHistory
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Numerical part of the first local record count

The coding map is explicit in the theorem hypothesis. A later record-localization theorem must
construct that map for the physical first-component records.
-/

@[expose] public section

namespace Balaban.LargeField

open Finset

/-- An injective code by six binary fields on a component has at most `2^(6*#X)` values. -/
theorem baseFirstRecord_card_le_of_injectiveCoding
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ] [Fintype ι]
    (X : Finset ι) (R : Finset ρ)
    (code : R → (Fin 6 → X → Bool)) (hcode : Function.Injective code) :
    R.card ≤ 2 ^ (6 * X.card) := by
  classical
  have h := Fintype.card_le_of_injective code hcode
  simpa [Fintype.card_fun, pow_mul, mul_comm] using h

/-- P6's six-bit count is absorbed by the first combinatorial cost when `d ≥ 3`, `L ≥ 2`. -/
theorem baseFirstRecord_weighted_count_of_card_bound
    {ρ : Type*} [DecidableEq ρ] (R : Finset ρ) (d L m : ℕ)
    (hd : 3 ≤ d) (hL : 2 ≤ L) (hcount : R.card ≤ 2 ^ (6 * m)) :
    ∑ _r ∈ R, Real.exp (-(5 / 4 : ℝ) * (L : ℝ) ^ d * m) ≤ 1 := by
  classical
  have hpow : (8 : ℝ) ≤ (L : ℝ) ^ d := by
    calc
      8 = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (L : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hL) _
      _ ≤ (L : ℝ) ^ d :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ L by omega) : (1 : ℝ) ≤ L) hd
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hcost : (6 * m : ℝ) * Real.log 2 ≤ (5 / 4 : ℝ) * (L : ℝ) ^ d * m := by
    have hm : (0 : ℝ) ≤ m := by positivity
    nlinarith
  have hcard : (R.card : ℝ) ≤ Real.exp ((6 * m : ℝ) * Real.log 2) := by
    have hc : (R.card : ℝ) ≤ (2 : ℝ) ^ (6 * m) := by exact_mod_cast hcount
    calc
      (R.card : ℝ) ≤ (2 : ℝ) ^ (6 * m) := hc
      _ = Real.exp ((6 * m : ℝ) * Real.log 2) := by
        calc
          (2 : ℝ) ^ (6 * m) = (Real.exp (Real.log 2)) ^ (6 * m) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = Real.exp (((6 * m : ℕ) : ℝ) * Real.log 2) := by
            rw [← Real.exp_nat_mul]
          _ = Real.exp ((6 * m : ℝ) * Real.log 2) := by norm_cast
  calc
    ∑ _r ∈ R, Real.exp (-(5 / 4 : ℝ) * (L : ℝ) ^ d * m) =
        (R.card : ℝ) * Real.exp (-(5 / 4 : ℝ) * (L : ℝ) ^ d * m) := by simp
    _ ≤ Real.exp ((6 * m : ℝ) * Real.log 2) *
          Real.exp (-(5 / 4 : ℝ) * (L : ℝ) ^ d * m) := by
            exact mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp ((6 * m : ℝ) * Real.log 2 -
          (5 / 4 : ℝ) * (L : ℝ) ^ d * m) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
    _ ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (sub_nonpos.mpr hcost)

/-- The local weighted count follows once the six binary fields are injective on restrictions. -/
theorem baseFirstRecord_weighted_count_of_injectiveCoding
    {ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ] [Fintype ι]
    (X : Finset ι) (R : Finset ρ)
    (code : R → (Fin 6 → X → Bool)) (hcode : Function.Injective code)
    (d L : ℕ) (hd : 3 ≤ d) (hL : 2 ≤ L) :
    ∑ _r ∈ R, Real.exp (-(5 / 4 : ℝ) * (L : ℝ) ^ d * X.card) ≤ 1 :=
  baseFirstRecord_weighted_count_of_card_bound R d L X.card hd hL
    (baseFirstRecord_card_le_of_injectiveCoding X R code hcode)

end Balaban.LargeField
