/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The sum over distance levels with polynomially many sites (blocker 5)

If the number of sites `|W n|` at distance level `n` is at most `C_W (n+1)^r`, then
`∑_{n ≤ N} ω_n |W n|`, `ω_0 = 1`, `ω_n = A e^{-γ (n-1)}`, is at most
`C_W (1 + A ∑_{m ≥ 0} e^{-γ m} (m+2)^r)`, a bound independent of `N`.
-/

@[expose] public section

open Finset

namespace Balaban.Green

/-- The series `∑ e^{-γ m} (m+2)^r` converges for `γ > 0`. -/
theorem summable_exp_mul_pow_add_two {γ : ℝ} (hγ : 0 < γ) (r : ℕ) :
    Summable fun m : ℕ => Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r := by
  have h1 := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul r hγ)
  have h2 : Summable fun m : ℕ => 2 ^ r * Real.exp γ *
      (((m + 1 : ℕ) : ℝ) ^ r * Real.exp (-γ * ((m + 1 : ℕ) : ℝ))) := h1.mul_left _
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h2
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hp : ((m : ℝ) + 2) ^ r ≤ (2 : ℝ) ^ r * (((m + 1 : ℕ) : ℝ)) ^ r := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) r
  have he : Real.exp (-(γ * m)) = Real.exp γ * Real.exp (-γ * ((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  calc Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r
      ≤ Real.exp (-(γ * m)) * ((2 : ℝ) ^ r * (((m + 1 : ℕ) : ℝ)) ^ r) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = _ := by rw [he]; ring

/-- **The sum over distance levels with polynomially many sites.** -/
theorem sum_poly_decay_le {X : Type*} {A γ Cw : ℝ} {r : ℕ} (hA : 0 ≤ A) (hγ : 0 < γ)
    (hCw : 0 ≤ Cw) (W : ℕ → Finset X) (hWp : ∀ n, ((W n).card : ℝ) ≤ Cw * ((n : ℝ) + 1) ^ r)
    (Nm : ℕ) :
    ∑ n ∈ Finset.range (Nm + 1),
        (if n = 0 then (1 : ℝ) else A * Real.exp (-(γ * ((n - 1 : ℕ) : ℝ)))) * ((W n).card : ℝ) ≤
      Cw * (1 + A * ∑' m : ℕ, Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r) := by
  have hs := summable_exp_mul_pow_add_two hγ r
  have ht : ∀ m : ℕ, 0 ≤ Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r := fun m => by positivity
  rw [Finset.sum_range_succ']
  have h0 : (if (0 : ℕ) = 0 then (1 : ℝ) else A * Real.exp (-(γ * (((0 : ℕ) - 1 : ℕ) : ℝ)))) *
      ((W 0).card : ℝ) ≤ Cw := by
    simpa using hWp 0
  have h1 : ∑ m ∈ Finset.range Nm,
      (if m + 1 = 0 then (1 : ℝ) else A * Real.exp (-(γ * ((m + 1 - 1 : ℕ) : ℝ)))) *
        ((W (m + 1)).card : ℝ) ≤
      Cw * A * ∑' m : ℕ, Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r := by
    calc _ ≤ ∑ m ∈ Finset.range Nm, Cw * A * (Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r) := by
          refine Finset.sum_le_sum fun m _ => ?_
          simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          have := hWp (m + 1)
          push_cast at this ⊢
          calc A * Real.exp (-(γ * m)) * ((W (m + 1)).card : ℝ)
              ≤ A * Real.exp (-(γ * m)) * (Cw * ((m : ℝ) + 1 + 1) ^ r) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = Cw * A * (Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r) := by ring_nf
      _ = Cw * A * ∑ m ∈ Finset.range Nm, Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r := by
          rw [Finset.mul_sum]
      _ ≤ Cw * (A * ∑' m : ℕ, Real.exp (-(γ * m)) * ((m : ℝ) + 2) ^ r) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hs.sum_le_tsum _ fun m _ => ht m) hA) hCw
      _ = _ := by ring
  linarith

end Balaban.Green
