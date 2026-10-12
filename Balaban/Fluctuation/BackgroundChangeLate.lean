/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 5: the late threshold (Λ28′) (FLUCTUATION.md §4.2)

Pure real analysis.  With `x = λ̂_k`, `R = R_base`, `γ = γ_w`:

* `lambda28_eventually`: if `γ M > 1` then (Λ28′)
  `C_F a⁻¹ α₀² e^x exp(-γ [M(⌊R (x-2)²⌋ - 1) - 2 M₁]) ≤ e^{-R x²/2}` holds for all `x ≥ λ_*`;
* `delta_second_bound`: the passage from the first to the second bound of (4.3), from (Λ28′)-type
  control of the prefactor and `2κ - 1 - κ₀ ≥ 3κ/2`.
-/

@[expose] public section

namespace Balaban.Fluctuation

/-- A negative-leading-coefficient quadratic is eventually negative. -/
theorem quad_eventually_neg {ε b c : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ x : ℝ, lam ≤ x → -ε * x ^ 2 + b * x + c ≤ 0 := by
  refine ⟨max 1 ((|b| + |c| + 1) / ε), le_max_left _ _, fun x hx => ?_⟩
  have h1 : 1 ≤ x := (le_max_left _ _).trans hx
  have h2 : (|b| + |c| + 1) / ε ≤ x := (le_max_right _ _).trans hx
  have h3 : |b| + |c| + 1 ≤ ε * x := by
    rw [div_le_iff₀ hε] at h2; linarith
  have h4 : b * x ≤ |b| * x := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
  have h5 : c ≤ |c| := le_abs_self c
  have h6 : |c| ≤ |c| * x := le_mul_of_one_le_right (abs_nonneg c) h1
  nlinarith [abs_nonneg b, abs_nonneg c]

/-- **(Λ28′).**  For `γ M > 1`, `R > 0`, `M ≥ 0`, `γ ≥ 0` (and any real `P = C_F a⁻¹ α₀²`, `M₁`), there is `λ_*` with
`C_F a⁻¹ α₀² e^x exp(-γ [M(⌊R (x-2)²⌋ - 1) - 2 M₁]) ≤ e^{-R x²/2}` for `x ≥ λ_*`. -/
theorem lambda28_eventually {P γ R M M₁ : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hγ : 0 ≤ γ) (hγM : 1 < γ * M) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ x : ℝ, lam ≤ x →
      P * Real.exp x * Real.exp (-γ * (M * (⌊R * (x - 2) ^ 2⌋ - 1) - 2 * M₁)) ≤
        Real.exp (-(R * x ^ 2) / 2) := by
  set A := γ * M * R with hA
  have hε : 0 < A - R / 2 := by nlinarith
  obtain ⟨lam, hlam, hq⟩ := quad_eventually_neg (ε := A - R / 2) (b := 1 + 4 * A)
    (c := P + 2 * γ * M - 4 * A + 2 * γ * M₁) hε
  refine ⟨lam, hlam, fun x hx => ?_⟩
  have hfl : R * (x - 2) ^ 2 - 1 ≤ (⌊R * (x - 2) ^ 2⌋ : ℝ) := by
    have := Int.lt_floor_add_one (R * (x - 2) ^ 2); linarith
  have hexp : -γ * (M * (⌊R * (x - 2) ^ 2⌋ - 1) - 2 * M₁) ≤
      -A * (x - 2) ^ 2 + 2 * γ * M + 2 * γ * M₁ := by
    have : M * (R * (x - 2) ^ 2 - 2) ≤ M * (⌊R * (x - 2) ^ 2⌋ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hM
    have h2 : γ * (M * (R * (x - 2) ^ 2 - 2)) ≤ γ * (M * (⌊R * (x - 2) ^ 2⌋ - 1)) :=
      mul_le_mul_of_nonneg_left this hγ
    rw [hA]; nlinarith
  have hPe : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  calc P * Real.exp x * Real.exp (-γ * (M * (⌊R * (x - 2) ^ 2⌋ - 1) - 2 * M₁))
      ≤ Real.exp P * Real.exp x * Real.exp (-A * (x - 2) ^ 2 + 2 * γ * M + 2 * γ * M₁) := by
        gcongr
    _ = Real.exp (P + x + (-A * (x - 2) ^ 2 + 2 * γ * M + 2 * γ * M₁)) := by
        rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(R * x ^ 2) / 2) := by
        refine Real.exp_le_exp.2 ?_
        have := hq x hx
        nlinarith

/-- **(4.3), first bound to second bound.**  Suppose `C_F β r² e^{-γ D} e^{-(2κ-1-κ₀) d}` is the
first bound, with `β ≤ C_L a⁻¹ e^x`, `r ≤ C_H α₀`, `D ≥ D'`, `γ ≥ 0`, `d ≥ 0`, and the prefactor
condition (Λ28′) in the form `C_F C_H² C_L a⁻¹ α₀² e^x e^{-γ D'} ≤ e^{-R̂/2}`.  If
`2κ - 1 - κ₀ ≥ 3κ/2`, the bound is `≤ e^{-R̂/2} e^{-(3/2) κ d}`. -/
theorem delta_second_bound {CF CH CL a α₀ β r γ D D' x κ κ₀ d Rh : ℝ} (hCF : 0 ≤ CF) (ha : 0 ≤ a)
    (hCL : 0 ≤ CL) (hr0 : 0 ≤ r)
    (hβ : β ≤ CL * a⁻¹ * Real.exp x) (hr : r ≤ CH * α₀) (hD : D' ≤ D) (hγ : 0 ≤ γ)
    (hd : 0 ≤ d) (hκ : 3 * κ / 2 ≤ 2 * κ - 1 - κ₀)
    (hΛ : CF * CH ^ 2 * CL * a⁻¹ * α₀ ^ 2 * Real.exp x * Real.exp (-γ * D') ≤
      Real.exp (-Rh / 2)) :
    CF * β * r ^ 2 * Real.exp (-γ * D) * Real.exp (-(2 * κ - 1 - κ₀) * d) ≤
      Real.exp (-Rh / 2) * Real.exp (-(3 / 2) * κ * d) := by
  have h1 : Real.exp (-γ * D) ≤ Real.exp (-γ * D') :=
    Real.exp_le_exp.2 (by nlinarith)
  have h2 : Real.exp (-(2 * κ - 1 - κ₀) * d) ≤ Real.exp (-(3 / 2) * κ * d) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h3 : r ^ 2 ≤ (CH * α₀) ^ 2 := pow_le_pow_left₀ hr0 hr 2
  have hα : 0 ≤ CH * α₀ := le_trans hr0 hr
  have h4 : CF * β * r ^ 2 * Real.exp (-γ * D) ≤
      CF * (CL * a⁻¹ * Real.exp x) * (CH * α₀) ^ 2 * Real.exp (-γ * D') := by
    gcongr
  have ha' : 0 ≤ a⁻¹ := inv_nonneg.2 ha
  calc CF * β * r ^ 2 * Real.exp (-γ * D) * Real.exp (-(2 * κ - 1 - κ₀) * d)
      ≤ (CF * (CL * a⁻¹ * Real.exp x) * (CH * α₀) ^ 2 * Real.exp (-γ * D')) *
          Real.exp (-(3 / 2) * κ * d) := by
        gcongr
    _ = (CF * CH ^ 2 * CL * a⁻¹ * α₀ ^ 2 * Real.exp x * Real.exp (-γ * D')) *
          Real.exp (-(3 / 2) * κ * d) := by ring
    _ ≤ _ := by gcongr

end Balaban.Fluctuation
