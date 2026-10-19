/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.KF0CutoffSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `KF0FRGauss`: one-site Gaussian estimates (route FR, (G))

`notes/phase1/KF0-FR.md` (G). For the standard Gaussian `γ` of a finite dimensional real inner
product space of dimension `n`, `r = |ψ|`, `0 ≤ a`, `0 ≤ θ ≤ 1/8`:

* `lintegral_exp_three_eighths`: `∫ e^{3r²/8} dγ = 2^n`;
* `gaussDens_mul_exp_le` (G1): `(2π)^{-n/2} e^{-r²/2} e^{a r + θ r²} ≤ (2π)^{-n/2} e^{a²}`;
* `lintegral_exp_lin_sq_le` (G2): `∫ e^{a r + θ r²} dγ ≤ 2^n e^{2a²}`;
* `lintegral_tail_exp_le` (G3): for `a ≤ p/8`, `∫ 1[r > p] e^{a r + θ r²} dγ ≤ 2^n e^{-p²/8}`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Balaban.LargeField.KF0FR

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The Gaussian moment `∫ e^{3|ψ|²/8} dγ = 2^n`. -/
theorem lintegral_exp_three_eighths :
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (3 / 8 * ‖ψ‖ ^ 2)) ∂(oneSiteGaussian E) =
      ENNReal.ofReal (2 ^ Module.finrank ℝ E) := by
  set c : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hdm : Measurable fun x : E => ENNReal.ofReal (c * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) := by
    fun_prop
  unfold oneSiteGaussian
  rw [lintegral_withDensity_eq_lintegral_mul _ hdm (by fun_prop)]
  have hpt : ∀ x : E, ENNReal.ofReal (c * Real.exp (-(1 / 2) * ‖x‖ ^ 2)) *
      ENNReal.ofReal (Real.exp (3 / 8 * ‖x‖ ^ 2)) =
      ENNReal.ofReal (c * Real.exp (-(1 / 8) * ‖x‖ ^ 2)) := by
    intro x
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp only [Pi.mul_apply]
  simp_rw [hpt]
  rw [lintegral_exp_neg_mul_sq_norm (b := 1 / 8) (by norm_num) hc0]
  congr 1
  have h2π : 0 < 2 * Real.pi := by positivity
  have e1 : Real.pi / (1 / 8) = 4 * (2 * Real.pi) := by ring
  have e2 : -(Module.finrank ℝ E : ℝ) / 2 = -((Module.finrank ℝ E : ℝ) / 2) := by ring
  rw [hc, e1, e2, Real.rpow_neg h2π.le, Real.mul_rpow (by norm_num) h2π.le]
  have h4 : (4 : ℝ) ^ ((Module.finrank ℝ E : ℝ) / 2) = 2 ^ Module.finrank ℝ E := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    rw [show (2 : ℝ) * ((Module.finrank ℝ E : ℝ) / 2) = (Module.finrank ℝ E : ℝ) by ring]
    exact Real.rpow_natCast 2 _
  have hpos : 0 < (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) := Real.rpow_pos_of_pos h2π _
  rw [h4]
  field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **(G1)** The Gaussian density times `e^{a r + θ r²}` is at most `(2π)^{-n/2} e^{a²}`. -/
theorem gaussDens_mul_exp_le {a θ : ℝ} (hθ : θ ≤ 1 / 8) (r : ℝ) :
    (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (-(1 / 2) * r ^ 2) *
        Real.exp (a * r + θ * r ^ 2) ≤
      (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) * Real.exp (a ^ 2) := by
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  nlinarith [sq_nonneg (r - 4 * a / 3), sq_nonneg r]

/-- **(G2)** `∫ e^{a r + θ r²} dγ ≤ 2^n e^{2a²}`. -/
theorem lintegral_exp_lin_sq_le {a θ : ℝ} (hθ : θ ≤ 1 / 8) :
    ∫⁻ ψ, ENNReal.ofReal (Real.exp (a * ‖ψ‖ + θ * ‖ψ‖ ^ 2)) ∂(oneSiteGaussian E) ≤
      ENNReal.ofReal (2 ^ Module.finrank ℝ E * Real.exp (2 * a ^ 2)) := by
  have hpt : ∀ ψ : E, ENNReal.ofReal (Real.exp (a * ‖ψ‖ + θ * ‖ψ‖ ^ 2)) ≤
      ENNReal.ofReal (Real.exp (2 * a ^ 2)) * ENNReal.ofReal (Real.exp (3 / 8 * ‖ψ‖ ^ 2)) := by
    intro ψ
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith [sq_nonneg (‖ψ‖ - 4 * a), sq_nonneg ‖ψ‖]
  calc _ ≤ ∫⁻ ψ, ENNReal.ofReal (Real.exp (2 * a ^ 2)) *
        ENNReal.ofReal (Real.exp (3 / 8 * ‖ψ‖ ^ 2)) ∂(oneSiteGaussian E) := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (2 * a ^ 2)) * ENNReal.ofReal (2 ^ Module.finrank ℝ E) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_three_eighths]
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

/-- **(G3)** For `a ≤ p/8`: `∫ 1[r > p] e^{a r + θ r²} dγ ≤ 2^n e^{-p²/8}`. -/
theorem lintegral_tail_exp_le {a θ p : ℝ} (ha : 0 ≤ a) (hap : a ≤ p / 8) (hθ : θ ≤ 1 / 8) :
    ∫⁻ ψ, Set.indicator {ψ : E | p < ‖ψ‖}
        (fun ψ => ENNReal.ofReal (Real.exp (a * ‖ψ‖ + θ * ‖ψ‖ ^ 2))) ψ ∂(oneSiteGaussian E) ≤
      ENNReal.ofReal (2 ^ Module.finrank ℝ E * Real.exp (-p ^ 2 / 8)) := by
  have hpt : ∀ ψ : E, Set.indicator {ψ : E | p < ‖ψ‖}
      (fun ψ => ENNReal.ofReal (Real.exp (a * ‖ψ‖ + θ * ‖ψ‖ ^ 2))) ψ ≤
      ENNReal.ofReal (Real.exp (-p ^ 2 / 8)) * ENNReal.ofReal (Real.exp (3 / 8 * ‖ψ‖ ^ 2)) := by
    intro ψ
    by_cases hψ : p < ‖ψ‖
    · rw [Set.indicator_of_mem (by exact hψ), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have hp0 : 0 ≤ p := by linarith
      have h1 : a * ‖ψ‖ ≤ ‖ψ‖ ^ 2 / 8 := by nlinarith [norm_nonneg ψ]
      have h2 : θ * ‖ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 / 8 := by nlinarith [sq_nonneg ‖ψ‖]
      have h3 : p ^ 2 ≤ ‖ψ‖ ^ 2 := pow_le_pow_left₀ hp0 hψ.le 2
      nlinarith
    · rw [Set.indicator_of_notMem (by exact hψ)]
      exact zero_le
  calc _ ≤ ∫⁻ ψ, ENNReal.ofReal (Real.exp (-p ^ 2 / 8)) *
        ENNReal.ofReal (Real.exp (3 / 8 * ‖ψ‖ ^ 2)) ∂(oneSiteGaussian E) := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (-p ^ 2 / 8)) * ENNReal.ofReal (2 ^ Module.finrank ℝ E) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_three_eighths]
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

end

end Balaban.LargeField.KF0FR
