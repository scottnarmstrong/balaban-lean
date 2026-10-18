/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomBoundScale
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rate conversion to the coefficient-family convention

The torus anisotropic estimate uses the actual scale ratio `s` and decay `P.κ - 1`.
The class count uses `3^{-(k-j)}` and `κdec - 1`. This theorem records the precise numerical
conversion; the analytic estimate is supplied by the landed non-special torus theorem.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6

variable {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Tm : Terms 3 3 N₁ m₁ K 2 ϱ}
  {j k : ℕ} {y : CTorus 3 3 N₁ m₁ K}
  {X : Set (CTorus 3 3 N₁ m₁ K)} {Ψ : Fld 3 3 N₁ m₁ K 2}
  {hv : Fin 2 → ℂ} {i₀ i₁ : Fin 2}
  {CI γ α₃ κdec s : ℝ}

/-- The count allows one fewer inverse block factor than the composed source ratio. -/
theorem step_ratio_le_class_ratio (hj : j ≤ k) :
    ((3 : ℝ)⁻¹) ^ (k + 1 - j) ≤ ((3 : ℝ)⁻¹) ^ (k - j) := by
  have hexp : k + 1 - j = (k - j) + 1 := by omega
  rw [hexp, pow_succ]
  have hpow : 0 ≤ ((3 : ℝ)⁻¹) ^ (k - j) := by positivity
  have hq : ((3 : ℝ)⁻¹) ≤ 1 := by norm_num
  nlinarith

/-- Convert the landed non-special anisotropic estimate into the rate and decay convention
of `hEbd`/`hEbI`. This preserves the same coefficient `CI`; uniformity of `CI` across labels
must be supplied by the source estimate used to produce the input bound. -/
theorem irrelTorus_bound_class_rate_of_scaled_bound
    (hCI : 0 ≤ CI) (hE₀ : 0 ≤ P.E₀) (hα₃ : α₃ = 1 - 2 * γ - P.α₁)
    (hα₃pos : 0 < α₃) (hs : 0 ≤ s)
    (hscale : s ≤ ((3 : ℝ)⁻¹) ^ (k - j))
    (hκ : κdec ≤ P.κ)
    (hbound : ‖irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
      CI * P.E₀ * s ^ ((3 : ℝ) + (1 - 2 * γ - P.α₁)) *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) :
    ‖irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
      (CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - j)) ^ ((3 : ℝ) + α₃))) *
        Real.exp (-(κdec - 1) * treeLenCovOne P.m₀ j X) := by
  have hpow : s ^ ((3 : ℝ) + (1 - 2 * γ - P.α₁)) ≤
      (((3 : ℝ)⁻¹) ^ (k - j)) ^ ((3 : ℝ) + α₃) := by
    rw [hα₃]
    exact Real.rpow_le_rpow hs hscale (by linarith [hα₃pos])
  have hdist : 0 ≤ sizeJ P.m₀ j X := treeLenCovOne_nonneg P.m₀ j X
  have hrate : Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) ≤
      Real.exp (-(κdec - 1) * treeLenCovOne P.m₀ j X) := by
    apply Real.exp_le_exp.mpr
    change -(P.κ - 1) * sizeJ P.m₀ j X ≤
      -(κdec - 1) * sizeJ P.m₀ j X
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ) hdist]
  have hcoef : 0 ≤ CI * P.E₀ := mul_nonneg hCI hE₀
  calc
    _ ≤ CI * P.E₀ * s ^ ((3 : ℝ) + (1 - 2 * γ - P.α₁)) *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := hbound
    _ ≤ CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - j)) ^ ((3 : ℝ) + α₃)) *
        Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoef)
        (Real.exp_pos _).le
    _ ≤ CI * P.E₀ * (((3 : ℝ)⁻¹ ^ (k - j)) ^ ((3 : ℝ) + α₃)) *
        Real.exp (-(κdec - 1) * treeLenCovOne P.m₀ j X) :=
      mul_le_mul_of_nonneg_left hrate
        (mul_nonneg hcoef (Real.rpow_nonneg (by positivity) _))

end Balaban.SmallField.Def6v2
