/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseFRWhiteRow
public import Balaban.LargeField.Base.BaseFRWhiteLogDetSeries

/-!
# The logarithm of the determinant of the whitening of the first step

`log |det W| = ½ Re ∑_{n ≥ 1} (-1)^{n+1} tr(D_R^n)/n - ½ log |det A_e|` where `D_R` is the defect
of the finite-range whitening and `A_e = baseOp` the first-step Hessian operator
(`log_abs_det_whiteW` and `det_one_add_eq_exp_tsum_trace`); the series converges because the row
sums of `D_R` are at most `N (2 (2R+1)(dL+1) + 1)^d · 4 (1-q)^{-1/2} q^{R+1}/(1-q) < 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix Balaban.Green Balaban.LargeField.Base Balaban.Multiscale
open scoped Matrix.Norms.L2Operator

namespace Balaban.LargeField.FRWhite

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ)
variable {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ} {η : ℝ} {s : FineBond d L N₀ → ℂ}
  (e : G.Ω 1 → Fin N → ℝ)

/-- **`log |det W| = ½ Re ∑ (-1)^n tr(D_R^{n+1})/(n+1) - ½ log |det A_e|`** for the finite-range
whitening of the first step, when the row sums of the defect are below `1`. -/
theorem log_abs_det_baseWhiteW [Nonempty (G.Ω 1)] [NeZero N] (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights 1 a) (hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2)) (hη0 : 0 ≤ η)
    (hη : η ≤ baseCoercivity L / (8 * d)) (hs : s ∈ baseParamNbhd G η)
    (he : ∀ z, ∑ i, e z i ^ 2 = 1) (R : ℕ)
    (hrow : (N : ℝ) * (2 * ((2 * R + 1) * (d * L + 1)) + 1) ^ d *
      (4 * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹ *
        (Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2) ^ (R + 1) /
          (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2)))) < 1) :
    Real.log ‖(baseWhiteW G a ν α s e R).det‖ =
      (1 / 2) * (∑' n : ℕ, (-1) ^ n *
        ((whiteDefect (baseWhiteK G a ν α s e) R) ^ (n + 1)).trace / ((n : ℂ) + 1)).re -
      (1 / 2) * Real.log ‖(baseOp N (fun z i => (e z i : ℂ))
        (baseHamiltonian G a ν α s)).det‖ := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hγ : 0 < baseCoercivity L / 2 := half_pos (baseCoercivity_pos hL)
  have hJ := baseJ_pos (d := d) hν
  obtain ⟨-, -, hrangeD, hDn⟩ := baseWhite G e hν ha hα hη0 hη hs he R
  set b : ℝ := 4 * Real.sqrt (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))⁻¹ *
    (Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2) ^ (R + 1) /
      (1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2))) with hb
  obtain ⟨hK, hq⟩ := baseWhiteK_norm_le G e hν ha hα hη0 hη hs he
  have hq0 := Real.sqrt_nonneg (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2)
  have hb0 : 0 ≤ b := by
    have h1 : 0 < 1 - Real.sqrt (1 - ((baseCoercivity L / 2) / baseJ d ν) ^ 2) := by linarith
    rw [hb]; positivity
  have hDn' : ‖whiteDefect (baseWhiteK G a ν α s e) R‖ ≤ b := hDn
  set ρD : ℕ := (2 * R + 1) * (d * L + 1) with hρD
  set Brow : ℝ := (N : ℝ) * (2 * ρD + 1) ^ d * b with hBrow
  have hrowD : ∀ x, ∑ y, ‖whiteDefect (baseWhiteK G a ν α s e) R x y‖ ≤ Brow := by
    intro x
    refine (sum_norm_row_le hrangeD x).trans ?_
    have hcard := card_indexDist_le G x ρD
    have hρ : ((2 * R + 1 : ℝ)) * baseRange d L = ((ρD : ℕ) : ℝ) := by
      unfold baseRange; rw [hρD]; push_cast; ring
    rw [hρ]
    exact mul_le_mul hcard hDn' (norm_nonneg _) (by positivity)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hbB : b ≤ Brow := by
    have h1 : (1 : ℝ) ≤ (2 * ρD + 1) ^ d := one_le_pow₀ (by linarith [(Nat.cast_nonneg ρD : (0:ℝ) ≤ ρD)])
    have : 1 ≤ (N : ℝ) * (2 * ρD + 1) ^ d := by nlinarith
    rw [hBrow]; nlinarith
  have hBlt : Brow < 1 := by
    rw [hBrow, hρD]; push_cast; exact hrow
  have hD1 : ‖whiteDefect (baseWhiteK G a ν α s e) R‖ < 1 := lt_of_le_of_lt (hDn'.trans hbB) hBlt
  have hA : IsUnit (baseOp N (fun z i => (e z i : ℂ)) (baseHamiltonian G a ν α s)) :=
    isUnit_of_isCoercive hγ (baseOp_isCoercive_of_close G hν ha hα hη0 hη hs e he)
  have hlog := log_abs_det_whiteW (R := R) hγ hJ hA hD1
  obtain ⟨-, hdet⟩ := Balaban.LargeField.Base.det_one_add_eq_exp_tsum_trace
    (whiteDefect (baseWhiteK G a ν α s e) R) hBlt hrowD
  have hlogD : Real.log ‖(1 + whiteDefect (baseWhiteK G a ν α s e) R).det‖ =
      (∑' n : ℕ, (-1) ^ n * ((whiteDefect (baseWhiteK G a ν α s e) R) ^ (n + 1)).trace /
        ((n : ℂ) + 1)).re := by
    rw [hdet, Complex.norm_exp, Real.log_exp]
  rw [← hlogD]
  exact hlog

end Balaban.LargeField.FRWhite
