/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The oscillation bound at the margin `(2/γ) log β_k` (W910, blocker 4, input (i))

`removed_E_arith`: the first term `E` of `denominatorRestricted_bounds_of_margin_of_weighted` (with
`ν = 0`), for the margin `R = (2/γ_w) log β_k`, is at most a constant times `D₀^d`: the factor
`β_k e^{-(γ_w/2) R} = 1`, and `K₁ K₆ δ ≤ 1`, `ρ ≤ 1` bound the rest.
-/

@[expose] public section

namespace Balaban.LargeField

theorem removed_E_arith {d N : ℕ} {βk γ R κ1 ρ Kw cF e2 cst card Dd : ℝ} (hβ : 0 < βk) (hγ : 0 < γ)
    (hR : R = 2 / γ * Real.log βk) (hκ0 : 0 ≤ κ1) (hκ1 : κ1 ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hKw : 0 ≤ Kw) (hcF : 0 ≤ cF) (he2 : 0 ≤ e2) (hcst : 0 ≤ cst) (hcard0 : 0 ≤ card)
    (hcard : card ≤ Dd) :
    βk * ((d + 1) * N * (2 * κ1 * (Kw * (cF * ρ) * e2) + (Kw * (cF * ρ) * e2) ^ 2)) *
        Real.exp (-(γ / 2 * R)) * (card * cst) ≤
      (d + 1) * N * (2 * (Kw * cF * e2) + (Kw * cF * e2) ^ 2) * cst * Dd := by
  have hexp : βk * Real.exp (-(γ / 2 * R)) = 1 := by
    have : γ / 2 * R = Real.log βk := by rw [hR]; field_simp
    rw [this, Real.exp_neg, Real.exp_log hβ]; field_simp
  set B := Kw * (cF * ρ) * e2 with hB
  set Bc := Kw * cF * e2 with hBc
  have hB0 : 0 ≤ B := by positivity
  have hBc0 : 0 ≤ Bc := by positivity
  have hBle : B ≤ Bc := by
    rw [hB, hBc]
    have : Kw * (cF * ρ) * e2 = (Kw * cF * e2) * ρ := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) hρ1
  have h1 : 2 * κ1 * B + B ^ 2 ≤ 2 * Bc + Bc ^ 2 := by
    have : 2 * κ1 * B ≤ 2 * Bc := by nlinarith
    nlinarith [pow_le_pow_left₀ hB0 hBle 2]
  have h2 : 0 ≤ 2 * κ1 * B + B ^ 2 := by positivity
  have h3 : 0 ≤ ((d : ℝ) + 1) * N := by positivity
  calc βk * (((d : ℝ) + 1) * N * (2 * κ1 * B + B ^ 2)) * Real.exp (-(γ / 2 * R)) * (card * cst)
      = (βk * Real.exp (-(γ / 2 * R))) * (((d : ℝ) + 1) * N * (2 * κ1 * B + B ^ 2)) * (card * cst) := by
        ring
    _ = (((d : ℝ) + 1) * N * (2 * κ1 * B + B ^ 2)) * (card * cst) := by rw [hexp, one_mul]
    _ ≤ (((d : ℝ) + 1) * N * (2 * Bc + Bc ^ 2)) * (Dd * cst) := by
        gcongr
    _ = _ := by ring

end Balaban.LargeField
