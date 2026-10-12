/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.FirstOrderBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The second-order step of OBSERVABLES.md §3.6: the Cauchy chains of the `R₁` rows

A coupling Cauchy factor `4/r₁` and `m` background field Cauchy factors `1/r₀` (P9 (3.28), (3.37))
give `x ≤ (4/r₁)(1/r₀)^m C`.  With (B1), (B3) this is
`K β^{-1/2+(m+1)ρ₂} η^{(d-2)/2-(m+1)(d-2)ρ₂}` (`cauchy_chain_pre`); `m = 0` is the row
`R₁^{i,k+1}` (`i ≤ k`), `m = 1` is `T1`, `m = 2` is the new term of `R₁^{k+1,k+1}` (3.37).
`cauchy_chain_final` closes the row: `≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` for `β ≥ β₀` (E1), (E2).
-/

@[expose] public section

namespace Balaban.Observables

open Real

/-- **The Cauchy chain of an `R₁` row, pre-conversion** (P9 (3.28), (3.37)): the coupling factor
and `m` background field factors give `K β^{-1/2+(m+1)ρ₂} η^{D/2-(m+1)Dρ₂}`. -/
theorem cauchy_chain_pre {D ρ₂ : ℝ} (S : StepScale D ρ₂) (hρ2 : 0 < ρ₂) (hρ2' : ρ₂ ≤ 1) (m : ℕ)
    {c c₁ α εo εn C x : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (hC : 0 ≤ C)
    (hx : x ≤ 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) ^ m * C) :
    x ≤ 4 * C / (c * c₁) ^ (m + 1) * (2 * S.Cp) ^ (m + 1) * √2 *
      S.β ^ (-(1 / 2 : ℝ) + ((m : ℝ) + 1) * ρ₂) * S.η ^ (D / 2 - ((m : ℝ) + 1) * (D * ρ₂)) := by
  have hβp := S.β_pos
  have hβk := S.βk_pos
  have hη0 := S.hη0
  have hp1 : 0 < S.p1 := by linarith [S.hp1]
  have hsq : 0 < √S.βk := Real.sqrt_pos.2 hβk
  have hCp0 : 0 < S.Cp := by linarith [S.hCp]
  have h1 : 4 / couplingRadius c c₁ S.βk S.p1 *
      (1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background) ^ m * C =
      (4 * C / (c * c₁) ^ (m + 1)) * S.p1 ^ (m + 1) * S.βk ^ (-(1 / 2 : ℝ)) := by
    have hr : 1 / fieldRadius c c₁ α εo εn S.p1 RadiusCase.background = S.p1 / (c * c₁) := by
      simp only [fieldRadius]; rw [one_div_div]
    rw [hr]
    unfold couplingRadius
    rw [Real.rpow_neg hβk.le, ← Real.sqrt_eq_rpow, div_pow]
    field_simp
    ring
  have hK : 0 ≤ 4 * C / (c * c₁) ^ (m + 1) := by positivity
  have hp : S.p1 ^ (m + 1) ≤ (2 * S.Cp) ^ (m + 1) * S.β ^ (((m : ℝ) + 1) * ρ₂) *
      S.η ^ (-(((m : ℝ) + 1) * (D * ρ₂))) := by
    have := S.p1_pow_le hρ2.le hρ2' (s := (m : ℝ) + 1) (by positivity)
    simpa [← Real.rpow_natCast, Nat.cast_add] using this
  have hb1 := S.betak_inv_sqrt_le
  rw [h1] at hx
  refine hx.trans ?_
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hp hK) hb1 (Real.rpow_nonneg hβk.le _)
    (by positivity)
  refine hm.trans (le_of_eq ?_)
  have e1 : S.β ^ (-(1 / 2 : ℝ) + ((m : ℝ) + 1) * ρ₂) =
      S.β ^ (((m : ℝ) + 1) * ρ₂) * S.β ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hβp]; congr 1; ring
  have e2 : S.η ^ (D / 2 - ((m : ℝ) + 1) * (D * ρ₂)) =
      S.η ^ (-(((m : ℝ) + 1) * (D * ρ₂))) * S.η ^ (D / 2) := by
    rw [← Real.rpow_add hη0]; congr 1; ring
  rw [e1, e2]; ring

/-- **Closing an `R₁` row** (E1), (E2).  For `m ≤ 2`, `x ≤ K β^{-1/2+(m+1)ρ₂} η^{D/2-(m+1)Dρ₂}`
implies `x ≤ ½ β^{-1/2+ρ₁} ξ_{k+1}^{ρ₀}` once `2 K L^{ρ₀} ≤ β^{ρ₂}`. -/
theorem cauchy_chain_final {d : ℕ} {γ α₁ ρ₀ ρ₁ ρ₂ : ℝ}
    (hE : ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂) (S : StepScale ((d : ℝ) - 2) ρ₂) (m : ℕ)
    (hm : m ≤ 2) {K x : ℝ} (hK : 0 ≤ K)
    (hx : x ≤ K * S.β ^ (-(1 / 2 : ℝ) + ((m : ℝ) + 1) * ρ₂) *
      S.η ^ (((d : ℝ) - 2) / 2 - ((m : ℝ) + 1) * (((d : ℝ) - 2) * ρ₂)))
    (hβ0 : 2 * K * S.L ^ ρ₀ ≤ S.β ^ ρ₂) :
    x ≤ 1 / 2 * S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := S.hD
  have hβp := S.β_pos
  have hη0 := S.hη0
  have hρ2 := hE.ρ₂_pos
  have hm' : (m : ℝ) ≤ 2 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hηe : S.η ^ (((d : ℝ) - 2) / 2 - ((m : ℝ) + 1) * (((d : ℝ) - 2) * ρ₂)) ≤ S.η ^ ρ₀ := by
    refine Real.rpow_le_rpow_of_exponent_ge hη0 S.hη1 ?_
    have := hE.E2
    have h3 : 0 ≤ (2 - (m : ℝ)) * (((d : ℝ) - 2) * ρ₂) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hβe : S.β ^ (-(1 / 2 : ℝ) + ((m : ℝ) + 1) * ρ₂) ≤
      S.β ^ (-ρ₂) * S.β ^ (-(1 / 2 : ℝ) + ρ₁) := by
    rw [← Real.rpow_add hβp]
    refine Real.rpow_le_rpow_of_exponent_le S.hβ ?_
    have := hE.E1; nlinarith
  have hξ := S.ξ_pos
  have hneg : S.β ^ ρ₂ * S.β ^ (-ρ₂) = 1 := by rw [← Real.rpow_add hβp]; simp
  have hβ' : 0 ≤ S.β ^ (-ρ₂) := Real.rpow_nonneg hβp.le _
  calc x ≤ K * S.β ^ (-(1 / 2 : ℝ) + ((m : ℝ) + 1) * ρ₂) *
        S.η ^ (((d : ℝ) - 2) / 2 - ((m : ℝ) + 1) * (((d : ℝ) - 2) * ρ₂)) := hx
    _ ≤ K * (S.β ^ (-ρ₂) * S.β ^ (-(1 / 2 : ℝ) + ρ₁)) * S.η ^ ρ₀ := by
        gcongr
    _ = (K * S.L ^ ρ₀ * S.β ^ (-ρ₂)) * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        rw [S.η_rpow_eq (e := ρ₀)]; ring
    _ ≤ 1 / 2 * (S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀) := by
        have hprod : 0 ≤ S.β ^ (-(1 / 2 : ℝ) + ρ₁) * S.ξ ^ ρ₀ := by positivity
        have hle : K * S.L ^ ρ₀ * S.β ^ (-ρ₂) ≤ 1 / 2 := by
          have h2 := mul_le_mul_of_nonneg_right hβ0 hβ'
          nlinarith [h2, hneg]
        exact mul_le_mul_of_nonneg_right hle hprod
    _ = _ := by ring

end Balaban.Observables
