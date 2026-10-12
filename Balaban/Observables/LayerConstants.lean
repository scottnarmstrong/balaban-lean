/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lemma 1.1: admissible exponents of the observable layer (OBSERVABLES.md §1.3)

The exponents `ρ₀, ρ₁, ρ₂` of the observable layer and the constraints (E1)-(E7) collected from the
proofs of §3 (OBSERVABLES v2, after review items O-04, O-05, O-08).  (E8) (`β₀` large) is a choice
of `β₀` and not a constraint on the exponents; it is not part of `ExponentConstraints`.

* `ExponentConstraints d γ α₁ ρ₀ ρ₁ ρ₂`: `ρ₂ > 0`, `0 < ρ₀ ≤ d - 2`, `0 < ρ₁ < 1` (the ranges of the
  Lean `C1Star`), and (E1) `4ρ₂ ≤ ρ₁`, (E2) `ρ₀ ≤ (d-2)/2 - 3(d-2)ρ₂`, (E3) `ρ₀ ≤ 1 - 2(d-2)ρ₂`,
  (E4) `2(d-2)ρ₂ < γ`, (E5) `ρ₀ ≤ γ`, (E6) `ρ₀ ≤ d - 2`, (E7) `γ - α₁ ≤ ρ₀`;
* `obsRho2`: the explicit `ρ₂ = ½ min{((d-2)/2 - γ)/(3(d-2)), γ/(2(d-2)), (1-γ)/(2(d-2))}`;
* `exponentConstraints_explicit` (**Lemma 1.1**): for `d ≥ 3`, `γ ∈ (0, min{(d-2)/2, 1/2})`,
  `α₁ ∈ (0, γ)`, the choice `ρ₀ = γ`, `ρ₁ = 4ρ₂`, `ρ₂ = obsRho2 d γ` satisfies all of them.
-/

@[expose] public section

namespace Balaban.Observables

/-- **The exponent constraints (E1)-(E7)** of OBSERVABLES §1.3 (with `D = d - 2`). -/
structure ExponentConstraints (d : ℕ) (γ α₁ ρ₀ ρ₁ ρ₂ : ℝ) : Prop where
  ρ₂_pos : 0 < ρ₂
  ρ₀_pos : 0 < ρ₀
  ρ₁_pos : 0 < ρ₁
  ρ₁_lt_one : ρ₁ < 1
  E1 : 4 * ρ₂ ≤ ρ₁
  E2 : ρ₀ ≤ ((d : ℝ) - 2) / 2 - 3 * ((d : ℝ) - 2) * ρ₂
  E3 : ρ₀ ≤ 1 - 2 * ((d : ℝ) - 2) * ρ₂
  E4 : 2 * ((d : ℝ) - 2) * ρ₂ < γ
  E5 : ρ₀ ≤ γ
  E6 : ρ₀ ≤ (d : ℝ) - 2
  E7 : γ - α₁ ≤ ρ₀

/-- The explicit `ρ₂ := ½ min{((d-2)/2 - γ)/(3(d-2)), γ/(2(d-2)), (1-γ)/(2(d-2))}`. -/
noncomputable def obsRho2 (d : ℕ) (γ : ℝ) : ℝ :=
  1 / 2 * min (min ((((d : ℝ) - 2) / 2 - γ) / (3 * ((d : ℝ) - 2))) (γ / (2 * ((d : ℝ) - 2))))
    ((1 - γ) / (2 * ((d : ℝ) - 2)))

/-- **Lemma 1.1 (admissible exponents).**  For `d ≥ 3`, `γ ∈ (0, min{(d-2)/2, 1/2})` and
`α₁ ∈ (0, γ)`, the exponents `ρ₀ = γ`, `ρ₁ = 4ρ₂`, `ρ₂ = obsRho2 d γ` satisfy (E1)-(E7), with
`ρ₂ > 0`, `0 < ρ₀ ≤ d - 2`, `0 < ρ₁ < 1`. -/
theorem exponentConstraints_explicit {d : ℕ} (hd : 3 ≤ d) {γ α₁ : ℝ} (hγ : 0 < γ)
    (hγ' : γ < min (((d : ℝ) - 2) / 2) (1 / 2)) (hα₁ : 0 < α₁) (hα₁γ : α₁ < γ) :
    ExponentConstraints d γ α₁ γ (4 * obsRho2 d γ) (obsRho2 d γ) := by
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hD0 : 0 < (d : ℝ) - 2 := by linarith
  have hγ1 : γ < (d - 2 : ℝ) / 2 := lt_of_lt_of_le hγ' (min_le_left _ _)
  have hγ2 : γ < 1 / 2 := lt_of_lt_of_le hγ' (min_le_right _ _)
  set D : ℝ := (d : ℝ) - 2 with hDdef
  set a : ℝ := (D / 2 - γ) / (3 * D) with ha
  set b : ℝ := γ / (2 * D) with hb
  set c : ℝ := (1 - γ) / (2 * D) with hc
  have ha0 : 0 < a := div_pos (by linarith) (by positivity)
  have hb0 : 0 < b := div_pos hγ (by positivity)
  have hc0 : 0 < c := div_pos (by linarith) (by positivity)
  set ρ₂ : ℝ := obsRho2 d γ with hρ₂
  have hρ₂def : ρ₂ = 1 / 2 * min (min a b) c := rfl
  have hm0 : 0 < min (min a b) c := lt_min (lt_min ha0 hb0) hc0
  have hρ₂0 : 0 < ρ₂ := by rw [hρ₂def]; positivity
  have hρa : ρ₂ ≤ a / 2 := by
    rw [hρ₂def]
    have : min (min a b) c ≤ a := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hρb : ρ₂ ≤ b / 2 := by
    rw [hρ₂def]
    have : min (min a b) c ≤ b := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hρc : ρ₂ ≤ c / 2 := by
    rw [hρ₂def]
    have : min (min a b) c ≤ c := min_le_right _ _
    linarith
  have e2 : 3 * D * ρ₂ ≤ (D / 2 - γ) / 2 := by
    have : 3 * D * ρ₂ ≤ 3 * D * (a / 2) := mul_le_mul_of_nonneg_left hρa (by positivity)
    have h2 : 3 * D * (a / 2) = (D / 2 - γ) / 2 := by rw [ha]; field_simp
    linarith
  have e3 : 2 * D * ρ₂ ≤ (1 - γ) / 2 := by
    have : 2 * D * ρ₂ ≤ 2 * D * (c / 2) := mul_le_mul_of_nonneg_left hρc (by positivity)
    have h2 : 2 * D * (c / 2) = (1 - γ) / 2 := by rw [hc]; field_simp
    linarith
  have e4 : 2 * D * ρ₂ ≤ γ / 2 := by
    have : 2 * D * ρ₂ ≤ 2 * D * (b / 2) := mul_le_mul_of_nonneg_left hρb (by positivity)
    have h2 : 2 * D * (b / 2) = γ / 2 := by rw [hb]; field_simp
    linarith
  have e1 : 4 * ρ₂ ≤ γ := by
    have : 4 * ρ₂ ≤ 4 * (b / 2) := by linarith
    have h2 : 4 * (b / 2) = γ / D := by rw [hb]; field_simp; ring
    have h3 : γ / D ≤ γ := by
      rw [div_le_iff₀ hD0]; nlinarith
    linarith
  refine ⟨hρ₂0, hγ, by positivity, by linarith, le_rfl, ?_, ?_, ?_, le_rfl, ?_, by linarith⟩
  · linarith
  · linarith
  · linarith
  · linarith
