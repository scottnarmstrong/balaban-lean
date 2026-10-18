/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The RG increments over one conversion step (P7CONV (35)–(36))

Scalar consequences of the flow relations `g_{n-1} = g_n (1 + ξ₂)` and
`δ_{n-1} (1 + ξ₂) = δ_n (1 + ξ₁)` with `|ξ_c| ≤ ρ ≤ 1/2`: the changes of the coupling
`β g` and of the mass `ν δ` are at most `2 ρ` and `12 ρ` times the scale-`(n-1)` values, and the
coefficient `a` with `β₁ a₁ = β₀ a₀` changes by at most `2 ρ |a₀|`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

/-- The coupling and mass increments of one RG step. -/
theorem step_flow_bounds {β ν g0 g1 δ0 δ1 ξ1 ξ2 ρ : ℝ} (hβ : 0 < β) (hν : 0 < ν)
    (hg0 : 0 < g0) (hδ0 : 0 < δ0) (hg : g1 = g0 * (1 + ξ2))
    (hδ : δ1 * (1 + ξ2) = δ0 * (1 + ξ1)) (h1 : |ξ1| ≤ ρ) (h2 : |ξ2| ≤ ρ) (hρ : ρ ≤ 1 / 2) :
    0 < δ1 ∧ |β * g1 - β * g0| ≤ 2 * ρ * (β * g1) ∧
      |β * g1 * (ν * δ1) - β * g0 * (ν * δ0)| ≤ 2 * ρ * (β * g1 * |ν * δ1|) ∧
      ν * δ1 ≤ 3 * (ν * δ0) ∧ ν * δ0 ≤ 3 * (ν * δ1) ∧ |ν * δ1 - ν * δ0| ≤ 12 * ρ * (ν * δ1) := by
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have hu : 1 / 2 ≤ 1 + ξ2 := by linarith [a2.1]
  have hu' : 1 + ξ2 ≤ 3 / 2 := by linarith [a2.2]
  have hw : 1 / 2 ≤ 1 + ξ1 := by linarith [a1.1]
  have hw' : 1 + ξ1 ≤ 3 / 2 := by linarith [a1.2]
  have hu0 : 0 < 1 + ξ2 := by linarith
  have hw0 : 0 < 1 + ξ1 := by linarith
  have hδ1 : 0 < δ1 := by
    have : 0 < δ1 * (1 + ξ2) := by rw [hδ]; positivity
    exact (pos_iff_pos_of_mul_pos this).2 hu0
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans h1
  have habs1 : |ξ1| ≤ ρ := h1
  have habs2 : |ξ2| ≤ ρ := h2
  refine ⟨hδ1, ?_, ?_, ?_, ?_, ?_⟩
  · have e : β * g1 - β * g0 = β * g0 * ξ2 := by rw [hg]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < β * g0)]
    have : β * g0 * |ξ2| ≤ β * g0 * ρ := mul_le_mul_of_nonneg_left habs2 (by positivity)
    have h3 : β * g0 * ρ ≤ 2 * ρ * (β * g1) := by
      rw [hg]
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hβ.le hg0.le) hρ0)
        (by linarith : (0 : ℝ) ≤ 1 + ξ2 - 1 / 2)]
    linarith
  · have e : β * g1 * (ν * δ1) - β * g0 * (ν * δ0) = β * ν * g0 * δ0 * ξ1 := by
      have : g1 * δ1 = g0 * (δ0 * (1 + ξ1)) := by rw [hg, ← hδ]; ring
      calc _ = β * ν * (g1 * δ1) - β * ν * g0 * δ0 := by ring
        _ = _ := by rw [this]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < β * ν * g0 * δ0)]
    have h3 : β * ν * g0 * δ0 * |ξ1| ≤ β * ν * g0 * δ0 * ρ :=
      mul_le_mul_of_nonneg_left habs1 (by positivity)
    have h4 : β * g1 * |ν * δ1| = β * ν * g0 * δ0 * (1 + ξ1) * 1 := by
      have : g1 * δ1 = g0 * (δ0 * (1 + ξ1)) := by rw [hg, ← hδ]; ring
      rw [abs_of_pos (by positivity : 0 < ν * δ1)]
      calc β * g1 * (ν * δ1) = β * ν * (g1 * δ1) := by ring
        _ = _ := by rw [this]; ring
    rw [h4]
    have h5 : 0 ≤ β * ν * g0 * δ0 * ρ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hβ.le hν.le) hg0.le) hδ0.le) hρ0
    nlinarith [mul_nonneg h5 (by linarith : (0 : ℝ) ≤ 1 + ξ1 - 1 / 2)]
  · have : δ1 ≤ 3 * δ0 := by nlinarith
    nlinarith
  · have : δ0 ≤ 3 * δ1 := by nlinarith
    nlinarith
  · have e : δ1 - δ0 = δ0 * ξ1 - δ1 * ξ2 := by linear_combination hδ
    have hb : |δ1 - δ0| ≤ 12 * ρ * δ1 := by
      have b1 : |δ1 * ξ2| ≤ δ1 * ρ := by
        rw [abs_mul, abs_of_pos hδ1]; exact mul_le_mul_of_nonneg_left habs2 hδ1.le
      have hd03 : δ0 ≤ 3 * δ1 := by nlinarith
      have b2 : |δ0 * ξ1| ≤ 3 * δ1 * ρ := by
        rw [abs_mul, abs_of_pos hδ0]
        exact mul_le_mul hd03 habs1 (abs_nonneg _) (by positivity)
      rw [e]
      calc |δ0 * ξ1 - δ1 * ξ2| ≤ |δ0 * ξ1| + |δ1 * ξ2| := abs_sub _ _
        _ ≤ 12 * ρ * δ1 := by nlinarith
    have : ν * δ1 - ν * δ0 = ν * (δ1 - δ0) := by ring
    rw [this, abs_mul, abs_of_pos hν]
    nlinarith

/-- A coefficient with `β₁ a₁ = β₀ a₀` and `|β₁ - β₀| ≤ 2 ρ β₁` changes by at most `2 ρ |a₀|`. -/
theorem coeff_step_change {a₀ a₁ β₀ β₁ ρ : ℝ} (hβ₁ : 0 < β₁) (h : β₁ * a₁ = β₀ * a₀)
    (hb : |β₁ - β₀| ≤ 2 * ρ * β₁) : |a₁ - a₀| ≤ 2 * ρ * |a₀| := by
  have e : β₁ * (a₁ - a₀) = -((β₁ - β₀) * a₀) := by linear_combination h
  have h2 : β₁ * |a₁ - a₀| ≤ β₁ * (2 * ρ * |a₀|) := by
    calc β₁ * |a₁ - a₀| = |β₁ * (a₁ - a₀)| := by rw [abs_mul, abs_of_pos hβ₁]
      _ = |(β₁ - β₀) * a₀| := by rw [e, abs_neg]
      _ = |β₁ - β₀| * |a₀| := abs_mul _ _
      _ ≤ (2 * ρ * β₁) * |a₀| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = β₁ * (2 * ρ * |a₀|) := by ring
  exact le_of_mul_le_mul_left h2 hβ₁

/-- The size of a coefficient at the scale `n` from the coefficient `aw` at the scale `j + 1`:
`β g_n a₀ = β g_j aw` gives `|a₀| ≤ e^{2η} |aw|`. -/
theorem coeff_size_le {a₀ aw β gj gn η : ℝ} (hβ : 0 < β) (hgj : gj ≤ Real.exp η)
    (hgn : Real.exp (-η) ≤ gn) (hgj0 : 0 < gj) (h : β * gn * a₀ = β * gj * aw) :
    |a₀| ≤ Real.exp (2 * η) * |aw| := by
  have hgn0 : 0 < gn := lt_of_lt_of_le (Real.exp_pos _) hgn
  have e : gn * |a₀| = gj * |aw| := by
    have := congrArg abs h
    simp only [abs_mul, abs_of_pos hβ, abs_of_pos hgn0, abs_of_pos hgj0] at this
    exact mul_left_cancel₀ hβ.ne' (by linarith [this])
  have h1 : Real.exp (-η) * |a₀| ≤ Real.exp η * |aw| := by
    calc Real.exp (-η) * |a₀| ≤ gn * |a₀| := mul_le_mul_of_nonneg_right hgn (abs_nonneg _)
      _ = gj * |aw| := e
      _ ≤ Real.exp η * |aw| := mul_le_mul_of_nonneg_right hgj (abs_nonneg _)
  have e2 : Real.exp η * Real.exp (-η) = 1 := by rw [← Real.exp_add]; simp
  have e3 : Real.exp (2 * η) = Real.exp η * Real.exp η := by rw [← Real.exp_add]; ring_nf
  calc |a₀| = Real.exp η * (Real.exp (-η) * |a₀|) := by
        rw [← mul_assoc, e2, one_mul]
    _ ≤ Real.exp η * (Real.exp η * |aw|) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := by rw [e3]; ring

/-- The mass `ν δ_{n-1}` times a squared spacing is at most `cν²` when `ν sp Dδ ≤ cν²`. -/
theorem mass_spacing_le {ν δ1 Dδ sp cν : ℝ} (hν : 0 < ν) (hδ : δ1 ≤ Dδ) (hsp : 0 ≤ sp)
    (h : ν * sp * Dδ ≤ cν ^ 2) : ν * δ1 * sp ≤ cν ^ 2 := by
  have h3 := mul_le_mul_of_nonneg_left hδ (mul_nonneg hν.le hsp)
  calc ν * δ1 * sp = ν * sp * δ1 := by ring
    _ ≤ ν * sp * Dδ := h3
    _ ≤ cν ^ 2 := h

/-- The change of a coefficient over one step, in terms of the size of the initial coefficient. -/
theorem coeff_step_le {a₀ a₁ aw β₀ β₁ ρ β gj gn η Ka : ℝ} (hβ : 0 < β) (hβ₁ : 0 < β₁)
    (hρ : 0 ≤ ρ) (hcoef : β₁ * a₁ = β₀ * a₀) (hb : |β₁ - β₀| ≤ 2 * ρ * β₁)
    (hgj : gj ≤ Real.exp η) (hgn : Real.exp (-η) ≤ gn) (hgj0 : 0 < gj)
    (h0 : β * gn * a₀ = β * gj * aw) (hKa : |aw| ≤ Ka) :
    |a₁ - a₀| ≤ 2 * ρ * (Real.exp (2 * η) * Ka) := by
  have h1 := coeff_step_change hβ₁ hcoef hb
  have h2 := coeff_size_le hβ hgj hgn hgj0 h0
  have h3 : Real.exp (2 * η) * |aw| ≤ Real.exp (2 * η) * Ka :=
    mul_le_mul_of_nonneg_left hKa (Real.exp_pos _).le
  calc |a₁ - a₀| ≤ 2 * ρ * |a₀| := h1
    _ ≤ 2 * ρ * (Real.exp (2 * η) * Ka) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)

/-- The squared mass change over one step against the spacing. -/
theorem mass_step_sq_le {ν₀ ν₁ ρ cν sp : ℝ} (hν₁ : 0 < ν₁) (hsp : 0 ≤ sp)
    (h1 : |ν₁ - ν₀| ≤ 12 * ρ * ν₁) (h3 : ν₁ * sp ≤ cν ^ 2) :
    sp * (ν₁ - ν₀) ^ 2 ≤ (12 * ρ * cν) ^ 2 * ν₁ := by
  have h2 : (ν₁ - ν₀) ^ 2 ≤ (12 * ρ * ν₁) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc sp * (ν₁ - ν₀) ^ 2 ≤ sp * (12 * ρ * ν₁) ^ 2 := mul_le_mul_of_nonneg_left h2 hsp
    _ = (144 * ρ ^ 2 * ν₁) * (ν₁ * sp) := by ring
    _ ≤ (144 * ρ ^ 2 * ν₁) * cν ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end Balaban.LargeField.ActionConv
