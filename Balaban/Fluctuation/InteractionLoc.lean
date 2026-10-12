/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionDir
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Localized expansions of the interaction, and their calculus (FLUCTUATION §3.3, Prop. 3.3)

`LocInt` is the conclusion of Proposition 3.3 for one function: a value `val(x₀, w, σ, Θ)` (the
interaction built from the fluctuation direction `x₀` of the ray and the direction `w`, the
parameter `σ`, and the data `Θ`) is a finite sum `∑_Y T_Y` of terms that are analytic in
`(Θ, σ)`, bounded by `|σ| b_Y`, local (they depend on `Θ` through `AgΘ` and on `(x₀, w)` through
`AgF`), and vanish at `σ = 0`.  The terms of the old effective action, of the source, and of the
interaction potential are added with `LocInt.add`, `LocInt.sum`, scaled with `LocInt.smul`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Set Metric

section LocInt

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*}
variable {ι : Type*}

/-- **A localized expansion** `val = ∑_{Y ∈ 𝒴} T_Y` with the properties of Proposition 3.3. -/
structure LocInt (S : Set Λ) (XW : Set (F × F)) (Rσ : ℝ) (𝒴 : Finset ι)
    (T : ι → F → F → ℂ → Λ → ℂ) (val : F → F → ℂ → Λ → ℂ) (b : ι → ℝ)
    (AgΘ : ι → Λ → Λ → Prop) (AgF : ι → F → F → Prop) : Prop where
  sum : ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S,
    val xw.1 xw.2 σ Θ = ∑ Y ∈ 𝒴, T Y xw.1 xw.2 σ Θ
  analytic : ∀ Y, ∀ xw ∈ XW,
    AnalyticOnNhd ℂ (fun p : Λ × ℂ => T Y xw.1 xw.2 p.2 p.1) (S ×ˢ ball (0 : ℂ) Rσ)
  bound : ∀ Y, ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S, ‖T Y xw.1 xw.2 σ Θ‖ ≤ ‖σ‖ * b Y
  loc : ∀ Y, ∀ xw ∈ XW, ∀ xw' ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ Θ ∈ S, ∀ Θ' ∈ S,
    AgΘ Y Θ Θ' → AgF Y xw.1 xw'.1 → AgF Y xw.2 xw'.2 →
    T Y xw.1 xw.2 σ Θ = T Y xw'.1 xw'.2 σ Θ'
  zero : ∀ Y, ∀ xw ∈ XW, ∀ Θ ∈ S, T Y xw.1 xw.2 0 Θ = 0

variable {S : Set Λ} {XW : Set (F × F)} {Rσ : ℝ} {AgΘ : ι → Λ → Λ → Prop}
  {AgF : ι → F → F → Prop}

/-- Weakening the bound. -/
theorem LocInt.mono {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b b' : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) (hb : ∀ Y, b Y ≤ b' Y) :
    LocInt S XW Rσ 𝒴 T val b' AgΘ AgF :=
  { h with bound := fun Y xw hxw σ hσ Θ hΘ =>
      (h.bound Y xw hxw σ hσ Θ hΘ).trans (mul_le_mul_of_nonneg_left (hb Y) (norm_nonneg _)) }

/-- Multiplication by a constant. -/
theorem LocInt.smul {𝒴 : Finset ι} {T : ι → F → F → ℂ → Λ → ℂ} {val : F → F → ℂ → Λ → ℂ}
    {b : ι → ℝ} (h : LocInt S XW Rσ 𝒴 T val b AgΘ AgF) (c : ℂ) :
    LocInt S XW Rσ 𝒴 (fun Y x w σ Θ => c * T Y x w σ Θ) (fun x w σ Θ => c * val x w σ Θ)
      (fun Y => ‖c‖ * b Y) AgΘ AgF where
  sum := fun xw hxw σ hσ Θ hΘ => by
    rw [h.sum xw hxw σ hσ Θ hΘ, Finset.mul_sum]
  analytic := fun Y xw hxw => (analyticOnNhd_const).mul (h.analytic Y xw hxw)
  bound := fun Y xw hxw σ hσ Θ hΘ => by
    rw [norm_mul]
    calc ‖c‖ * ‖T Y xw.1 xw.2 σ Θ‖ ≤ ‖c‖ * (‖σ‖ * b Y) :=
          mul_le_mul_of_nonneg_left (h.bound Y xw hxw σ hσ Θ hΘ) (norm_nonneg _)
      _ = ‖σ‖ * (‖c‖ * b Y) := by ring
  loc := fun Y xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3 => by
    rw [h.loc Y xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3]
  zero := fun Y xw hxw Θ hΘ => by rw [h.zero Y xw hxw Θ hΘ, mul_zero]

/-- Finite sums of localized expansions over a family of terms `τ ∈ 𝒯`, with label sets `𝒴 τ`. -/
theorem LocInt.finsum {κ : Type*} [DecidableEq ι] (𝒯 : Finset κ) {𝒴 : κ → Finset ι}
    {T : κ → ι → F → F → ℂ → Λ → ℂ} {val : κ → F → F → ℂ → Λ → ℂ} {b : κ → ι → ℝ}
    (h : ∀ τ ∈ 𝒯, LocInt S XW Rσ (𝒴 τ) (T τ) (val τ) (b τ) AgΘ AgF) :
    LocInt S XW Rσ (𝒯.biUnion 𝒴)
      (fun Y x w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x w σ Θ else 0)
      (fun x w σ Θ => ∑ τ ∈ 𝒯, val τ x w σ Θ)
      (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then b τ Y else 0) AgΘ AgF where
  sum := fun xw hxw σ hσ Θ hΘ => by
    classical
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [(h τ hτ).sum xw hxw σ hσ Θ hΘ, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem 𝒴 hτ)]
  analytic := fun Y xw hxw => by
    classical
    intro p hp
    refine Finset.analyticAt_fun_sum _ fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simpa [hY] using (h τ hτ).analytic Y xw hxw p hp
    · simp only [hY, ite_false]; exact analyticAt_const
  bound := fun Y xw hxw σ hσ Θ hΘ => by
    classical
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simpa [hY] using (h τ hτ).bound Y xw hxw σ hσ Θ hΘ
    · simp [hY]
  loc := fun Y xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3 => by
    classical
    refine Finset.sum_congr rfl fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simp only [hY, ite_true]
      exact (h τ hτ).loc Y xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1 h2 h3
    · simp [hY]
  zero := fun Y xw hxw Θ hΘ => by
    classical
    refine Finset.sum_eq_zero fun τ hτ => ?_
    by_cases hY : Y ∈ 𝒴 τ
    · simp only [hY, ite_true]; exact (h τ hτ).zero Y xw hxw Θ hΘ
    · simp [hY]

end LocInt

end Balaban.Fluctuation
