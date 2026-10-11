/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.ScaleMismatch

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# G-2(vi), analyticity of `α ↦ G_D(α)` (GREEN.md §3, §4.6)

`G_D(α) = H_D(α)⁻¹` is a rational function of the finitely many values of `α`
(`H_D(α) = H_D(0) + diag α`, `inverse = det⁻¹ • adjugate`).  Hence every matrix entry of
`G_D(α)` is analytic in `α` at every `α` with `det H_D(α) ≠ 0`, in particular on the closed
polydisc `|α(x)| ≤ c₁ ℓ(x)⁻² / 2` of G-1(a) (`Balaban.Multiscale.analyticOnNhd_green_apply`), on
which the bounds `green_G2i_green` hold uniformly in `α`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix Finset

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι] [DecidableEq ι]

/-- The determinant of a matrix family with analytic entries is analytic. -/
theorem analyticAt_det {M : E → Matrix ι ι ℂ} {a : E}
    (h : ∀ i j, AnalyticAt ℂ (fun x => M x i j) a) : AnalyticAt ℂ (fun x => (M x).det) a := by
  simp_rw [Matrix.det_apply']
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine AnalyticAt.mul (analyticAt_const) ?_
  exact Finset.analyticAt_fun_prod _ fun i _ => h _ _

/-- Entries of the adjugate of a matrix family with analytic entries are analytic. -/
theorem analyticAt_adjugate {M : E → Matrix ι ι ℂ} {a : E}
    (h : ∀ i j, AnalyticAt ℂ (fun x => M x i j) a) (i j : ι) :
    AnalyticAt ℂ (fun x => (M x).adjugate i j) a := by
  simp_rw [Matrix.adjugate_apply]
  refine analyticAt_det fun r c => ?_
  by_cases hr : r = j
  · subst hr; simp only [Matrix.updateRow_self]
    exact analyticAt_const
  · simp only [Matrix.updateRow_ne hr]
    exact h r c

/-- Entries of the inverse of a matrix family with analytic entries are analytic where the
determinant is nonzero. -/
theorem analyticAt_inv_apply {M : E → Matrix ι ι ℂ} {a : E}
    (h : ∀ i j, AnalyticAt ℂ (fun x => M x i j) a) (hdet : (M a).det ≠ 0) (i j : ι) :
    AnalyticAt ℂ (fun x => (M x)⁻¹ i j) a := by
  have e : ∀ x, (M x)⁻¹ i j = ((M x).det)⁻¹ * (M x).adjugate i j := by
    intro x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp
  simp_rw [e]
  exact ((analyticAt_det h).inv hdet).mul (analyticAt_adjugate h i j)

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem analyticAt_dirichletOperator_apply (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α₀ : G.Ω 1 → ℂ) (i j : G.Ω 1) :
    AnalyticAt ℂ (fun α : G.Ω 1 → ℂ => dirichletOperator G a ν α i j) α₀ := by
  have e : ∀ α : G.Ω 1 → ℂ, dirichletOperator G a ν α i j =
      dirichletOperator G a ν 0 i j + (if i = j then α i else 0) := by
    intro α
    simp only [dirichletOperator, Matrix.add_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  rw [show (fun α : G.Ω 1 → ℂ => dirichletOperator G a ν α i j) = _ from funext e]
  refine analyticAt_const.add ?_
  by_cases hij : i = j
  · simp only [hij, ite_true]
    exact (analyticAt_pi_iff.1 analyticAt_id) j
  · simp only [hij, ite_false]
    exact analyticAt_const

/-- **G-2(vi), analyticity.** Every entry of `G_D(α) = H_D(α)⁻¹` is analytic in `α` at every point
of the closed polydisc `|α(x)| ≤ c₁ ℓ(x)⁻² / 2` of G-1(a). -/
theorem analyticOnNhd_green_apply (G : GeneratingSet d L N₀ k ϱ) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (i j : G.Ω 1) :
    AnalyticOnNhd ℂ (fun α : G.Ω 1 → ℂ => (dirichletOperator G a ν α)⁻¹ i j)
      {α | ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)} := by
  intro α hα
  refine analyticAt_inv_apply (fun i j => analyticAt_dirichletOperator_apply G a ν α i j) ?_ i j
  exact (Matrix.isUnit_iff_isUnit_det _).1 (dirichletOperator_isUnit G hd hν ha α hα) |>.ne_zero

end Balaban.Multiscale
