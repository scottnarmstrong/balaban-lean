/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventMain
public import Balaban.LargeField.Base.BaseResolventRange
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complex backgrounds and the norm criterion (BASE-KERNEL-3 (1.9))

For a complex background `e` (`e_z · e_z = 1`) the family `A_e(s)` is analytic in `(e, α, s)`
(`baseOp_rectAt_general`), and wherever `‖A_e(s) - A_{e⁰}(r)‖ ≤ c/2` for a real unit reference
`e⁰` and real `r ∈ [0,1]^𝓔` it is `c/2`-coercive, invertible with `‖(A + x)⁻¹‖ ≤ (c/2 + x)⁻¹`
(`isCoercive_of_opNorm_close`, `baseResolvent_analyticAt_of_close`).  This is a norm criterion,
not a claim that the H7 domain satisfies it.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset
open scoped Matrix.Norms.L2Operator

section Criterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Accretivity is stable under operator-norm perturbations. -/
theorem isCoercive_of_opNorm_close {A A0 : Matrix ι ι ℂ} {γ : ℝ} (h0 : IsCoercive A0 γ)
    (hclose : ‖A - A0‖ ≤ γ / 2) : IsCoercive A (γ / 2) := by
  intro u
  have h1 := h0 u
  set Δ := A - A0 with hΔ
  have hA : A = A0 + Δ := by rw [hΔ]; abel
  have h2 : -(‖Δ‖ * sqNorm u) ≤ reQuad Δ u := by
    have hcs := norm_star_dot_le u (Δ *ᵥ u)
    have hsq : Real.sqrt (sqNorm (Δ *ᵥ u)) ≤ ‖Δ‖ * Real.sqrt (sqNorm u) := by
      have := sqNorm_mulVec_le_opNorm Δ u
      calc _ ≤ Real.sqrt (‖Δ‖ ^ 2 * sqNorm u) := Real.sqrt_le_sqrt this
        _ = ‖Δ‖ * Real.sqrt (sqNorm u) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have hu0 := Real.sqrt_nonneg (sqNorm u)
    have hu2 : Real.sqrt (sqNorm u) * Real.sqrt (sqNorm u) = sqNorm u :=
      Real.mul_self_sqrt (sqNorm_nonneg u)
    have h3 : reQuad Δ u ≥ -‖star u ⬝ᵥ (Δ *ᵥ u)‖ := by
      rw [reQuad_eq_dot]
      have := Complex.abs_re_le_norm (star u ⬝ᵥ (Δ *ᵥ u))
      linarith [neg_abs_le ((star u ⬝ᵥ (Δ *ᵥ u)).re)]
    have h4 : ‖star u ⬝ᵥ (Δ *ᵥ u)‖ ≤ ‖Δ‖ * sqNorm u := by
      calc _ ≤ Real.sqrt (sqNorm u) * Real.sqrt (sqNorm (Δ *ᵥ u)) := hcs
        _ ≤ Real.sqrt (sqNorm u) * (‖Δ‖ * Real.sqrt (sqNorm u)) :=
          mul_le_mul_of_nonneg_left hsq hu0
        _ = ‖Δ‖ * (Real.sqrt (sqNorm u) * Real.sqrt (sqNorm u)) := by ring
        _ = ‖Δ‖ * sqNorm u := by rw [hu2]
    linarith
  rw [hA, reQuad_add]
  have hN := sqNorm_nonneg u
  nlinarith [mul_le_mul_of_nonneg_right hclose hN]

/-- Perturbation of a `γ`-coercive matrix by an operator-norm `γ/2`: invertible resolvent bound. -/
theorem opNorm_resolvent_of_close {A A0 : Matrix ι ι ℂ} {γ : ℝ} (hγ : 0 < γ)
    (h0 : IsCoercive A0 γ) (hclose : ‖A - A0‖ ≤ γ / 2) {x : ℝ} (hx : 0 ≤ x) :
    IsUnit (A + (x : ℂ) • (1 : Matrix ι ι ℂ)) ∧ ‖(A + (x : ℂ) • (1 : Matrix ι ι ℂ))⁻¹‖ ≤
      (γ / 2 + x)⁻¹ :=
  opNorm_inv_le_of_isCoercive (by linarith)
    ((isCoercive_of_opNorm_close h0 hclose).add_smul_one x)

end Criterion

section Family

open Balaban.Localization

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ 1 ϱ) {N : ℕ}

/-- **Analyticity of `A_e(s)` in `(e, α, s)`** (BASE-KERNEL-3 (1.9)): if the entries of a complex
background `e`, of the potential `α` and of the parameters `s` are analytic at `z₀`, so are the
entries of `A_e(s)`. -/
theorem baseOp_rectAt_general (a : ℕ → ℝ) (ν : ℝ) (e : ℂ → G.Ω 1 → Fin N → ℂ)
    (α : ℂ → G.Ω 1 → ℂ) (s : ℂ → FineBond d L N₀ → ℂ) (z0 : ℂ)
    (he : ∀ y i, AnalyticAt ℂ (fun z => e z y i) z0) (hα : ∀ y, AnalyticAt ℂ (fun z => α z y) z0)
    (hs : ∀ b, AnalyticAt ℂ (fun z => s z b) z0) :
    RectAt (fun z => baseOp N (e z) (baseHamiltonian G a ν (α z) (s z))) z0 := by
  have hH : RectAt (fun z => baseHamiltonian G a ν (α z) (s z)) z0 := by
    intro i j
    simp only [baseHamiltonian_apply]
    refine (analyticAt_const.add ?_).add ?_
    · by_cases h : i = j
      · simp only [h, ite_true]; exact hα j
      · simp only [h, ite_false]; exact analyticAt_const
    · exact Finset.analyticAt_fun_sum _ fun b _ => (hs b).mul analyticAt_const
  have hF : RectAt (fun z => fieldMul (e z)) z0 := by
    intro p y
    simp only [fieldMul]
    by_cases h : p.1 = y
    · simp only [h, ite_true]; exact he y p.2
    · simp only [h, ite_false]; exact analyticAt_const
  have hFt : RectAt (fun z => (fieldMul (e z))ᵀ) z0 := fun y p => by
    simp only [Matrix.transpose_apply]; exact hF p y
  have hP : RectAt (fun z => basePart (e z)) z0 := by
    unfold basePart; exact hF.mul hFt
  have hQ : RectAt (fun z => (1 - basePart (e z))) z0 := (RectAt.const _ _).sub hP
  unfold baseOp
  exact ((hQ.mul (RectAt.liftOp hH)).mul hQ).add hP

/-- **The resolvent is analytic wherever the norm criterion (1.9) holds**: if the reference
`A_{e⁰}(r)` is `c`-coercive and `‖A_e(s) - A_{e⁰}(r)‖ ≤ c/2` at `z₀`, the entries of
`𝒞_{e,x}(s)` are analytic at `z₀`. -/
theorem rectAt_inv_of_close {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ℂ → Matrix ι ι ℂ}
    {A0 : Matrix ι ι ℂ} {γ : ℝ} (hγ : 0 < γ) (h0 : IsCoercive A0 γ) {z0 : ℂ}
    (hA : RectAt A z0) (hclose : ‖A z0 - A0‖ ≤ γ / 2) {x : ℝ} (hx : 0 ≤ x) :
    RectAt (fun z => (A z + (x : ℂ) • (1 : Matrix ι ι ℂ))⁻¹) z0 := by
  have hU := (opNorm_resolvent_of_close hγ h0 hclose hx).1
  exact RectAt.inv (hA.add (RectAt.const _ _)) ((Matrix.isUnit_iff_isUnit_det _).1 hU).ne_zero

end Family

end Balaban.LargeField.Base
