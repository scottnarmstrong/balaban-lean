/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Data
public import Balaban.Background.Contraction
public import Balaban.Multiscale.ConstraintSandwich
public import Balaban.Multiscale.Constrained
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The linear response and the constrained operator `Π` (BACKGROUND.md §5.5, Proposition 5.4)

For a family `t ↦ (φ(t), α(t))` of solutions of (EL) with sources `S(t)` (a differentiable family;
for the solution of Theorem 5.2 the data enter (EL) affinely, so `Ṡ = Q* a Ψ̇ + 𝔟(Ψ̇) + ν ḣ`,
`Balaban.Background.source_hasDerivAt`), the derivatives are

`α̇ = [φ · G φ]⁻¹ φ · G Ṡ`,  `φ̇ = (G − Π) Ṡ`,  `G = H_D(α)⁻¹`, `Π = constrainedOp G φ`,

with no use of the constraint beyond its first derivative (`Balaban.Background.linearResponse`).
For real data `G − Π ⪰ 0` (`Balaban.Background.green_sub_constrainedOp_posSemidef`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset Filter Topology

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Algebra

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α₀ : G.Ω 1 → ℂ} {δ : ℝ}
  {Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **The algebra of Proposition 5.4**: the linearized system
`H_D(α) φ̇ + α̇ φ = Ṡ`, `φ · φ̇ = 0` determines `(φ̇, α̇)`. -/
theorem response_solve (St : Standing G a ν α₀ δ Φ) {Sd φd : G.Ω 1 × Fin N → ℂ} {αd : G.Ω 1 → ℂ}
    (E1 : liftOp N (dirichletOperator G a ν α₀) *ᵥ φd + fieldMul (restrictField G Φ) *ᵥ αd = Sd)
    (E2 : (fieldMul (restrictField G Φ))ᵀ *ᵥ φd = 0) :
    αd = (constraintForm (dirichletOperator G a ν α₀)⁻¹ (restrictField G Φ))⁻¹ *ᵥ
        ((fieldMul (restrictField G Φ))ᵀ *ᵥ (liftOp N (dirichletOperator G a ν α₀)⁻¹ *ᵥ Sd)) ∧
      φd = (liftOp N (dirichletOperator G a ν α₀)⁻¹ -
        constrainedOp (dirichletOperator G a ν α₀)⁻¹ (restrictField G Φ)) *ᵥ Sd := by
  set H := dirichletOperator G a ν α₀ with hH
  set T := fieldMul (restrictField G Φ) with hT
  set Lg := liftOp N H⁻¹ with hLg
  set M := constraintForm H⁻¹ (restrictField G Φ) with hM
  have hHu : IsUnit H := dirichletOperator_isUnit G St.pos St.mass St.weights α₀ St.alpha
  have hMu : IsUnit M := constraintForm_isUnit St
  have hφd : φd = Lg *ᵥ (Sd - T *ᵥ αd) := by
    rw [← E1, add_sub_cancel_right, hLg]
    exact (liftOp_inv_mulVec hHu φd).symm
  have hMα : M *ᵥ αd = Tᵀ *ᵥ (Lg *ᵥ Sd) := by
    have h0 := E2
    rw [hφd, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at h0
    have : M = Tᵀ * Lg * T := by
      rw [hM, constraintForm, hLg, hT]
    have h0' := sub_eq_zero.1 h0
    rw [this, ← h0', Matrix.mulVec_mulVec]
  have hαd : αd = M⁻¹ *ᵥ (Tᵀ *ᵥ (Lg *ᵥ Sd)) := by
    rw [← hMα, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hMu), Matrix.one_mulVec]
  refine ⟨hαd, ?_⟩
  rw [hφd, hαd]
  unfold constrainedOp
  rw [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec]

end Algebra

section Derivative

theorem hasDerivAt_mulVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) {w : ℂ → ι → ℂ}
    {w' : ι → ℂ} {t₀ : ℂ} (h : HasDerivAt w w' t₀) (p : ι) :
    HasDerivAt (fun t => (A *ᵥ w t) p) ((A *ᵥ w') p) t₀ := by
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum (fun q _ => (hasDerivAt_pi.1 h q).const_mul (A p q))

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ} {α₀ : G.Ω 1 → ℂ} {δ : ℝ}
  {Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **Proposition 5.4** (BACKGROUND.md §5.5; consumed by I-4, P3 (3.9), P4 (2.23)).  Let
`t ↦ (φ(t), α(t))` be a family of solutions of (EL) for sources `S(t)` (differentiable at `t₀`;
for a solution family of Theorem 5.2 these are analytic), `(φ, α)(t₀) = (φ₀, α₀)` with the
standing hypotheses `Standing G a ν α₀ δ Φ` of the constrained operator (`Φ` a torus field
restricting to `φ₀`).  Then, with `G = H_D(α₀)⁻¹`, `Π = constrainedOp G φ₀`,
`α̇ = [φ₀ · G φ₀]⁻¹ φ₀ · G Ṡ` and `φ̇ = (G − Π) Ṡ`.  Only the first derivative of the constraint
is used (the constraint `φ · φ = 1` is not assumed to hold exactly at `t₀` beyond the family). -/
theorem linearResponse (St : Standing G a ν α₀ δ Φ) {S φ : ℂ → G.Ω 1 × Fin N → ℂ}
    {α : ℂ → G.Ω 1 → ℂ} {t₀ : ℂ} {Sd φd : G.Ω 1 × Fin N → ℂ} {αd : G.Ω 1 → ℂ}
    (hS : HasDerivAt S Sd t₀) (hφ : HasDerivAt φ φd t₀) (hα : HasDerivAt α αd t₀)
    (hα₀ : α t₀ = α₀) (hφ₀ : ∀ (z : G.Ω 1) (i : Fin N), φ t₀ (z, i) = restrictField G Φ z i)
    (hEL : ∀ᶠ t in 𝓝 t₀, liftOp N (dirichletOperator G a ν (α t)) *ᵥ φ t = S t ∧
      ∀ z : G.Ω 1, ∑ i, φ t (z, i) * φ t (z, i) = 1) :
    αd = (constraintForm (dirichletOperator G a ν α₀)⁻¹ (restrictField G Φ))⁻¹ *ᵥ
        ((fieldMul (restrictField G Φ))ᵀ *ᵥ (liftOp N (dirichletOperator G a ν α₀)⁻¹ *ᵥ Sd)) ∧
      φd = (liftOp N (dirichletOperator G a ν α₀)⁻¹ -
        constrainedOp (dirichletOperator G a ν α₀)⁻¹ (restrictField G Φ)) *ᵥ Sd := by
  refine response_solve St ?_ ?_
  · funext ⟨z, i⟩
    have hF : HasDerivAt (fun t => (liftOp N (dirichletOperator G a ν α₀) *ᵥ φ t) (z, i) +
        (α t z - α₀ z) * φ t (z, i))
        ((liftOp N (dirichletOperator G a ν α₀) *ᵥ φd) (z, i) +
          (αd z * φ t₀ (z, i) + (α t₀ z - α₀ z) * φd (z, i))) t₀ := by
      refine (hasDerivAt_mulVec _ hφ (z, i)).add ?_
      have h1 : HasDerivAt (fun t => α t z - α₀ z) (αd z) t₀ :=
        (hasDerivAt_pi.1 hα z).sub_const _
      exact h1.mul (hasDerivAt_pi.1 hφ (z, i))
    have hev : (fun t => S t (z, i)) =ᶠ[𝓝 t₀] fun t =>
        (liftOp N (dirichletOperator G a ν α₀) *ᵥ φ t) (z, i) + (α t z - α₀ z) * φ t (z, i) := by
      filter_upwards [hEL] with t ht
      have := liftOp_dirichlet_add (G := G) (N := N) a ν α₀ (α t - α₀) (φ t) (z, i)
      rw [add_sub_cancel] at this
      rw [← ht.1, this]; rfl
    have hu := (hF.congr_of_eventuallyEq hev).unique (hasDerivAt_pi.1 hS (z, i))
    rw [hα₀, sub_self, zero_mul, add_zero] at hu
    simp only [Pi.add_apply, fieldMul_mulVec]
    rw [hφ₀ z i] at hu
    linear_combination hu
  · funext z
    have hg : HasDerivAt (fun t => ∑ i, φ t (z, i) * φ t (z, i))
        (∑ i, (φd (z, i) * φ t₀ (z, i) + φ t₀ (z, i) * φd (z, i))) t₀ := by
      refine HasDerivAt.fun_sum (fun i _ => ?_)
      exact (hasDerivAt_pi.1 hφ (z, i)).mul (hasDerivAt_pi.1 hφ (z, i))
    have hev : (fun _ : ℂ => (1 : ℂ)) =ᶠ[𝓝 t₀] fun t => ∑ i, φ t (z, i) * φ t (z, i) := by
      filter_upwards [hEL] with t ht
      exact (ht.2 z).symm
    have hu := (hg.congr_of_eventuallyEq hev).unique (hasDerivAt_const t₀ (1 : ℂ))
    rw [fieldMul_transpose_mulVec]
    simp only [Pi.zero_apply, hφ₀] at hu ⊢
    have : ∑ i, restrictField G Φ z i * φd (z, i) = 0 := by
      have e : ∑ i, (φd (z, i) * restrictField G Φ z i + restrictField G Φ z i * φd (z, i)) =
          2 * ∑ i, restrictField G Φ z i * φd (z, i) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e] at hu
      exact (mul_eq_zero.1 hu).resolve_left two_ne_zero
    exact this

end Derivative

end Balaban.Background
