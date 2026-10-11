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
open scoped ComplexOrder

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

/-- The source `S` of (1.1) is affine in the data, so its tangent is the source of the tangent
data (without the weights `a`, mass `ν` or generating set changing): for differentiable families
`Ψ(t)`, `h̃(t)`, `Ṡ = Q* a Ψ̇ + ν ḣ + 𝔟(Ψ̇)`. -/
theorem source_hasDerivAt (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)
    {Ψt ht : ℂ → Torus d (N₀ * L ^ k) → Fin N → ℂ} {Ψd hd : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {t₀ : ℂ} (hΨ : HasDerivAt Ψt Ψd t₀) (hh : HasDerivAt ht hd t₀) :
    HasDerivAt (fun t p => qStar G a (Ψt t) p + (ν : ℂ) * ht t p.1 p.2 +
        boundaryTerm G (Ψt t) p)
      (fun p => qStar G a Ψd p + (ν : ℂ) * hd p.1 p.2 + boundaryTerm G Ψd p) t₀ := by
  classical
  refine hasDerivAt_pi.2 fun p => ?_
  have hΨ' : ∀ x i, HasDerivAt (fun t => Ψt t x i) (Ψd x i) t₀ := fun x i =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hΨ x) i
  have hh' : ∀ x i, HasDerivAt (fun t => ht t x i) (hd x i) t₀ := fun x i =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hh x) i
  have hite : ∀ (c : Prop) [Decidable c] (x : Torus d (N₀ * L ^ k)) (i : Fin N),
      HasDerivAt (fun t => if c then Ψt t x i else 0) (if c then Ψd x i else 0) t₀ := by
    intro c _ x i
    by_cases hc : c
    · simp only [hc, ↓reduceIte]; exact hΨ' x i
    · simp only [hc, ↓reduceIte]; exact hasDerivAt_const _ _
  refine ((((hΨ' p.1 p.2).const_mul _).add ((hh' p.1 p.2).const_mul _))).add ?_
  unfold boundaryTerm
  exact HasDerivAt.fun_sum fun μ _ => (hite _ _ _).add (hite _ _ _)

end Derivative

section Positivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`G − Π ⪰ 0`** (abstract form): for `A` positive semidefinite, `φ` real and
`φ · A φ` invertible, `liftOp A − constrainedOp A φ = Eᴴ (liftOp A) E` with
`E = 1 − φ [φ · A φ]⁻¹ φ · A`, hence positive semidefinite. -/
theorem sub_constrainedOp_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) {φ : ι → Fin N → ℂ}
    (hφ : ∀ x i, star (φ x i) = φ x i) (hM : IsUnit (constraintForm A φ)) :
    (liftOp N A - constrainedOp A φ).PosSemidef := by
  set Lg := liftOp N A with hLg
  set T := fieldMul φ with hT
  set M := constraintForm A φ with hMdef
  have hL : Lg.PosSemidef := liftOp_posSemidef hA
  have hTH : Tᴴ = Tᵀ := fieldMul_conjTranspose hφ
  have hMpsd : M.PosSemidef := by
    rw [hMdef, constraintForm, ← hTH]
    exact hL.conjTranspose_mul_mul_same _
  have hMi : (M⁻¹).PosSemidef := hMpsd.inv
  have hMinv : M⁻¹ * M = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hM)
  set X := T * M⁻¹ * Tᵀ with hX
  have hXH : Xᴴ = X := by
    rw [hX, conjTranspose_mul, conjTranspose_mul, hMi.isHermitian.eq]
    have : (Tᵀ)ᴴ = T := by
      rw [← hTH, conjTranspose_conjTranspose]
    rw [this, ← hTH, Matrix.mul_assoc]
  have hXLX : X * Lg * X = X := by
    have hMe : Tᵀ * Lg * T = M := by rw [hMdef, constraintForm]
    calc X * Lg * X = T * M⁻¹ * (Tᵀ * Lg * T) * M⁻¹ * Tᵀ := by
          simp only [hX, Matrix.mul_assoc]
      _ = T * M⁻¹ * M * M⁻¹ * Tᵀ := by rw [hMe]
      _ = X := by
          rw [show T * M⁻¹ * M * M⁻¹ * Tᵀ = T * (M⁻¹ * M) * M⁻¹ * Tᵀ by simp only [Matrix.mul_assoc],
            hMinv, Matrix.mul_one]
  have hPi : constrainedOp A φ = Lg * X * Lg := by
    unfold constrainedOp; simp only [hX, hLg, hT, Matrix.mul_assoc]; rfl
  have hE : (1 - X * Lg)ᴴ = 1 - Lg * X := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, hXH, hL.isHermitian.eq]
  have key : (1 - Lg * X) * Lg * (1 - X * Lg) = Lg - Lg * X * Lg := by
    have e : (1 - Lg * X) * Lg * (1 - X * Lg) =
        Lg - Lg * X * Lg - Lg * X * Lg + Lg * X * Lg * X * Lg := by noncomm_ring
    have e2 : Lg * X * Lg * X * Lg = Lg * X * Lg := by
      rw [show Lg * X * Lg * X * Lg = Lg * (X * Lg * X) * Lg by simp only [Matrix.mul_assoc], hXLX]
    rw [e, e2]; abel
  have := hL.conjTranspose_mul_mul_same (1 - X * Lg)
  rw [hE, key, ← hPi] at this
  exact this

end Positivity

/-- **Proposition 5.4 (b)**: for real data (`α₀` and `φ₀ = restrictField G Φ` real) the
constrained Green's function `G − Π` of the linear response is positive semidefinite. -/
theorem green_sub_constrainedOp_posSemidef {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {α₀ : G.Ω 1 → ℂ} {δ : ℝ} {Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (St : Standing G a ν α₀ δ Φ) (hα : ∀ x, star (α₀ x) = α₀ x)
    (hΦ : ∀ (x : G.Ω 1) (i : Fin N), star (restrictField G Φ x i) = restrictField G Φ x i) :
    (liftOp N (dirichletOperator G a ν α₀)⁻¹ -
      constrainedOp (dirichletOperator G a ν α₀)⁻¹ (restrictField G Φ)).PosSemidef :=
  sub_constrainedOp_posSemidef
    (dirichletGreen_posSemidef G St.pos St.mass St.weights α₀ St.alpha hα) hΦ
    (constraintForm_isUnit St)

/-- **Proposition 5.4 (a), bounds**: under the hypotheses of `constrained_sup` the tangent
`φ̇ = (G − Π) Ṡ` obeys `|φ̇|₀, |∂φ̇|₁, |Δ^D φ̇|₂ ≤ (B + B₁') C` if `ℓ² |Ṡ| ≤ C`. -/
theorem linearResponse_sup {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {α₀ : G.Ω 1 → ℂ} {δ : ℝ} {Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hd : 3 ≤ d) (hL : 3 ≤ L) (St : Standing G a ν α₀ δ Φ)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (hϱ : 2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1))
    (hδ : (1 + sandwichConst d L N) * δ ≤ 1 / 2) {Sd φd : G.Ω 1 × Fin N → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hSd : ∀ (x : G.Ω 1) (i : Fin N), G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖Sd (x, i)‖ ≤ C)
    (hφd : φd = (liftOp N (dirichletOperator G a ν α₀)⁻¹ -
        constrainedOp (dirichletOperator G a ν α₀)⁻¹ (restrictField G Φ)) *ᵥ Sd) :
    SupBounds G φd ((greenSupConst d L + piSupConst d L N) * C) := by
  rw [hφd]
  exact (constrained_sup hd hL St hν1 hϱ hδ Sd hC hSd).2

end Balaban.Background
