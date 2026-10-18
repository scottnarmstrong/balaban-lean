/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassResponse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The same-datum coefficient source (P7 p. 500 (2.10)–(2.12))

Two Euler–Lagrange backgrounds on one datum `D` and one mass `ν`, with block coefficients `a₀`
and `a₁`: subtracting the two systems gives the perturbed system at coefficient `a₀` with zero
data change and the source
`f₁ = Q*(a₁ - a₀) (Ψ - Q φ¹)`, i.e. `f₁(x) = (a₁ - a₀)(ℓ_x) ℓ_x⁻² (Ψ(x) - (Q φ¹)(x))`.

* `liftOp_dirichlet_coeff`: the coefficient shift of the Dirichlet operator;
* `coeffSource_perturbed`: the difference of the two backgrounds solves the perturbed system;
* `coeffSource_bound`: the source bound `ℓ² |f₁| ≤ m · Bh`;
* `coeffChange_sameData_response_of_weighted`: the response bound, conditional on the weighted
  Proposition 5.1 predicate and the operator hypotheses.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- `Q*` is additive in the coefficient. -/
theorem qStar_sub_apply (a₁ a₀ : ℕ → ℝ) (Θ Θ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (p : G.Ω 1 × Fin N) :
    qStar G (a₁ - a₀) (fun y j => Θ y j - Θ' y j) p =
      qStar G (a₁ - a₀) Θ p - qStar G (a₁ - a₀) Θ' p := by
  simp only [qStar]; ring

/-- `Q* (a₁ - a₀) Ψ` is the difference of the two `Q* a Ψ`. -/
theorem qStar_coeff_sub (a₁ a₀ : ℕ → ℝ) (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (p : G.Ω 1 × Fin N) :
    qStar G a₁ Ψ p - qStar G a₀ Ψ p = qStar G (a₁ - a₀) Ψ p := by
  simp only [qStar, Pi.sub_apply]; push_cast; ring

/-- **Coefficient shift of the Dirichlet operator**: the difference of `H_D` at two block
coefficients is the block term of the difference, `Q*(a₁ - a₀) Q`. -/
theorem liftOp_dirichlet_coeff (a₁ a₀ : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (w : G.Ω 1 × Fin N → ℂ) (p : G.Ω 1 × Fin N) :
    (liftOp N (dirichletOperator G a₁ ν α) *ᵥ w) p =
      (liftOp N (dirichletOperator G a₀ ν α) *ᵥ w) p +
        qStar G (a₁ - a₀) (blockAvg G w) p := by
  obtain ⟨x, i⟩ := p
  rw [liftOp_mulVec, liftOp_mulVec, dirichlet_apply, dirichlet_apply]
  simp only [qStar, blockAvg, blockTerm, Pi.sub_apply, svec]
  push_cast
  ring

/-- **Same-datum coefficient source**: the two Euler–Lagrange systems on one datum and one mass,
at coefficients `a₀` and `a₁`, give the perturbed system at coefficient `a₀` with base `φ̄⁰`,
source `Q*(a₁ - a₀)(Ψ - Q φ¹)`, `δφ = φ¹ - φ⁰`, `δα = α¹ - α⁰`. -/
theorem coeffSource_perturbed (a₀ a₁ : ℕ → ℝ) (ν : ℝ) (D : BgData G N)
    {φ0 φ1 : G.Ω 1 × Fin N → ℂ} {α0 α1 : G.Ω 1 → ℂ}
    (h0 : IsEL G a₀ ν D φ0 α0) (h1 : IsEL G a₁ ν D φ1 α1) :
    IsPerturbed G a₀ ν α0 (barField G D.Ψ φ0)
      (fun p => qStar G (a₁ - a₀) (fun y j => D.Ψ y j - blockAvg G φ1 y j) p)
      (φ1 - φ0) (α1 - α0) := by
  have bar : ∀ (x : G.Ω 1) i, barField G D.Ψ φ0 x i = φ0 (x, i) := by
    intro x i; simp [barField, x.2]
  refine ⟨?_, ?_⟩
  · funext p
    have e0 := congrFun h0.1 p
    have e1 := congrFun h1.1 p
    rw [liftOp_dirichlet_coeff] at e1
    have ha := liftOp_dirichlet_add (G := G) (N := N) a₀ ν α0 (α1 - α0) φ1 p
    rw [add_sub_cancel] at ha
    rw [ha] at e1
    have t := qStar_coeff_sub (G := G) a₁ a₀ D.Ψ p
    have u := qStar_sub_apply (G := G) a₁ a₀ D.Ψ (blockAvg G φ1) p
    simp only [source, Pi.sub_apply] at e0 e1
    simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_sub, bar]
    linear_combination e1 - e0 + t - u
  · intro x
    have := h1.2 x
    simp only [bar, Pi.sub_apply]
    simpa using this

end Balaban.LargeField.ActionConv
