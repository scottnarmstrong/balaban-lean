/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ExpansionQuad
public import Balaban.Fluctuation.InteractionDir3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The quadratic form `deltaForm` has vanishing third derivative along lines

`V^{(k)} = ℰ - ½ ⟨ψ', Δ^{(k)} ψ'⟩` (Lemma 2.3 (b) with the chord identity): `deltaForm` is a quadratic
form in `ψ'`, so along a line `z + τ w` it is a polynomial of degree `≤ 2` in `τ` and its third
derivative vanishes (`iteratedDeriv_deltaForm_line`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Matrix

section Poly

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

theorem pair_line (u0 u1 v0 v1 : G.Ω 1 × Fin N → ℂ) (τ : ℂ) :
    pair G (u0 + τ • u1) (v0 + τ • v1) =
      pair G u0 v0 + τ * (pair G u0 v1 + pair G u1 v0) + τ ^ 2 * pair G u1 v1 := by
  unfold pair
  have h : ∀ p, (u0 + τ • u1) p * (v0 + τ • v1) p =
      u0 p * v0 p + τ * (u0 p * v1 p + u1 p * v0 p) + τ ^ 2 * (u1 p * v1 p) := by
    intro p; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_add_distrib]

theorem deltaForm_line (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (z w : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    ∃ c0 c1 c2 : ℂ, ∀ τ : ℂ,
      deltaForm h a ν α₁ φ₁ (fun x i => z x i + τ * w x i) = c0 + c1 * τ + c2 * τ ^ 2 := by
  classical
  set M := liftOp N (opHk h a ν α₁)⁻¹ - constrainedOp (opHk h a ν α₁)⁻¹ (fieldBase h φ₁) with hM
  have hq : ∀ τ : ℂ, qStar G a (fun x i => z x i + τ * w x i) =
      qStar G a z + τ • qStar G a w := by
    intro τ; funext p; simp only [qStar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hphi : ∀ (S : G.Ω 1 × Fin N → ℂ), phiOne h a ν α₁ φ₁ S = M *ᵥ S := fun S => rfl
  have hx : ∀ τ : ℂ, (fun p : G.Ω 1 × Fin N => (fun x i => z x i + τ * w x i) p.1 p.2) =
      (fun p : G.Ω 1 × Fin N => z p.1 p.2) + τ • (fun p : G.Ω 1 × Fin N => w p.1 p.2) := by
    intro τ; funext p; simp
  set Q0 := qStar G a z with hQ0
  set Q1 := qStar G a w with hQ1
  set z' : G.Ω 1 × Fin N → ℂ := fun p => z p.1 p.2 with hz'
  set w' : G.Ω 1 × Fin N → ℂ := fun p => w p.1 p.2 with hw'
  refine ⟨pair G z' Q0 - pair G Q0 (M *ᵥ Q0),
    (pair G z' Q1 + pair G w' Q0) - (pair G Q0 (M *ᵥ Q1) + pair G Q1 (M *ᵥ Q0)),
    pair G w' Q1 - pair G Q1 (M *ᵥ Q1), fun τ => ?_⟩
  unfold deltaForm
  rw [hx, hq, hphi, Matrix.mulVec_add, Matrix.mulVec_smul, pair_line, pair_line]
  ring

theorem iteratedDeriv_quad (c0 c1 c2 : ℂ) :
    iteratedDeriv 3 (fun τ : ℂ => c0 + c1 * τ + c2 * τ ^ 2) 0 = 0 := by
  have hd : ∀ τ : ℂ, HasDerivAt (fun τ : ℂ => c0 + c1 * τ + c2 * τ ^ 2) (c1 + 2 * c2 * τ) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℂ => c1 * τ) c1 τ := by simpa using (hasDerivAt_id τ).const_mul c1
    have h2 : HasDerivAt (fun τ : ℂ => c2 * τ ^ 2) (c2 * (2 * τ)) τ := by
      simpa using (hasDerivAt_pow 2 τ).const_mul c2
    have := (h1.const_add c0).add h2
    convert this using 1
    ring
  have h1 : deriv (fun τ : ℂ => c0 + c1 * τ + c2 * τ ^ 2) = fun τ => c1 + 2 * c2 * τ :=
    funext fun τ => (hd τ).deriv
  have h2 : deriv (fun τ : ℂ => c1 + 2 * c2 * τ) = fun _ => 2 * c2 := by
    funext τ
    have := (hasDerivAt_id τ).const_mul (2 * c2) |>.const_add c1
    simp
  rw [iteratedDeriv_succ', h1, iteratedDeriv_succ', h2]
  simp

end Poly

end Balaban.Fluctuation
