/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Minimizer

/-!
# The hard-spin action is exactly quadratic in the chord (LF-RECONSTRUCTION Lemma II.7.3)

For a constrained Euler–Lagrange point `(φ, α)` of the hard-spin action (`IsEL`) and any real unit
field `σ`, with chord `w = σ - φ`,
`A(σ) - A(φ) = ½ ⟨w, (H₀ + diag α) w⟩`
(P4 (2.44) at `λ = ∞`).  The identity holds for all spin configurations, not only on a chart.
It is the real-valued form of `Balaban.Background.actionC_sub_eq`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban.Multiscale Balaban.Background Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Lemma II.7.3** (the action is exactly quadratic in the chord).  For real data `D`, a
solution `(φ, α)` of (EL) that is a real unit field, and any real unit field `σ`,
`A(σ) - A(φ) = ½ ⟨σ - φ, (H₀ + diag α)(σ - φ)⟩`, where `dirichletOperator G a ν α` is
`H₀ + diag α`. -/
theorem action_sub_eq_chord_quadratic (D : BgData G N) (hD : D.IsReal)
    {φ σ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hφ : IsEL G a ν D φ α)
    (hφU : IsRealUnitField G φ) (hσU : IsRealUnitField G σ) :
    (((action G a ν D σ - action G a ν D φ : ℝ)) : ℂ) =
      (1 / 2) * pair G (σ - φ) (liftOp N (dirichletOperator G a ν α) *ᵥ (σ - φ)) := by
  have h1 := actionC_sub_eq (a := a) (ν := ν) D hφ (dot_eq_one_of_unit hσU)
  rw [← h1, Complex.ofReal_sub,
    action_cast D hD (fun x i => (hσU x).1 i), action_cast D hD (fun x i => (hφU x).1 i)]

/-- The chord identity with a real multiplier: the action difference is the real part of
`½ ⟨σ - φ, (H₀ + diag α)(σ - φ)⟩`. -/
theorem action_sub_eq_chord_quadratic_re (D : BgData G N) (hD : D.IsReal)
    {φ σ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hφ : IsEL G a ν D φ α)
    (hφU : IsRealUnitField G φ) (hσU : IsRealUnitField G σ) :
    action G a ν D σ - action G a ν D φ =
      ((1 / 2 : ℂ) * pair G (σ - φ) (liftOp N (dirichletOperator G a ν α) *ᵥ (σ - φ))).re := by
  rw [← action_sub_eq_chord_quadratic D hD hφ hφU hσU, Complex.ofReal_re]

end Balaban.LargeField
