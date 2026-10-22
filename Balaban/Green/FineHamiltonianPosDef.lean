/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.UnitLattice
import Mathlib.Tactic.Positivity

/-!
# Positive definiteness of the unit-lattice operator

`fineHamiltonian_posDef`: `H = N² (-Δ) + ν + a Q* Q` is positive definite for `ν ≥ 0`, `a > 0`
(moved from `Green/FinalHessian`, statement unchanged, so that the single-scale block decay and the
Dirichlet problem can use it).
-/

@[expose] public section

namespace Balaban

open Matrix

variable {d ℓ Nb m : ℕ} [NeZero ℓ] [NeZero m]

theorem fineHamiltonian_posDef (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) : (fineHamiltonian d ℓ Nb m ν a).PosDef := by
  have hc : (0 : ℝ) < (Nb : ℝ) ^ 2 := by positivity
  have hH : fineHamiltonian d ℓ Nb m ν a =
      ((Nb : ℝ) ^ 2) • blockHamiltonian d ℓ Nb m (ν / (Nb : ℝ) ^ 2) (a / (Nb : ℝ) ^ 2) := by
    unfold fineHamiltonian blockHamiltonian
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hc.ne']
  rw [hH]
  exact (blockHamiltonian_posDef hℓ hN hd (by positivity) (by positivity)).smul hc

theorem fineHamiltonian_isUnit_det (hℓ : ℓ = Nb * m) (hN : 0 < Nb) (hd : 0 < d) {ν a : ℝ}
    (hν : 0 ≤ ν) (ha : 0 < a) : IsUnit (fineHamiltonian d ℓ Nb m ν a).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (fineHamiltonian_posDef hℓ hN hd hν ha).isUnit

end Balaban
