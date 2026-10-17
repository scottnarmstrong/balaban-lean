/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.C1StarFromStep
public import Balaban.Correlations.RootCFromFlow

/-!
# Root-C after the physical step reduction

`c1Star_of_physical_step_targets` supplies the `hStep` premise below. The same block
factor and polymer multiplier must be used in the Root-F clauses and in `C1Star`.
-/

@[expose] public section

namespace Balaban.Correlations

/-- Pair the physical step output with Root-F clauses at the same `L` and `M`. -/
theorem rootFAndC1Star_of_rootF_step_output (d N L M : ℕ) (hN : 2 ≤ N)
    (hL : 3 ≤ L) (hM : 1 ≤ M) (δ β₀ : ℝ) (hδ : 0 < δ)
    (hRootF : ∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
        ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧
          1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
          ∃ T : RootFFamily d N,
            RootFClauses d N L M β ν h kf (kappaStar d) 1 δ T)
    (hStep : Nonempty (@C1Star d N L M ⟨by omega⟩ hN)) :
    RootFAndC1Star d N hN := by
  exact ⟨δ, hδ, L, M, hL, hM, β₀, hRootF, hStep⟩

/-- Root-C follows after the named physical step outputs have provided `C1Star` and
Root-F has been proved for the same scale parameters. -/
theorem rootC_of_rootF_step_output (d N L M : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)
    (hL : 3 ≤ L) (hM : 1 ≤ M) (δ β₀ : ℝ) (hδ : 0 < δ)
    (hRootF : ∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 0 < ν → ν ≤ 1 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
        ∃ kf : ℕ, (L : ℝ) ^ kf * Real.sqrt ν ≤ L ∧
          1 / 2 ≤ (L : ℝ) ^ (kf + 1) * Real.sqrt ν ∧
          ∃ T : RootFFamily d N,
            RootFClauses d N L M β ν h kf (kappaStar d) 1 δ T)
    (hStep : Nonempty (@C1Star d N L M ⟨by omega⟩ hN)) :
    RootCStatement d N :=
  rootC_of_rootFAndC1Star d N hd hN
    (rootFAndC1Star_of_rootF_step_output d N L M hN hL hM δ β₀ hδ hRootF hStep)

end Balaban.Correlations
