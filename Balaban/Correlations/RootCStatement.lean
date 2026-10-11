/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Frozen.Model.TwoPointTruncated
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# The statement of Root-C, as a predicate

`RootCStatement d N` is a verbatim copy of the type of the frozen root
`Balaban.lowTemperature_correlations` (`Balaban/Frozen/Roots/LowTemperatureCorrelations.lean`),
which is a draft root and is not imported (nor is its provider).  The theorem
`Balaban.Correlations.rootC_of_rootF_c1Star` (`Balaban/Correlations/Assembly.lean`) proves
`RootCStatement d N` from the clauses of Root-F, the interface C-1* and the Gaussian kernel
hypotheses; the equality of `RootCStatement` with the type of the frozen root is checked by a probe
outside the repository.
-/

@[expose] public section

namespace Balaban.Correlations

open Filter Topology

/-- The statement of Root-C (P9 Theorem 1.1 for hard spins), copied from the type of
`Balaban.lowTemperature_correlations`. -/
def RootCStatement (d N : ℕ) : Prop :=
    3 ≤ d → 2 ≤ N →
    ∃ β₀ c c' ρ₀ ρ₁ : ℝ, ∃ q : ℕ, 2 ≤ q ∧ 0 < c ∧ 0 < c' ∧ 0 < ρ₀ ∧ 0 < ρ₁ ∧ ρ₁ < 1 ∧
    ∀ β : ℝ, β₀ ≤ β →
    ∃ (m : ℝ → ℝ) (Gtr Glg : ℝ → (Fin d → ℤ) → ℝ),
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
        ∀ x y : Fin d → ℤ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
          ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₀ ∣ ℓ →
            (∀ i, |onePoint d N ℓ β ν h (fun μ => (x μ : ZMod ℓ)) i - m ν * h i| < ε) ∧
            ∀ i k, |twoPointTruncated d N ℓ β ν h (fun μ => (x μ : ZMod ℓ))
                (fun μ => (y μ : ZMod ℓ)) i k
              - (Gtr ν (x - y) * ((if i = k then 1 else 0) - h i * h k)
                  + Glg ν (x - y) * (h i * h k))| < ε) ∧
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 →
        |m ν - 1| ≤ c * β ^ (-1 + ρ₁) ∧
        ∀ x : Fin d → ℤ,
          |Gtr ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖)) ∧
          |Glg ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖))) ∧
      ∃ (m₀ γ : ℝ) (Gtr₀ Glg₀ G : (Fin d → ℤ) → ℝ),
        Tendsto m (𝓝[>] 0) (𝓝 m₀) ∧
        (∀ x, Tendsto (fun ν => Gtr ν x) (𝓝[>] 0) (𝓝 (Gtr₀ x))) ∧
        (∀ x, Tendsto (fun ν => Glg ν x) (𝓝[>] 0) (𝓝 (Glg₀ x))) ∧
        (∀ x, ∑ μ : Fin d, (2 * G x - G (x + Pi.single μ 1) - G (x - Pi.single μ 1))
          = if x = 0 then 1 else 0) ∧
        Tendsto G cofinite (𝓝 0) ∧
        0 < γ ∧ |γ - 1| ≤ c / β ∧
        ∀ x : Fin d → ℤ,
          |Gtr₀ x - m₀ ^ 2 / (β * γ) * G x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) ∧
          |Glg₀ x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀))

end Balaban.Correlations
