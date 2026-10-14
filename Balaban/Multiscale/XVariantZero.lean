/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.XVariantSharp
public import Balaban.Multiscale.XVariantAgmon

/-!
# The x-variant at the first step (`k = 0`)

At `k = 0` the weight condition `IsAdmissibleWeights 0 a` is empty, and the cores
`…_of_ak` of `XVariant.lean`, `XVariantSharp.lean` need only `a_0 ∈ [1/2, 2]`
(the weight entering `xS1 (a 0) x`, `xS2 (a 0) _ x`). This file records the instances.
-/

@[expose] public section

namespace Balaban.Multiscale

open Matrix

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The weight condition at `k = 0` is empty. -/
theorem isAdmissibleWeights_zero (a : ℕ → ℝ) : IsAdmissibleWeights 0 a :=
  fun _ h1 h2 => absurd h2 (by omega)

/-- **The x-variant operator at the first step is invertible**, with the sharp coercivity
constant: `k = 0`, only `a_0 ∈ [1/2, 2]` is needed. -/
theorem xDirichletOperator_isUnit_sharp_zero (G : GeneratingSet d L N₀ (0 + 1) ϱ)
    (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha0 : 1 / 2 ≤ a 0 ∧ a 0 ≤ 2)
    {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x) (α : G.Ω 1 → ℂ)
    (hα : ∀ y, ‖α y‖ ≤ (1 / 8) / (G.spacing y) ^ 2) :
    IsUnit (xDirichletOperator G a aT x ν α) :=
  xDirichletOperator_isUnit_sharp_of_ak G hL hν (isAdmissibleWeights_zero a) ha0 haT1 haT2 hx α
    hα

/-- **Coercivity at the first step** (`k = 0`, `0 ≤ θ < 1/4`). -/
theorem xDirichletOperator_isCoercive_sharp_zero (G : GeneratingSet d L N₀ (0 + 1) ϱ)
    (hL : 3 ≤ L) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (ha0 : 1 / 2 ≤ a 0 ∧ a 0 ≤ 2)
    {aT x : ℝ} (haT1 : 1 / 2 ≤ aT) (haT2 : aT ≤ 2) (hx : 0 ≤ x) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : θ < 1 / 4) (α : G.Ω 1 → ℂ) (hα : ∀ y, ‖α y‖ ≤ θ / (G.spacing y) ^ 2) {γ : ℝ}
    (hγ : ∀ y : G.Ω 1, γ ≤ ((G.spacing y) ^ 2)⁻¹) :
    Green.IsCoercive (xDirichletOperator G a aT x ν α) ((1 / 4 - θ) * γ) :=
  xDirichletOperator_isCoercive_sharp_of_ak G hL hν (isAdmissibleWeights_zero a) ha0 haT1 haT2 hx
    hθ0 hθ α hα hγ

end Balaban.Multiscale
