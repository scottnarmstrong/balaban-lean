/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33Bound
import Mathlib.Tactic.Linarith

/-!
# The labels `polyDom` are domains of `𝒟_{k+1}`

The label sets of the localized expansion (`polyDom`, and the `polymerDomains` of the sites) consist
of multiscale polymer domains (`polyDom_isMultiDom`), hence of domains `𝒟_lev` of the level
generating set (`isDj_of_isMultiDom`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **Every label `Y ∈ polyDom` is a domain of `𝒟_lev`.** -/
theorem isDj_of_polyDom {lev : ℕ} (hG' : IsLevel Gp lev) {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {j m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hS : CovSetup Gp m₀ j X 𝒦X) (hd : 3 ≤ d)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polyDom Gp X₁f m₀ j 𝒦X) : IsDj m₀ lev Y :=
  isDj_of_isMultiDom hG' (polyDom_isMultiDom hS hd hopt hY)

end Balaban.Fluctuation
