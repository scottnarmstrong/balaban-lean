/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonGeomDef

/-!
# Sites near a set, layer index bound

`nearSet r P`: the sites within sup-distance `r` of `P` (the margin of the canonical covers is built from
it, `castZ`).  `layerIndex_le_top`: the layer index of a site is at most the top level.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Localization Balaban.LargeField

section Local

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L]

/-- The sites within sup-distance `r` of a set. -/
def nearSet (r : ℕ) (P : Set (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1)) :=
  {x | ∃ w ∈ P, supDist x w ≤ r}

omit [NeZero N₁] [NeZero L] in
theorem layerIndex_le_top {N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ' : ℝ}
    (G : GeneratingSet d L N₀ K ϱ') (x : Torus d (N₀ * L ^ K)) : G.layerIndex x ≤ K := by
  by_cases hx : x ∈ G.Ω 1
  · exact (G.layerIndex_spec hx).2.1
  · have : ¬ ∃ j, 1 ≤ j ∧ j ≤ K ∧ x ∈ G.layer j := fun ⟨j, h1, h2, h3⟩ =>
      hx (G.layer_subset h1 h2 h3)
    unfold GeneratingSet.layerIndex
    simp [this]

end Local

end Balaban.Inhabited
