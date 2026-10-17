/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FarDecay
import Mathlib.Tactic.Linarith

/-!
# Where the changed data lie (blocker 5)

If two fields `f`, `f'` on the sites agree at every site `x` of a set `B` and at every site `x` for
which some site `z ∈ B` is at path distance `< n` from a site `ω ∈ Ω₁` equal or adjacent to `x`, then
every site of the `Ω₁`-shadow of the set where `f ≠ f'` is at path distance `≥ n` from every site
of `B`.
-/

@[expose] public section

namespace Balaban.Green

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Fluctuation

/-- **The shadow of the set of changed sites is far from `B`.** -/
theorem shadow_far {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {B : Set (CTorus d L N₁ m₁ K)} {n : ℝ}
    {f f' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hag : ∀ x (i : Fin N), (x ∈ B ∨ ∃ z ∈ B, ∃ ω ∈ G.Ω 1, (ω = x ∨ Adj ω x) ∧
      G.pathDist z ω < ENNReal.ofReal n) → f' x i = f x i) {x : CTorus d L N₁ m₁ K} (hx : x ∈ B)
    {ω : CTorus d L N₁ m₁ K}
    (hω : ω ∈ shadow G (open Classical in Finset.univ.filter fun y => ∃ i, f' y i ≠ f y i)) :
    ENNReal.ofReal n ≤ G.pathDist x ω := by
  classical
  by_contra hlt
  push Not at hlt
  simp only [Balaban.Fluctuation.shadow, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  obtain ⟨hω1, hω2⟩ := hω
  rcases hω2 with ⟨i, hi⟩ | ⟨y, ⟨i, hi⟩, hadj⟩
  · exact hi (hag ω i (Or.inr ⟨x, hx, ω, hω1, Or.inl rfl, hlt⟩))
  · exact hi (hag y i (Or.inr ⟨x, hx, ω, hω1, Or.inr hadj, hlt⟩))

end Balaban.Green
