/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Xi

/-!
# Uniqueness of the data realizing a real datum

Two background data `D`, `D'` of the same generating set that realize the same real datum
`(Ψ₀, h₀)` are equal.  (Moved from `Def6Inhabited`, so that the second-version class can use it
without importing the witnesses.)
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem bgData_eq {N₀ : ℕ} [NeZero N₀] {G : GeneratingSet d L N₀ k ϱ} {D D' : BgData G N}
    (h1 : D.Ψ = D'.Ψ) (h2 : D.h = D'.h) : D = D' := by
  cases D; cases D'
  simp only at h1 h2
  subst h1; subst h2; rfl

theorem realizes_unique {N₀ : ℕ} [NeZero N₀] {G : GeneratingSet d L N₀ k ϱ} {D D' : BgData G N}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (h : Realizes D Ψ₀ h₀) (h' : Realizes D' Ψ₀ h₀) : D = D' := by
  refine bgData_eq (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · by_cases hx : x ∈ dataSites G
    · rw [h.1 x hx i, h'.1 x hx i]
    · rw [D.Ψ_zero x hx, D'.Ψ_zero x hx]
  · by_cases hx : x ∈ G.Ω 1
    · rw [h.2 x hx i, h'.2 x hx i]
    · rw [D.h_zero x hx, D'.h_zero x hx]

end Balaban.SmallField.Def6
