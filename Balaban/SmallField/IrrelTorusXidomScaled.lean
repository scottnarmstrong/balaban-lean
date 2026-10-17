/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomLong
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Longitudinal estimate from scaled composition data

The source fields of `ScaledPsiC`, together with the sharp square displacement supplied by
`xiC_scaledComposition_square_sharp`, imply the quadratic longitudinal bound at a level site.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Finset

variable {d L N₀ k N j : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {ν τ ζ : ℝ}
  {p : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
  {z h' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- The source `ScaledPsiC` witness implies the required longitudinal estimate at any site
of its top layer, once its sharp square displacement is supplied. -/
theorem ScaledPsiC.vInv_bound_of_square_sharp (H : ScaledPsiC G ν τ ζ j p h z h')
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (hyj : G.layerIndex y = j)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hsq : ‖∑ i, ((p y i : ℂ) + z y i) * ((p y i : ℂ) + z y i) -
      ∑ i, (p y i : ℂ) * (p y i : ℂ)‖ < τ ^ 2 * ζ) :
    ‖vInv (fun _ : Site d => fun i => (p y i : ℂ) + z y i)
      (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' y i) -
      (ν * ((L : ℝ) ^ j) ^ 2 : ℝ)‖ ≤ 98 * τ ^ 2 * ζ ^ 2 := by
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy)
  apply vInv_bound_of_source_tube (p := p y) (h := h) (z := z y) (h' := h' y)
    hν hτ hτ1 hντ hζ hζ1
  · simpa using H.r2 y hyd
  · simpa [hyj, mul_pow] using H.r3 y hyd
  · simpa [mul_pow] using H.r4
  · exact H.c2a y hyd
  · exact hsq
  · have hc := H.c3a y hy
    rw [hyj] at hc
    have he : (τ * ζ) ^ 2 / ζ = τ ^ 2 * ζ := by field_simp [hζ.ne']
    rwa [he] at hc
  · simpa [hyj, mul_pow] using H.c3b y hy

end Balaban.SmallField
