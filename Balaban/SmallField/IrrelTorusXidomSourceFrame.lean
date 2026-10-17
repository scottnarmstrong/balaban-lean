/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomFrameField
public import Balaban.SmallField.IrrelTorusXidomClose
public import Balaban.SmallField.PsiGeomTube
import Mathlib.Tactic.Linarith

/-!
# A real-centre frame for the scaled composition witness
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N j : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {ν τ ζ : ℝ}
  {p : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
  {z h' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- Source chart clauses supply a real frame with the coordinate estimates used in the
small-polymer tube comparison. -/
theorem ScaledPsiC.exists_real_frame_bounds (H : ScaledPsiC G ν τ ζ j p h z h')
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ G.Ω 1) (hyj : G.layerIndex y = j)
    {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200) :
    ∃ Q : Matrix (Fin N) (Fin N) ℝ,
      Q.transpose * Q = 1 ∧
      Q.mulVec (p y) = rn (p y) • (Pi.single i₀ 1 : Fin N → ℝ) ∧
      (∀ i, ‖(cmat Q).mulVec (fun l => (p y l : ℂ) + z y l) i -
        (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ τ ^ 2 * ζ + 2 * N * ζ) ∧
      (∀ i, ‖(cmat Q).mulVec
        (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) •
          fun l => (h l : ℂ) + h' y l) i -
        ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) *
          (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ 13 * N * τ ^ 2 * ζ) ∧
      ‖(cmat Q).mulVec
        (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) •
          fun l => (h l : ℂ) + h' y l) i₀ -
        ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ)‖ < 2 * τ ^ 2 * ζ ^ 2 := by
  have hyd : y ∈ dataSites G := (mem_dataSites G).2 (Or.inl hy)
  have hp := H.r2 y hyd
  have hz := H.c2a y hyd
  have hrpos : 0 < rn (p y) := rn_pos_of_close hτ hτ1 hζ (by linarith) hp
  obtain ⟨Q, hQ, hQp, hQnorm, -⟩ := exists_real_center_frame hne (p y) hrpos
  have hQe := realOrth_transpose_frame hQ hQnorm
  have hclose := Balaban.SmallField.ScaledPsiC.b_close H hy hyj hν hτ hτ1 hντ hζ hζ1
  have hr : (ν * ((L : ℝ) ^ j) ^ 2) *
      |1 - (∑ i, p y i * h i) / rn (p y)| < τ ^ 2 * ζ ^ 2 := by
    simpa only [hyj, mul_pow] using H.r3 y hyd
  have hc : (ν * ((L : ℝ) ^ j) ^ 2) *
      ‖∑ i, ((p y i / rn (p y) : ℝ) : ℂ) * h' y i‖ < τ ^ 2 * ζ ^ 2 := by
    simpa only [hyj, mul_pow] using H.c3b y hy
  have hfield := realFrame_field_coords hν hτ hτ1 hζ hντ hp hz hclose hr hc hQ hQp hQe
  exact ⟨Q, hQ, hQp, realFrame_source_center_close hτ1 hζ hp hz hQ hQp,
    hfield.1, hfield.2⟩

end Balaban.SmallField
