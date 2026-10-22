/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BasePstTransport
import Mathlib.Tactic.Linarith

/-!
# Covariance of the local term `P(S)` under a measure-preserving change of the block variables

`Pst_equiv`: if a measurable equivalence `e` of the block configurations preserves the product measure and
`H' y (e Φ) = H y Φ`, then `Pst μ Lab H' S = Pst μ Lab H S` (`Pst_transport` with `σ = id`).  For the
rotations, `e` is the componentwise action on the block variables (the truncated standard Gaussian blocks
are rotation invariant) and `H'` is the family of activities at the rotated datum (`chartTerm_rot`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.Polymer Balaban.Polymer.TwoTorusStep
  MeasureTheory Finset

open scoped Classical

section PstRot

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}
  {Ω : Set (Balaban.Localization.CTorus d L N₁ m₁ K)} {Lb : Type*} [Fintype Lb]

/-- **Covariance of the local term `P(S)` under a measure-preserving change of the block variables.**
If `e` is a measurable equivalence of the block configurations preserving the product measure and the
activities satisfy `H' y (e Φ) = H y Φ`, then `Pst μ Lab H' S = Pst μ Lab H S`.  (Rotations act on the
block variables by `e`; the truncated Gaussian blocks are rotation invariant.) -/
theorem Pst_equiv {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (Lab : CubeLabels m₀ j Ω Lb) (H H' : Lb → (∀ b, Ωb b) → ℂ)
    (hHdep : ∀ y, DepOn (blocksOf m₀ j Ω (Lab.ysite y)) (H y))
    (e : (∀ b, Ωb b) ≃ᵐ (∀ b, Ωb b)) (he : MeasurePreserving e (Measure.pi μ) (Measure.pi μ))
    (hH : ∀ y Φ, H' y (e Φ) = H y Φ) (S : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)) :
    Pst μ Lab H' S = Pst μ Lab H S := by
  have key := Pst_transport (N₁' := N₁) (Ω' := Ω) μ μ Lab Lab H H' hHdep (fun b => b) S
    (fun _ _ _ _ h => h) (fun Φ Φ' => Φ' = e Φ)
    (fun Z _ F F' _ hFF => by
      have h1 : ∫ Φ, F' (e Φ) ∂(Measure.pi μ) = ∫ Φ', F' Φ' ∂(Measure.pi μ) :=
        he.integral_comp' F'
      rw [← h1]
      exact integral_congr_ae (Filter.Eventually.of_forall fun Φ => hFF Φ (e Φ) rfl))
    (fun _ => True) (fun _ => True) (fun y hy => absurd trivial hy) (fun y hy => absurd trivial hy)
    (fun y _ _ => y) (fun _ _ _ => trivial) (fun y _ _ => by simp)
    (fun y₁ _ _ y₂ _ _ h => h) (fun y' _ hy' => ⟨y', trivial, by simpa using hy', rfl⟩)
    (fun y _ _ Φ Φ' hR => by rw [hR]; exact hH y Φ)
  simpa using key

end PstRot

end Balaban.LargeField.Base
