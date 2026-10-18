/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusE1Coef
public import Balaban.Inhabited.E0CoeffFamilyRotBlock

/-!
# Equivariance of the interpolation coefficient `gsumCoeff`

`gsumCoeff_rot`: if a coordinatewise measure-preserving equivalence `E` of the block variables
carries the activities and the marks of one family to those of another on an almost-sure set, the
coefficients coincide.  This is `gsumCoeff_transport` with the identity correspondence of blocks.
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open scoped Classical
open MeasureTheory Balaban Balaban.Localization Balaban.Fluctuation Balaban.Polymer
  Balaban.Multiscale

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
  {Lb : Type*} [Fintype Lb] {ι : Type*} [Fintype ι]

local notation "𝔅" => CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω

/-- **Equivariance of `gsumCoeff` under a sitewise measure-preserving equivalence.** -/
theorem gsumCoeff_rot {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)] (Lab : CubeLabels m₀ j Ω Lb)
    {εH κH κ0 Kc εH' κH' κ0' Kc' : ℝ}
    (A : ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (A' : ℂ → LabelAct Lab Ωb εH' κH' κ0' Kc')
    (y0 : ι → Lb) (G G' : ι → ℂ → (∀ b, Ωb b) → ℂ)
    (hGdep : ∀ i u, DepOn (blocksOf m₀ j Ω (Lab.ysite (y0 i))) (G i u))
    (T : Finset 𝔅) (E : ∀ b, Ωb b ≃ᵐ Ωb b) (hE : ∀ b, MeasurePreserving (E b) (μ b) (μ b))
    {Q : Set (∀ b, Ωb b)} (hQ : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q)
    (hA : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ∀ Φ ∈ Q,
      (A' (s : ℂ)).H y (fun b => E b (Φ b)) = (A (s : ℂ)).H y Φ)
    (hG : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, ∀ Φ ∈ Q,
      G' i (s : ℂ) (fun b => E b (Φ b)) = G i (s : ℂ) Φ) :
    gsumCoeff μ Lab A' y0 G' T = gsumCoeff μ Lab A y0 G T := by
  have h := gsumCoeff_transport (m₀ := m₀) (j := j) (Ω := Ω) (Ω' := Ω) (σ := (id : 𝔅 → 𝔅))
    μ μ Lab Lab A A' y0 y0 G G' hGdep T (Set.injOn_id _)
    (fun Φ Φ' => Φ ∈ Q ∧ Φ' = fun b => E b (Φ b))
    (fun Z _ F F' _ hFF => integral_comp_of_pi_equiv μ E hE hQ (fun Φ hΦ => hFF Φ _ ⟨hΦ, rfl⟩))
    (fun _ => True) (fun _ => True) (fun s hs y hy => absurd trivial hy)
    (fun s hs y hy => absurd trivial hy) (fun y _ _ => y) (fun _ _ _ => trivial)
    (fun y _ _ => by simp) (fun y₁ _ _ y₂ _ _ h => h)
    (fun y' _ hy' => ⟨y', trivial, by simpa using hy', rfl⟩)
    (fun s hs y _ _ Φ Φ' hR => by obtain ⟨hΦ, rfl⟩ := hR; exact hA s hs y Φ hΦ)
    (fun i _ => i) (fun i _ => by simp) (fun i₁ _ i₂ _ h => h)
    (fun i' hi' => ⟨i', by simpa using hi', rfl⟩)
    (fun s hs i _ Φ Φ' hR => by obtain ⟨hΦ, rfl⟩ := hR; exact hG s hs i Φ hΦ)
  simpa using h

end Balaban.Polymer.TwoTorusStep
