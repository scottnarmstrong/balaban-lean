/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLargeBackground
public import Balaban.Green.FinalRadiusClass
import Mathlib.Tactic.Linarith

/-!
# Analytic room for bounded retained data

The global cutoff comparison also leaves room for a nonzero retained background if half of
the class radius is reserved for it. This is a numerical statement. P7's variational chart
and the covariance on the complement of a selected bad set still require construction.
-/

@[expose] public section

noncomputable section

open Balaban.Inhabited Balaban.SmallField Balaban.LargeField.ActionConv Balaban.Analysis

namespace Balaban.Green

/-- The explicit beta threshold for a retained background of size at most half the class
radius. The second half is paid by the landed cutoff comparison, uniformly in the scale. -/
theorem retained_room_of_half_budget
    {d L : ℕ} [NeZero L] {B A₁ α α₀ β0 c D : ℝ} {p : ℕ}
    (hd : 2 ≤ d) (hp : 1 ≤ p) (hB : 0 ≤ B) (hA : 0 ≤ A₁)
    (hα₀ : 0 < α₀) (hc : 0 < c)
    (hα : α ≤ ((d : ℝ) - 2) * (1 / 4)) (hβ0 : 1 < β0)
    (hsize : B * A₁ * (4 * (p : ℝ)) ^ p < (c / 2) * α₀ * β0 ^ (1 / 4 : ℝ))
    (k : ℕ) (hD : D ≤ (c / 2) * epsSeq L α α₀ k) :
    D + B * (betaK d L k β0 ^ (-(1 / 2 : ℝ)) *
      pLog A₁ p (betaK d L k β0)) < c * epsSeq L α α₀ k := by
  have hc2 : 0 < c / 2 := by linarith
  have hT := cutConst_mul_pLog_lt_epsSeq (d := d) (L := L) (B := B)
    (A₁ := A₁) (α := α) (α₀ := α₀) (β0 := β0) (c := c / 2)
    hd hp hB hA hα₀ hc2 hα hβ0 hsize k
  linarith only [hD, hT]

/-- The W975 analytic cutoff theorem with its radius comparison supplied by the explicit
half-budget. The chart and restricted-covariance estimates remain visible hypotheses. -/
theorem retained_box_interaction_analytic_of_half_budget
    {d L : ℕ} [NeZero L] {B A₁ α α₀ β0 c D : ℝ} {p : ℕ}
    (hd : 2 ≤ d) (hp : 1 ≤ p) (hB : 0 ≤ B) (hA : 0 ≤ A₁)
    (hα₀ : 0 < α₀) (hc : 0 < c)
    (hα : α ≤ ((d : ℝ) - 2) * (1 / 4)) (hβ0 : 1 < β0)
    (hsize : B * A₁ * (4 * (p : ℝ)) ^ p < (c / 2) * α₀ * β0 ^ (1 / 4 : ℝ))
    (k : ℕ) (hD : D ≤ (c / 2) * epsSeq L α α₀ k)
    {P I : Type*} [Fintype P] [Fintype I]
    {γ : MeasureTheory.Measure (I → ℝ)} {ρ B' κ : ℝ}
    (hγ : γ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {G : (I → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G
      (polydisc (0 : I → ℂ) (fun _ => c * epsSeq L α α₀ k)))
    (hGB : ∀ w ∈ polydisc (0 : I → ℂ) (fun _ => c * epsSeq L α α₀ k),
      ‖G w‖ ≤ B')
    (u : I → ℂ) (hBackground : ∀ x, ‖u x‖ ≤ D)
    {Φ : (P → ℂ) → (I → ℝ) → (I → ℂ)}
    (hΦan : ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) →
      AnalyticOnNhd ℂ (fun s => Φ s ψ)
        (polydisc (0 : P → ℂ) (fun _ => Real.exp κ)))
    (hΦcont : ContinuousOn (fun q : (P → ℂ) × (I → ℝ) => Φ q.1 q.2)
      (polydisc (0 : P → ℂ) (fun _ => Real.exp κ) ×ˢ
        {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}))
    (hFluct : ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ),
      ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) → ∀ x,
        ‖Φ s ψ x - u x‖ ≤ B * (betaK d L k β0 ^ (-(1 / 2 : ℝ)) *
          pLog A₁ p (betaK d L k β0))) :
    AnalyticOnNhd ℂ (fun s => ∫ ψ in {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ},
      G (Φ s ψ) ∂γ) (polydisc (0 : P → ℂ) (fun _ => Real.exp κ)) ∧
    ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ),
      ‖∫ ψ in {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}, G (Φ s ψ) ∂γ‖ ≤
        B' * (γ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal := by
  exact retained_box_interaction_analytic_of_room hγ hG hGB u hBackground hΦan hΦcont
    hFluct (retained_room_of_half_budget hd hp hB hA hα₀ hc hα hβ0 hsize k hD)

end Balaban.Green
