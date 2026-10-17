/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalInteractionCutoff
import Mathlib.Tactic.Linarith

/-!
# Bounded retained backgrounds at the last integral

The variational fixed-point equation, its massive resolvent estimate, and the restricted
covariance estimates remain named physical inputs. The results here deduce the value bound and
analyticity of the cutoff integral from these inputs and the landed parameter-integral theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Balaban.Analysis

namespace Balaban.Green

/-- A massive retained-data fixed point stays in the value ball determined by its bounded
forcing. The fixed-point equation and the two quantitative estimates are explicit inputs. -/
theorem retained_background_value_bound
    {E : Type*} [NormedAddCommGroup E] (u u0 : E)
    (G force : E → E) {μ a b δ : ℝ} (ha : a < μ)
    (hEq : u - u0 = G (force u))
    (hGreen : ∀ v, μ * ‖G v‖ ≤ ‖v‖)
    (hForce : ‖force u‖ ≤ a * ‖u - u0‖ + b * δ) :
    ‖u - u0‖ ≤ b * δ / (μ - a) := by
  have hden : 0 < μ - a := by linarith
  apply (le_div_iff₀ hden).2
  have h1 : μ * ‖u - u0‖ ≤ a * ‖u - u0‖ + b * δ := by
    calc
      μ * ‖u - u0‖ = μ * ‖G (force u)‖ := by rw [hEq]
      _ ≤ ‖force u‖ := hGreen _
      _ ≤ a * ‖u - u0‖ + b * δ := hForce
  nlinarith

variable {P I : Type*} [Fintype P] [Fintype I]

omit [Fintype P] [Fintype I] in
/-- A bounded retained background plus a uniformly bounded complex fluctuation stays in the
open analytic polydisc. This is the value clause; the other `XiCData` clauses remain separate. -/
theorem retained_field_mem_polydisc
    (u : I → ℂ) (Φ : (P → ℂ) → (I → ℝ) → I → ℂ)
    {D T R κ ρ : ℝ}
    (hBackground : ∀ x, ‖u x‖ ≤ D)
    (hFluct : ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ),
      ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) → ∀ x, ‖Φ s ψ x - u x‖ ≤ T)
    (hRoom : D + T < R)
    (s : P → ℂ) (hs : s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ))
    (ψ : I → ℝ) (hψ : ∀ y, |ψ y| ≤ ρ) :
    Φ s ψ ∈ polydisc (0 : I → ℂ) (fun _ => R) := by
  intro x
  simp only [Pi.zero_apply, sub_zero]
  have htri : ‖Φ s ψ x‖ ≤ ‖Φ s ψ x - u x‖ + ‖u x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (Φ s ψ x - u x) (u x)
  exact lt_of_le_of_lt (htri.trans (add_le_add (hFluct s hs ψ hψ x) (hBackground x)))
    (by linarith)

/-- Analyticity of the small-field cutoff integral under the per-hole retained chart and
restricted covariance estimates. The cutoff uses only real bounded variables; no large-field
variable appears in the analytic integrand. -/
theorem retained_box_interaction_analytic_of_room
    {γ : Measure (I → ℝ)} {ρ R B' κ D T : ℝ}
    (hγ : γ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {G : (I → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G (polydisc (0 : I → ℂ) (fun _ => R)))
    (hGB : ∀ w ∈ polydisc (0 : I → ℂ) (fun _ => R), ‖G w‖ ≤ B')
    (u : I → ℂ) (hBackground : ∀ x, ‖u x‖ ≤ D)
    {Φ : (P → ℂ) → (I → ℝ) → (I → ℂ)}
    (hΦan : ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) →
      AnalyticOnNhd ℂ (fun s => Φ s ψ) (polydisc (0 : P → ℂ) (fun _ => Real.exp κ)))
    (hΦcont : ContinuousOn (fun q : (P → ℂ) × (I → ℝ) => Φ q.1 q.2)
      (polydisc (0 : P → ℂ) (fun _ => Real.exp κ) ×ˢ
        {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}))
    (hFluct : ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ),
      ∀ ψ : I → ℝ, (∀ y, |ψ y| ≤ ρ) → ∀ x, ‖Φ s ψ x - u x‖ ≤ T)
    (hRoom : D + T < R) :
    AnalyticOnNhd ℂ (fun s => ∫ ψ in {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ},
        G (Φ s ψ) ∂γ) (polydisc (0 : P → ℂ) (fun _ => Real.exp κ)) ∧
    ∀ s ∈ polydisc (0 : P → ℂ) (fun _ => Real.exp κ),
      ‖∫ ψ in {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}, G (Φ s ψ) ∂γ‖ ≤
        B' * (γ {ψ : I → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal := by
  apply analyticOnNhd_integral_box hγ hG hGB hΦan hΦcont
  intro s hs ψ hψ
  exact retained_field_mem_polydisc u Φ hBackground hFluct hRoom s hs ψ hψ

end Balaban.Green
