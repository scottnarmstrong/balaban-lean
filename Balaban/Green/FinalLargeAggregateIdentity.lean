/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLargeAggregate

/-!
# Regrouping coverage labels at a fixed parent footprint

The coverage transform of the linked Mayer series is a finite sum. Regrouping it by the
coverage subset produces one coefficient per parent footprint and subset, namely the sum
over all connected clusters with that footprint and containing that subset of marks.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset MeasureTheory Balaban.Polymer

namespace Balaban.Green

/-- The fixed-parent coefficient is a sum over all connected clusters, not an individual
Mayer cluster. Every activating site of an elementary term lies in its charged footprint. -/
theorem linked_mayerK_eq_aggregated_coverage
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (act : T → B)
    (H : T → (∀ b, Ω b) → ℂ) (Z : Finset B)
    (hact : ∀ t, act t ∈ foot t)
    (hmeas : ∀ t, Measurable (H t)) (hbdd : ∀ t, Bdd (H t))
    (Y : NePoly B) :
    mayerK μ foot (fun t Φ => if act t ∈ Z then H t Φ else 0) Y =
      ∑ S ∈ Y.1.powerset,
        if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
          ∑ C ∈ (Cfam foot (fun _ : Finset T => True) Y.1).filter
            (fun C => S ⊆ C.image act),
            ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ) := by
  classical
  rw [linked_mayerK_eq_coverage_sum μ foot act H Z hmeas hbdd Y]
  have hmark : ∀ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
      C.image act ⊆ Y.1 := by
    intro C hC
    have h := linked_activation_subset_footprint foot act hact C
    simpa only [(mem_Cfam.mp hC).2.2] using h
  let w : Finset T → Finset B → ℂ := fun C S =>
    if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
      ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ)
  change (∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
      ∑ S ∈ (C.image act).powerset, w C S) = _
  calc
    ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
        ∑ S ∈ (C.image act).powerset, w C S
      = ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
          ∑ S ∈ Y.1.powerset,
            if S ⊆ C.image act then w C S else 0 := by
          apply Finset.sum_congr rfl
          intro C hC
          have hfilter : Y.1.powerset.filter (fun S => S ⊆ C.image act) =
              (C.image act).powerset := by
            ext S
            simp only [Finset.mem_filter, Finset.mem_powerset]
            exact ⟨fun h => h.2, fun h => ⟨h.trans (hmark C hC), h⟩⟩
          conv_rhs => rw [← Finset.sum_filter, hfilter]
    _ = ∑ S ∈ Y.1.powerset,
          ∑ C ∈ Cfam foot (fun _ : Finset T => True) Y.1,
            if S ⊆ C.image act then w C S else 0 := Finset.sum_comm
    _ = ∑ S ∈ Y.1.powerset,
          if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
            ∑ C ∈ (Cfam foot (fun _ : Finset T => True) Y.1).filter
              (fun C => S ⊆ C.image act),
              ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1)) ∂(Measure.pi μ) := by
          apply Finset.sum_congr rfl
          intro S _
          by_cases hSZ : Disjoint S Z
          · simp [w, hSZ]
          · simp only [w, hSZ, ↓reduceIte, ← Finset.sum_filter, Finset.mul_sum]

end Balaban.Green
