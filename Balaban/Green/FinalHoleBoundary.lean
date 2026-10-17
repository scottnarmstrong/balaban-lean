/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol (astra)
-/
module

public import Balaban.Polymer.Mayer

/-!
# Fixed coefficients in the last boundary subtraction

For a fixed family of local terms, the whole-volume sum splits into terms supported inside
the bad set, terms supported inside its complement, and crossing terms. The crossing
coefficients are the original coefficients and hence do not depend on the selected bad set.
This is the algebraic partition required by P7 (4.11); identifying its terms with the
physical covariance, determinant and background differences is a separate task.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Green

/-- Every nonempty fixed footprint is either entirely bad, entirely retained, or crosses
the two regions. The three sums use the same coefficient `H t`. -/
theorem finalBoundary_fixed_crossing_partition
    {B T : Type*} [Fintype B] [Fintype T]
    (foot : T → Finset B) (hfoot : ∀ t, (foot t).Nonempty)
    (H : T → ℂ) (Z : Finset B) :
    (∑ t : T, H t) =
      (∑ t ∈ Finset.univ.filter (fun t => foot t ⊆ Z), H t) +
      (∑ t ∈ Finset.univ.filter (fun t => Disjoint (foot t) Z), H t) +
      (∑ t ∈ Finset.univ.filter
        (fun t => ¬ foot t ⊆ Z ∧ ¬ Disjoint (foot t) Z), H t) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hZ : foot t ⊆ Z
  · have hne : ¬ Disjoint (foot t) Z := by
      intro hd
      obtain ⟨b, hb⟩ := hfoot t
      exact (Finset.disjoint_left.mp hd hb) (hZ hb)
    simp [hZ, hne]
  · by_cases hd : Disjoint (foot t) Z
    · simp [hZ, hd]
    · simp [hZ, hd]

/-- The selected boundary difference is exactly the crossing sum after terms wholly
inside the bad set have been assigned to the heavy operator. -/
theorem finalBoundary_difference_eq_crossing
    {B T : Type*} [Fintype B] [Fintype T]
    (foot : T → Finset B) (hfoot : ∀ t, (foot t).Nonempty)
    (H : T → ℂ) (Z : Finset B) :
    (∑ t : T, H t) -
      (∑ t ∈ Finset.univ.filter (fun t => foot t ⊆ Z), H t) -
      (∑ t ∈ Finset.univ.filter (fun t => Disjoint (foot t) Z), H t) =
      ∑ t ∈ Finset.univ.filter
        (fun t => ¬ foot t ⊆ Z ∧ ¬ Disjoint (foot t) Z), H t := by
  have h := finalBoundary_fixed_crossing_partition foot hfoot H Z
  calc
    _ = (∑ t ∈ Finset.univ.filter
      (fun t => ¬ foot t ⊆ Z ∧ ¬ Disjoint (foot t) Z), H t) := by
        rw [h]; abel

/-- The same identity for elementary field-dependent potentials. Each crossing term is
evaluated with the original fixed coefficient function, so its `DepOn`, analytic and bound
properties can be supplied before the bad set is selected. -/
theorem finalBoundary_potential_difference_eq_crossing
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} (foot : T → Finset B)
    (hfoot : ∀ t, (foot t).Nonempty)
    (H : T → (∀ b, Ω b) → ℂ) (Z : Finset B) (Φ : ∀ b, Ω b) :
    (∑ t : T, H t Φ) -
      (∑ t ∈ Finset.univ.filter (fun t => foot t ⊆ Z), H t Φ) -
      (∑ t ∈ Finset.univ.filter (fun t => Disjoint (foot t) Z), H t Φ) =
      ∑ t ∈ Finset.univ.filter
        (fun t => ¬ foot t ⊆ Z ∧ ¬ Disjoint (foot t) Z), H t Φ :=
  finalBoundary_difference_eq_crossing foot hfoot (fun t => H t Φ) Z

end Balaban.Green
