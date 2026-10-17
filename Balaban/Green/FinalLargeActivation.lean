/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLargeLinkedMayer
public import Mathlib.Data.Nat.Choose.Sum

/-!
# From all-sites activation to coverage activation

A linked cluster activated when all its marked sites are selected can be rewritten with fixed
coefficients activated by intersection. The new activation supports may be disconnected while
the cluster footprint is unchanged. The finite transform can multiply the label count by
`2^|A|`, which must be paid by the physical decay budget.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Green

/-- Every subset of `A` disjoint from `Z` is a subset of `A \ Z`, and conversely. -/
theorem powerset_filter_disjoint_eq_sdiff_powerset
    {B : Type*} [DecidableEq B] (A Z : Finset B) :
    A.powerset.filter (fun S => Disjoint S Z) = (A \ Z).powerset := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨hSA, hSZ⟩ b hb
    exact Finset.mem_sdiff.mpr ⟨hSA hb, Finset.disjoint_left.mp hSZ hb⟩
  · intro hS
    refine ⟨fun b hb => (Finset.mem_sdiff.mp (hS hb)).1, ?_⟩
    exact Finset.disjoint_left.mpr (fun b hbS hbZ =>
      (Finset.mem_sdiff.mp (hS hbS)).2 hbZ)

/-- The finite inclusion-exclusion identity converting `A ⊆ Z` to fixed coverage labels.
The empty activation set is excluded, as for every nonempty linked cluster. -/
theorem all_selected_eq_coverage_sum
    {B : Type*} [DecidableEq B] (A Z : Finset B) (hA : A.Nonempty) :
    (if A ⊆ Z then (1 : ℤ) else 0) =
      ∑ S ∈ A.powerset,
        if Disjoint S Z then 0 else (-1 : ℤ) ^ (S.card + 1) := by
  have hA0 : A ≠ ∅ := hA.ne_empty
  have htotal : (∑ S ∈ A.powerset, (-1 : ℤ) ^ S.card) = 0 := by
    rw [Finset.sum_powerset_neg_one_pow_card]
    simp [hA0]
  have hdis : (∑ S ∈ A.powerset,
      if Disjoint S Z then (-1 : ℤ) ^ S.card else 0) =
      if A \ Z = ∅ then 1 else 0 := by
    rw [← Finset.sum_filter]
    rw [powerset_filter_disjoint_eq_sdiff_powerset]
    exact Finset.sum_powerset_neg_one_pow_card
  have hpart : (∑ S ∈ A.powerset,
      if Disjoint S Z then 0 else (-1 : ℤ) ^ (S.card + 1)) =
      (∑ S ∈ A.powerset,
        if Disjoint S Z then (-1 : ℤ) ^ S.card else 0) -
      (∑ S ∈ A.powerset, (-1 : ℤ) ^ S.card) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases hSZ : Disjoint S Z
    · simp [hSZ]
    · simp [hSZ, pow_succ]
  rw [hpart, htotal, sub_zero, hdis]
  by_cases hAZ : A ⊆ Z
  · simp [hAZ, Finset.sdiff_eq_empty_iff_subset.mpr hAZ]
  · have hne : A \ Z ≠ ∅ := by
      intro he
      exact hAZ (Finset.sdiff_eq_empty_iff_subset.mp he)
    simp [hAZ, hne]

/-- The same transform applied to a fixed complex linked coefficient. Its signs have norm one,
so each new coverage coefficient has the original magnitude. -/
theorem all_selected_weight_eq_coverage_sum
    {B : Type*} [DecidableEq B] (A Z : Finset B) (hA : A.Nonempty) (w : ℂ) :
    (if A ⊆ Z then w else 0) =
      ∑ S ∈ A.powerset,
        if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) * w := by
  have hcast : (if A ⊆ Z then (1 : ℂ) else 0) =
      ∑ S ∈ A.powerset,
        if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) := by
    exact_mod_cast all_selected_eq_coverage_sum A Z hA
  calc
    (if A ⊆ Z then w else 0) = (if A ⊆ Z then (1 : ℂ) else 0) * w := by
      split_ifs <;> ring
    _ = (∑ S ∈ A.powerset,
          if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ)) * w := by
      rw [hcast]
    _ = ∑ S ∈ A.powerset,
          if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) * w := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S _
      split_ifs <;> ring

/-- The linked Mayer coefficient in the coverage-activation convention: each label is a
connected cluster `C` together with a subset `S` of its marked sites. The fixed coefficient
has the cluster's full footprint and a possibly disconnected activation support `S`. -/
theorem linked_mayerK_eq_coverage_sum
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, MeasureTheory.Measure (Ω b))
    [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (act : T → B)
    (H : T → (∀ b, Ω b) → ℂ) (Z : Finset B)
    (hmeas : ∀ t, Measurable (H t)) (hbdd : ∀ t, Balaban.Polymer.Bdd (H t))
    (Y : Balaban.Polymer.NePoly B) :
    Balaban.Polymer.mayerK μ foot (fun t Φ => if act t ∈ Z then H t Φ else 0) Y =
      ∑ C ∈ Balaban.Polymer.Cfam foot (fun _ : Finset T => True) Y.1,
        ∑ S ∈ (C.image act).powerset,
          if Disjoint S Z then 0 else ((-1 : ℤ) ^ (S.card + 1) : ℂ) *
            ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1))
              ∂(MeasureTheory.Measure.pi μ) := by
  rw [linked_mayerK_eq_sum_fixed μ foot act H Z hmeas hbdd Y]
  apply Finset.sum_congr rfl
  intro C hC
  have hCne : C.Nonempty := (Balaban.Polymer.mem_Cfam.mp hC).1.1
  have hA : (C.image act).Nonempty := by
    obtain ⟨t, ht⟩ := hCne
    exact ⟨act t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
  exact all_selected_weight_eq_coverage_sum (C.image act) Z hA _

/-- The finite inclusion-exclusion signs preserve the magnitude of each fixed linked
coefficient, so the individual footprint bound passes to coverage activation unchanged. -/
theorem coverage_cluster_coefficient_bound
    {B T : Type*} [Fintype B] [Fintype T]
    {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
    (μ : ∀ b, MeasureTheory.Measure (Ω b))
    [∀ b, MeasureTheory.IsProbabilityMeasure (μ b)]
    (foot : T → Finset B) (H : T → (∀ b, Ω b) → ℂ)
    (dist : Finset B → ℝ) {H0 κ0 κ1 c : ℝ}
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2)
    (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hdist : ∀ Y, 0 ≤ dist Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * dist (foot t)))
    (hG3 : ∀ C : Finset T, Balaban.Polymer.ConnSet foot C →
      dist (Balaban.Polymer.unionCs foot C) ≤
        ∑ t ∈ C, dist (foot t) + c * ((C.card : ℝ) - 1))
    (hsmall : 2 * H0 * Real.exp (κ1 * c) ≤ 1)
    (C : Finset T) (hC : Balaban.Polymer.ConnSet foot C) (S : Finset B) :
    ‖(((-1 : ℤ) ^ (S.card + 1) : ℂ) *
      ∫ Φ, (∏ t ∈ C, (Complex.exp (H t Φ) - 1))
        ∂(MeasureTheory.Measure.pi μ))‖ ≤
      Real.exp (-κ1 * dist (Balaban.Polymer.unionCs foot C)) := by
  have hsign : ‖(((-1 : ℤ) ^ (S.card + 1) : ℂ))‖ = 1 := by
    simp
  rw [norm_mul, hsign, one_mul]
  exact linked_cluster_integral_bound μ foot H dist hH0 hH0' hκ0 hκ1 hc
    hdist hH hG3 hsmall C hC

end Balaban.Green
