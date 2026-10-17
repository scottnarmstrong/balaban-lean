/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedCore

/-!
# The three-block linked bridge

The linked term of the three-block example requires two separated bad blocks a and c.
Its footprint includes the retained intervening block b, so the coupling meets both heavy
objects in the connected-family expansion.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Toy

variable {B : Type*} [Fintype B]

/-- One linked coupling is present exactly when both endpoint blocks are selected as bad. -/
theorem gasLinkedXi_pair (a c : B) (κ : ℂ) (τ : B → ℂ) :
    gasLinkedXi (fun _ : Unit => true) (fun _ => ({a, c} : Finset B))
      (fun z => ({z} : Finset B)) (fun z => ({z} : Finset B))
      (fun _ => κ) τ =
    ∑ Γ : Finset B, (∏ z ∈ Γ, τ z) *
      (if a ∈ Γ ∧ c ∈ Γ then Complex.exp κ else 1) := by
  unfold gasLinkedXi
  have hcompat : ∀ Γ : Finset B,
      (∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' →
        Disjoint ({z} : Finset B) ({z'} : Finset B)) := by
    intro Γ z _ z' _ hne
    exact Finset.disjoint_singleton.mpr hne
  simp only [Finset.filter_true_of_mem (fun Γ _ => hcompat Γ)]
  apply Finset.sum_congr rfl
  intro Γ _
  have hfilter : Finset.univ.filter
      (gasLinkedActive (fun _ : Unit => true) (fun _ => ({a, c} : Finset B))
        (fun z => ({z} : Finset B)) Γ) =
      if a ∈ Γ ∧ c ∈ Γ then ({()} : Finset Unit) else ∅ := by
    ext y
    cases y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      gasLinkedActive_pair_iff]
    split_ifs <;> simp_all
  rw [hfilter]
  by_cases h : a ∈ Γ ∧ c ∈ Γ
  · simp [h]
  · simp [h]

omit [Fintype B] in
/-- The footprint of the endpoint coupling and its two heavy objects is the three-block set. -/
theorem gasLinked_three_union (a b c : B) :
    unionCs (gasCs (fun _ : Unit => ({a, b, c} : Finset B))
      (fun z => ({z} : Finset B)))
      ({Sum.inl (), Sum.inr a, Sum.inr c} : Finset (Unit ⊕ B)) =
        ({a, b, c} : Finset B) := by
  simp [unionCs, gasCs]

omit [Fintype B] in
/-- The two endpoint heavy objects activate the linked coupling. -/
theorem gasLinked_three_admissible (a c : B) :
    gasLinkedA (fun _ : Unit => true) (fun _ => ({a, c} : Finset B))
      (fun z => ({z} : Finset B)) (fun z => ({z} : Finset B))
      ({Sum.inl (), Sum.inr a, Sum.inr c} : Finset (Unit ⊕ B)) := by
  simp [gasLinkedA, gasLinkedActive]

omit [Fintype B] in
/-- The linked coupling joins its two heavy endpoints into one connected elementary family,
whose charged union contains the retained middle block. -/
theorem gasLinked_three_connected (a b c : B) :
    ConnSet (gasCs (fun _ : Unit => ({a, b, c} : Finset B))
      (fun z => ({z} : Finset B)))
      ({Sum.inl (), Sum.inr a, Sum.inr c} : Finset (Unit ⊕ B)) := by
  let cs : Unit ⊕ B → Finset B :=
    gasCs (fun _ : Unit => ({a, b, c} : Finset B))
      (fun z => ({z} : Finset B))
  let D : Finset (Unit ⊕ B) := {Sum.inl (), Sum.inr a, Sum.inr c}
  change ConnSet cs D
  have hy : (Sum.inl () : Unit ⊕ B) ∈ D := by simp [D]
  have ha : Sum.inr a ∈ D := by simp [D]
  have hc : Sum.inr c ∈ D := by simp [D]
  have hya : Reach cs D (Sum.inl ()) (Sum.inr a) :=
    Reach.single cs hy ha (Finset.not_disjoint_iff.mpr
      ⟨a, by simp [cs, gasCs], by simp [cs, gasCs]⟩)
  have hyc : Reach cs D (Sum.inl ()) (Sum.inr c) :=
    Reach.single cs hy hc (Finset.not_disjoint_iff.mpr
      ⟨c, by simp [cs, gasCs], by simp [cs, gasCs]⟩)
  refine ⟨⟨Sum.inl (), hy⟩, ?_⟩
  intro s hs s' hs'
  simp only [D, Finset.mem_insert, Finset.mem_singleton] at hs hs'
  rcases hs with rfl | rfl | rfl <;> rcases hs' with rfl | rfl | rfl
  all_goals
    first
    | exact Reach.refl cs D _
    | exact hya
    | exact hyc
    | exact hya.symm
    | exact hyc.symm
    | exact hya.symm.trans cs hyc
    | exact hyc.symm.trans cs hya

/-- The endpoint bridge is one connected admissible family contributing to the polymer
whose footprint is the three-block set. -/
theorem gasLinked_three_mem_Cfam (a b c : B) :
    ({Sum.inl (), Sum.inr a, Sum.inr c} : Finset (Unit ⊕ B)) ∈
      Cfam (gasCs (fun _ : Unit => ({a, b, c} : Finset B))
        (fun z => ({z} : Finset B)))
        (gasLinkedA (fun _ : Unit => true)
          (fun _ => ({a, c} : Finset B))
          (fun z => ({z} : Finset B)) (fun z => ({z} : Finset B)))
        ({a, b, c} : Finset B) := by
  exact mem_Cfam.mpr ⟨gasLinked_three_connected a b c,
    gasLinked_three_admissible a c, gasLinked_three_union a b c⟩

end Toy

end Balaban.Polymer
