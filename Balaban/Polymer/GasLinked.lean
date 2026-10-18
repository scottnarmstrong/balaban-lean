/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasCore

/-!
# A gas with separate activation and charged footprint

A coupling has an activation set of bad blocks and a charged footprint. In all-required mode
the coupling is active when every block of its nonempty activation set belongs to the union of
selected heavy cores. In intersection mode it is active when its activation set meets that union.
The latter mode recovers the landed gas when activation equals footprint.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Linked

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]

/-- Activation of a coupling: all of the nonempty activation set is bad in all-required mode;
in intersection mode at least one activation block is bad. The bad set is the union of the
cores of the selected heavy objects. -/
def gasLinkedActive (allRequired : Yt → Bool) (activation : Yt → Finset B)
    (cr : Zt → Finset B) (Γ : Finset Zt) (y : Yt) : Prop :=
  if allRequired y then (activation y).Nonempty ∧ activation y ⊆ Γ.biUnion cr
  else ¬ Disjoint (activation y) (Γ.biUnion cr)

/-- Admissible linked families have disjoint heavy supports, and each chosen coupling is
activated by the heavy objects of the same family. -/
def gasLinkedA (allRequired : Yt → Bool) (activation : Yt → Finset B)
    (zs cr : Zt → Finset B) (D : Finset (Yt ⊕ Zt)) : Prop :=
  (∀ z ∈ D.toRight, ∀ z' ∈ D.toRight, z ≠ z' → Disjoint (zs z) (zs z')) ∧
    ∀ y ∈ D.toLeft, gasLinkedActive allRequired activation cr D.toRight y

/-- A linked coupling has weight exp (β y) - 1, and a heavy object has weight τ z. -/
def gasLinkedW (β : Yt → ℂ) (τ : Zt → ℂ) : Yt ⊕ Zt → ℂ :=
  gasW β τ

/-- The linked partition function sums compatible heavy families; every activated coupling
contributes its exponential boundary factor. -/
def gasLinkedXi (allRequired : Yt → Bool) (activation : Yt → Finset B)
    (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ) : ℂ :=
  ∑ Γ ∈ Finset.univ.filter
      (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
    (∏ z ∈ Γ, τ z) *
      Complex.exp (∑ y ∈ Finset.univ.filter
        (gasLinkedActive allRequired activation cr Γ), β y)

/-- The linked polymer activity is the sum over connected admissible families whose union of
charged footprints and heavy supports is the polymer. -/
def gasLinkedK (allRequired : Yt → Bool) (activation footprint : Yt → Finset B)
    (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ)
    (X : NePoly B) : ℂ :=
  polyAct (gasCs footprint zs) (gasLinkedA allRequired activation zs cr)
    (gasLinkedW β τ) X

omit [Fintype Yt] [Fintype Zt] in
/-- The new weight is the landed elementary weight. -/
theorem gasLinkedW_eq_gasW (β : Yt → ℂ) (τ : Zt → ℂ) :
    gasLinkedW β τ = gasW β τ := rfl

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- Intersection activation with the charged footprint is the landed activation rule. -/
theorem gasLinkedActive_intersection_eq (footprint : Yt → Finset B)
    (cr : Zt → Finset B) (Γ : Finset Zt) (y : Yt) :
    gasLinkedActive (fun _ => false) footprint cr Γ y ↔
      ¬ Disjoint (footprint y) (Γ.biUnion cr) := by
  simp [gasLinkedActive]

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- With intersection activation equal to the footprint, admissibility is the landed one. -/
theorem gasLinkedA_intersection_eq (footprint : Yt → Finset B)
    (zs cr : Zt → Finset B) (D : Finset (Yt ⊕ Zt)) :
    gasLinkedA (fun _ => false) footprint zs cr D ↔ gasA footprint zs cr D := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro y hy
    have h := h2 y hy
    simp only [gasLinkedActive, Bool.false_eq_true, ↓reduceIte] at h
    rw [Finset.disjoint_biUnion_right] at h
    push Not at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro y hy
    obtain ⟨z, hz, hnd⟩ := h2 y hy
    simp only [gasLinkedActive, Bool.false_eq_true, ↓reduceIte]
    intro hd
    exact hnd (Finset.disjoint_of_subset_right
      (Finset.subset_biUnion_of_mem cr hz) hd)

omit [Fintype B] in
/-- The landed partition function is the intersection-mode specialization. -/
theorem gasLinkedXi_intersection_eq (footprint : Yt → Finset B)
    (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ) :
    gasLinkedXi (fun _ => false) footprint zs cr β τ = gasXi footprint zs cr β τ := by
  unfold gasLinkedXi gasXi
  apply Finset.sum_congr rfl
  intro Γ _
  have hfilter : Finset.univ.filter
      (gasLinkedActive (fun _ => false) footprint cr Γ) =
      Finset.univ.filter (fun y => ¬ Disjoint (footprint y) (Γ.biUnion cr)) := by
    ext y
    simp [gasLinkedActive]
  rw [hfilter]

omit [Fintype B] in
/-- The landed polymer activity is the intersection-mode specialization. -/
theorem gasLinkedK_intersection_eq (footprint : Yt → Finset B)
    (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ) (X : NePoly B) :
    gasLinkedK (fun _ => false) footprint footprint zs cr β τ X =
      gasK footprint zs cr β τ X := by
  have hA : gasLinkedA (fun _ => false) footprint zs cr = gasA footprint zs cr :=
    funext (fun D => propext (gasLinkedA_intersection_eq footprint zs cr D))
  simp only [gasLinkedK, gasK, gasLinkedW_eq_gasW, hA]

omit [Fintype B] in
/-- The activation of the separated endpoints in the three-block example requires both
endpoints to be bad. Its charged footprint can include the intervening block. -/
theorem gasLinkedActive_pair_iff (a c : B) (Γ : Finset B) :
    gasLinkedActive (fun _ : Unit => true) (fun _ => ({a, c} : Finset B))
      (fun z => ({z} : Finset B)) Γ () ↔ a ∈ Γ ∧ c ∈ Γ := by
  simp [gasLinkedActive, Finset.insert_subset_iff]

end Linked

end Balaban.Polymer
