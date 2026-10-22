/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinked

/-!
# Connected decomposition of a linked gas

The activation set is contained in the charged footprint. This makes every activated
coupling touch the selected heavy cores, and makes activation local to components formed by
overlapping charged footprints. In the terms of `Gas.lean` the linked activation satisfies
the conditions (L) `gasLinkedActive_local` and (M) `gasLinkedActive_meets`, and `gasLinked_eq` is
the instance of `actGasXi_eq`.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Local

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {allRequired : Yt → Bool} {activation footprint : Yt → Finset B}
  {zs cr : Zt → Finset B}

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- Enlarging the selected heavy family preserves activation. -/
theorem gasLinkedActive_mono {Γ Γ' : Finset Zt} (hΓ : Γ ⊆ Γ') (y : Yt)
    (h : gasLinkedActive allRequired activation cr Γ y) :
    gasLinkedActive allRequired activation cr Γ' y := by
  have hc : Γ.biUnion cr ⊆ Γ'.biUnion cr :=
    Finset.biUnion_subset_biUnion_of_subset_left cr hΓ
  cases hm : allRequired y with
  | false =>
      simp only [gasLinkedActive, hm, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨b, hbA, hbC⟩ := Finset.not_disjoint_iff.mp h
      exact Finset.not_disjoint_iff.mpr ⟨b, hbA, hc hbC⟩
  | true =>
      simp only [gasLinkedActive, hm, ↓reduceIte] at h ⊢
      exact ⟨h.1, h.2.trans hc⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- An active coupling touches a heavy core through its charged footprint. -/
theorem gasLinkedActive_footprint_meets
    (hact : ∀ y, activation y ⊆ footprint y) (y : Yt) (Γ : Finset Zt)
    (h : gasLinkedActive allRequired activation cr Γ y) :
    ¬ Disjoint (footprint y) (Γ.biUnion cr) := by
  cases hm : allRequired y with
  | false =>
      simp only [gasLinkedActive, hm, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨b, hbA, hbC⟩ := Finset.not_disjoint_iff.mp h
      exact Finset.not_disjoint_iff.mpr ⟨b, hact y hbA, hbC⟩
  | true =>
      simp only [gasLinkedActive, hm, ↓reduceIte] at h
      obtain ⟨b, hbA⟩ := h.1
      exact Finset.not_disjoint_iff.mpr ⟨b, hact y hbA, h.2 hbA⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- A heavy object containing a required activation block belongs to the charged component
of the coupling. -/
theorem gasLinked_core_mem_comp (hact : ∀ y, activation y ⊆ footprint y)
    (hcr : ∀ z, cr z ⊆ zs z) {D : Finset (Yt ⊕ Zt)} {t : Yt ⊕ Zt}
    {y : Yt} (hy : Sum.inl y ∈ comp (gasCs footprint zs) D t)
    {b : B} (hbA : b ∈ activation y) {z : Zt}
    (hz : z ∈ D.toRight) (hbC : b ∈ cr z) :
    Sum.inr z ∈ comp (gasCs footprint zs) D t := by
  apply comp_closed hy (Finset.mem_toRight.mp hz)
  show ¬ Disjoint (gasCs footprint zs (Sum.inl y)) (gasCs footprint zs (Sum.inr z))
  exact Finset.not_disjoint_iff.mpr ⟨b, hact y hbA, hcr z hbC⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- Activation of a coupling in a family is already witnessed in the charged component
containing that coupling. -/
theorem gasLinkedActive_comp (hact : ∀ y, activation y ⊆ footprint y)
    (hcr : ∀ z, cr z ⊆ zs z) {D : Finset (Yt ⊕ Zt)} {t : Yt ⊕ Zt}
    {y : Yt} (hy : Sum.inl y ∈ comp (gasCs footprint zs) D t)
    (h : gasLinkedActive allRequired activation cr D.toRight y) :
    gasLinkedActive allRequired activation cr
      (comp (gasCs footprint zs) D t).toRight y := by
  cases hm : allRequired y with
  | false =>
      simp only [gasLinkedActive, hm, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨b, hbA, hbC⟩ := Finset.not_disjoint_iff.mp h
      obtain ⟨z, hz, hbcr⟩ := Finset.mem_biUnion.mp hbC
      have hzc := gasLinked_core_mem_comp hact hcr hy hbA hz hbcr
      exact Finset.not_disjoint_iff.mpr
        ⟨b, hbA, Finset.mem_biUnion.mpr ⟨z, Finset.mem_toRight.mpr hzc, hbcr⟩⟩
  | true =>
      simp only [gasLinkedActive, hm, ↓reduceIte] at h ⊢
      refine ⟨h.1, ?_⟩
      intro b hbA
      obtain ⟨z, hz, hbcr⟩ := Finset.mem_biUnion.mp (h.2 hbA)
      have hzc := gasLinked_core_mem_comp hact hcr hy hbA hz hbcr
      exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_toRight.mpr hzc, hbcr⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- (L): linked activation is decided by the heavy objects whose supports meet the charged
footprint. -/
theorem gasLinkedActive_local (hact : ∀ y, activation y ⊆ footprint y)
    (hcr : ∀ z, cr z ⊆ zs z) (y : Yt) (Γ : Finset Zt) :
    gasLinkedActive allRequired activation cr Γ y ↔
      gasLinkedActive allRequired activation cr
        (Γ.filter (fun z => ¬ Disjoint (footprint y) (zs z))) y := by
  have key : ∀ b ∈ activation y, b ∈ Γ.biUnion cr →
      b ∈ (Γ.filter (fun z => ¬ Disjoint (footprint y) (zs z))).biUnion cr := by
    intro b hbA hbC
    obtain ⟨z, hz, hbcr⟩ := Finset.mem_biUnion.mp hbC
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_filter.mpr ⟨hz,
      Finset.not_disjoint_iff.mpr ⟨b, hact y hbA, hcr z hbcr⟩⟩, hbcr⟩
  refine ⟨fun h => ?_, gasLinkedActive_mono (Finset.filter_subset _ _) y⟩
  cases hm : allRequired y with
  | false =>
      simp only [gasLinkedActive, hm, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨b, hbA, hbC⟩ := Finset.not_disjoint_iff.mp h
      exact Finset.not_disjoint_iff.mpr ⟨b, hbA, key b hbA hbC⟩
  | true =>
      simp only [gasLinkedActive, hm, ↓reduceIte] at h ⊢
      exact ⟨h.1, fun b hbA => key b hbA (h.2 hbA)⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- (M): an active linked coupling meets the support of a selected heavy object. -/
theorem gasLinkedActive_meets (hact : ∀ y, activation y ⊆ footprint y)
    (hcr : ∀ z, cr z ⊆ zs z) (y : Yt) (Γ : Finset Zt)
    (h : gasLinkedActive allRequired activation cr Γ y) :
    ∃ z ∈ Γ, ¬ Disjoint (footprint y) (zs z) := by
  obtain ⟨b, hbF, hbC⟩ := Finset.not_disjoint_iff.mp
    (gasLinkedActive_footprint_meets hact y Γ h)
  obtain ⟨z, hz, hbcr⟩ := Finset.mem_biUnion.mp hbC
  exact ⟨z, hz, Finset.not_disjoint_iff.mpr ⟨b, hbF, hcr z hbcr⟩⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- Linked admissibility is local to the connected components of overlapping charged
footprints. This is the input to the landed decomposition theorem. -/
theorem gasLinkedA_loc (hact : ∀ y, activation y ⊆ footprint y)
    (hcr : ∀ z, cr z ⊆ zs z) (D : Finset (Yt ⊕ Zt)) :
    gasLinkedA allRequired activation zs cr D ↔
      ∀ t ∈ D, gasLinkedA allRequired activation zs cr
        (comp (gasCs footprint zs) D t) :=
  actGasA_loc (act := fun y Γ => gasLinkedActive allRequired activation cr Γ y)
    (fun y Γ => gasLinkedActive_local hact hcr y Γ) D

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- Every elementary object in an admissible linked family has nonempty charged support. -/
theorem gasLinkedA_nonempty (hact : ∀ y, activation y ⊆ footprint y)
    (hz : ∀ z, (zs z).Nonempty) (D : Finset (Yt ⊕ Zt))
    (hD : gasLinkedA allRequired activation zs cr D) :
    ∀ t ∈ D, (gasCs footprint zs t).Nonempty := by
  intro t ht
  rcases t with y | z
  · have hmeet := gasLinkedActive_footprint_meets hact y D.toRight
      (hD.2 y (Finset.mem_toLeft.mpr ht))
    obtain ⟨b, hb, _⟩ := Finset.not_disjoint_iff.mp hmeet
    exact ⟨b, hb⟩
  · exact hz z

end Local

section Identity

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  (allRequired : Yt → Bool) (activation footprint : Yt → Finset B)
  (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ)

/-- The linked partition function is the polymer partition function of connected families
with overlapping charged footprints. -/
theorem gasLinked_eq (hact : ∀ y, activation y ⊆ footprint y)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z) :
    gasLinkedXi allRequired activation zs cr β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (gasLinkedK allRequired activation footprint zs cr β τ) :=
  actGasXi_eq (act := fun y Γ => gasLinkedActive allRequired activation cr Γ y) (cy := footprint)
    β τ hz (gasLinkedActive_local hact hcr) (gasLinkedActive_meets hact hcr)

/-- The landed gas identity is the intersection-mode specialization of the linked identity. -/
theorem gas_eq_of_gasLinked_eq (hz : ∀ z, (zs z).Nonempty)
    (hcr : ∀ z, cr z ⊆ zs z) :
    gasXi footprint zs cr β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B))
        (gasK footprint zs cr β τ) := by
  have h := gasLinked_eq (fun _ => false) footprint footprint zs cr β τ
    (fun _ => Finset.Subset.rfl) hz hcr
  have hk : gasLinkedK (fun _ => false) footprint footprint zs cr β τ =
      gasK footprint zs cr β τ :=
    funext (gasLinkedK_intersection_eq footprint zs cr β τ)
  rw [gasLinkedXi_intersection_eq, hk] at h
  exact h

end Identity

end Balaban.Polymer
