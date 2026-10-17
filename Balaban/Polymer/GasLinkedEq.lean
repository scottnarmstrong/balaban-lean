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
overlapping charged footprints.
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
/-- Linked admissibility is local to the connected components of overlapping charged
footprints. This is the input to the landed decomposition theorem. -/
theorem gasLinkedA_loc (hact : ∀ y, activation y ⊆ footprint y)
    (hcr : ∀ z, cr z ⊆ zs z) (D : Finset (Yt ⊕ Zt)) :
    gasLinkedA allRequired activation zs cr D ↔
      ∀ t ∈ D, gasLinkedA allRequired activation zs cr
        (comp (gasCs footprint zs) D t) := by
  constructor
  · rintro ⟨hheavy, hactive⟩ t ht
    refine ⟨fun z hz z' hz' hne => ?_, fun y hy => ?_⟩
    · exact hheavy z (toRight_subset_toRight (comp_subset D t) hz)
        z' (toRight_subset_toRight (comp_subset D t) hz') hne
    · have hyD : y ∈ D.toLeft :=
        Finset.mem_toLeft.mpr (comp_subset D t (Finset.mem_toLeft.mp hy))
      exact gasLinkedActive_comp hact hcr (Finset.mem_toLeft.mp hy) (hactive y hyD)
  · intro h
    refine ⟨fun z hz z' hz' hne => ?_, fun y hy => ?_⟩
    · by_contra hnd
      have hzD := Finset.mem_toRight.mp hz
      have hz'D := Finset.mem_toRight.mp hz'
      have hmem : (Sum.inr z' : Yt ⊕ Zt) ∈ comp (gasCs footprint zs) D (Sum.inr z) :=
        comp_closed (self_mem_comp hzD) hz'D hnd
      exact hnd ((h _ hzD).1 z (Finset.mem_toRight.mpr (self_mem_comp hzD))
        z' (Finset.mem_toRight.mpr hmem) hne)
    · have hyD := Finset.mem_toLeft.mp hy
      have hloc := (h _ hyD).2 y (Finset.mem_toLeft.mpr (self_mem_comp hyD))
      exact gasLinkedActive_mono (toRight_subset_toRight (comp_subset D _) ) y hloc

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
        (gasLinkedK allRequired activation footprint zs cr β τ) := by
  have hdec := decomposition (cs := gasCs footprint zs)
    (A := gasLinkedA allRequired activation zs cr)
    (fun D hD => gasLinkedA_nonempty hact hz D hD)
    (gasLinkedA_loc hact hcr) (gasLinkedW β τ)
  unfold gasLinkedK
  rw [← hdec]
  unfold gasLinkedXi
  set S : Finset (Finset Zt) := Finset.univ.filter
    (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) with hS
  set Ym : Finset Zt → Finset Yt := fun Γ => Finset.univ.filter
    (gasLinkedActive allRequired activation cr Γ) with hYm
  have h1 : ∀ Γ : Finset Zt, (∏ z ∈ Γ, τ z) * Complex.exp (∑ y ∈ Ym Γ, β y) =
      ∑ Dy ∈ (Ym Γ).powerset, (∏ y ∈ Dy, (Complex.exp (β y) - 1)) * ∏ z ∈ Γ, τ z := by
    intro Γ
    rw [Complex.exp_sum, ← Finset.sum_mul]
    have he : ∏ y ∈ Ym Γ, Complex.exp (β y) =
        ∏ y ∈ Ym Γ, (1 + (Complex.exp (β y) - 1)) :=
      Finset.prod_congr rfl (fun y _ => by ring)
    rw [he, Finset.prod_one_add, mul_comm]
  refine (Finset.sum_congr rfl (fun Γ _ => h1 Γ)).trans ?_
  rw [Finset.sum_sigma' S (fun Γ => (Ym Γ).powerset)
    (fun Γ Dy => (∏ y ∈ Dy, (Complex.exp (β y) - 1)) * ∏ z ∈ Γ, τ z)]
  symm
  refine Finset.sum_nbij' (fun D => (⟨D.toRight, D.toLeft⟩ : Σ _ : Finset Zt, Finset Yt))
    (fun x => x.2.disjSum x.1) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    have hA : gasLinkedA allRequired activation zs cr D := (Finset.mem_filter.mp hD).2
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.1⟩, ?_⟩
    rw [Finset.mem_powerset]
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.2 y hy⟩
  · rintro ⟨Γ, Dy⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hΓ, hDy⟩ := hx
    rw [Finset.mem_powerset] at hDy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa using (Finset.mem_filter.mp hΓ).2
    · intro y hy
      simp only [Finset.toLeft_disjSum] at hy
      simpa only [Finset.toRight_disjSum] using (Finset.mem_filter.mp (hDy hy)).2
  · intro D _
    simp [Finset.toLeft_disjSum_toRight]
  · rintro ⟨Γ, Dy⟩ _
    simp
  · intro D _
    simp only [gasLinkedW_eq_gasW]
    rw [prod_gasW]

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
