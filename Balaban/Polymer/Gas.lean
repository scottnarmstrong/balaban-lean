module

public import Balaban.Polymer.Decomposition

/-!
# The boundary-term lemma GAS

Heavy objects `Z` (blocks `zs Z`, core `cr Z ⊆ zs Z`, weight `τ Z`) and couplings `Y` (charged
support `cy Y`, value `β Y`).  The partition function
`Ξ = ∑_{Γ ⊆ 𝒵 pairwise disjoint} ∏_{Z ∈ Γ} τ Z · exp ∑_{Y meeting the core of Γ} β Y`
equals the partition function of the polymer gas whose polymers are the connected clusters
`(D, Γ₀)` of couplings and heavy objects (POLYMER.md §2.6, §3.9, `gas_eq`).  The coupling/heavy
contact relation is "the charged supports meet"; two heavy objects in one polymer never touch.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset

namespace Balaban.Polymer

section Gas

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  (cy : Yt → Finset B) (zs cr : Zt → Finset B) (β : Yt → ℂ) (τ : Zt → ℂ)

/-- The charged supports of the elementary objects: couplings on the left, heavy objects on the
right. -/
def gasCs : Yt ⊕ Zt → Finset B := Sum.elim cy zs

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
variable {cy zs} in
@[simp] theorem gasCs_inl (y : Yt) : gasCs cy zs (Sum.inl y) = cy y := rfl

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
variable {cy zs} in
@[simp] theorem gasCs_inr (z : Zt) : gasCs cy zs (Sum.inr z) = zs z := rfl

/-- The weights `e^{β Y} - 1` and `τ Z`. -/
def gasW : Yt ⊕ Zt → ℂ := Sum.elim (fun y => Complex.exp (β y) - 1) τ

/-- Admissible families: the heavy objects are pairwise disjoint and every coupling meets the core
of a heavy object of the family. -/
def gasA (D : Finset (Yt ⊕ Zt)) : Prop :=
  (∀ z ∈ D.toRight, ∀ z' ∈ D.toRight, z ≠ z' → Disjoint (zs z) (zs z')) ∧
    ∀ y ∈ D.toLeft, ∃ z ∈ D.toRight, ¬ Disjoint (cy y) (cr z)

/-- The partition function of GAS. -/
def gasXi : ℂ :=
  ∑ Γ ∈ Finset.univ.filter (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')),
    (∏ z ∈ Γ, τ z) * Complex.exp (∑ y ∈ Finset.univ.filter
      (fun y => ¬ Disjoint (cy y) (Γ.biUnion cr)), β y)

/-- The activity of the polymer `X`: the sum over connected admissible clusters with union `X`. -/
def gasK (X : NePoly B) : ℂ := polyAct (gasCs cy zs) (gasA cy zs cr) (gasW β τ) X

variable {cy zs cr}

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem gasA_loc (hcr : ∀ z, cr z ⊆ zs z) (D : Finset (Yt ⊕ Zt)) :
    gasA cy zs cr D ↔ ∀ t ∈ D, gasA cy zs cr (comp (gasCs cy zs) D t) := by
  constructor
  · rintro ⟨h1, h2⟩ t ht
    refine ⟨fun z hz z' hz' hne => ?_, fun y hy => ?_⟩
    · exact h1 z (toRight_subset_toRight (comp_subset D t) hz) z'
        (toRight_subset_toRight (comp_subset D t) hz') hne
    · rw [Finset.mem_toLeft] at hy
      have hyD : y ∈ D.toLeft := Finset.mem_toLeft.mpr (comp_subset D t hy)
      obtain ⟨z, hz, hnd⟩ := h2 y hyD
      refine ⟨z, Finset.mem_toRight.mpr ?_, hnd⟩
      refine comp_closed hy (Finset.mem_toRight.mp hz) ?_
      exact fun hd => hnd (Finset.disjoint_of_subset_right (hcr z) hd)
  · intro h
    refine ⟨fun z hz z' hz' hne => ?_, fun y hy => ?_⟩
    · by_contra hnd
      have hzD := Finset.mem_toRight.mp hz
      have hz'D := Finset.mem_toRight.mp hz'
      have hmem : (Sum.inr z' : Yt ⊕ Zt) ∈ comp (gasCs cy zs) D (Sum.inr z) :=
        comp_closed (self_mem_comp hzD) hz'D hnd
      exact (h _ hzD).1 z (Finset.mem_toRight.mpr (self_mem_comp hzD)) z'
        (Finset.mem_toRight.mpr hmem) hne |> fun hd => hnd hd
    · have hyD := Finset.mem_toLeft.mp hy
      obtain ⟨z, hz, hnd⟩ := (h _ hyD).2 y (Finset.mem_toLeft.mpr (self_mem_comp hyD))
      exact ⟨z, Finset.mem_toRight.mpr (comp_subset D _ (Finset.mem_toRight.mp hz)), hnd⟩

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
theorem gasA_nonempty (hz : ∀ z, (zs z).Nonempty)
    (D : Finset (Yt ⊕ Zt)) (hD : gasA cy zs cr D) : ∀ t ∈ D, (gasCs cy zs t).Nonempty := by
  intro t ht
  rcases t with y | z
  · obtain ⟨z, _, hnd⟩ := hD.2 y (Finset.mem_toLeft.mpr ht)
    exact (Finset.not_disjoint_iff.mp hnd).elim (fun b hb => ⟨b, hb.1⟩)
  · exact hz z

omit [Fintype Yt] [Fintype Zt] in
theorem prod_gasW (D : Finset (Yt ⊕ Zt)) :
    ∏ t ∈ D, gasW β τ t =
      (∏ y ∈ D.toLeft, (Complex.exp (β y) - 1)) * ∏ z ∈ D.toRight, τ z := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := D)]
  rw [Finset.prod_disjSum]
  rfl

/-- **GAS (identity)**: the partition function with non-small boundary terms is the partition
function of the polymer gas of connected clusters `(D, Γ₀)`. -/
theorem gas_eq (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z) :
    gasXi cy zs cr β τ =
      Xi (shareBlock (Subtype.val : NePoly B → Finset B)) (gasK cy zs cr β τ) := by
  have hdec := decomposition (cs := gasCs cy zs) (A := gasA cy zs cr)
    (fun D hD => gasA_nonempty hz D hD) (gasA_loc hcr) (gasW β τ)
  unfold gasK
  rw [← hdec]
  unfold gasXi
  set S : Finset (Finset Zt) := Finset.univ.filter
    (fun Γ : Finset Zt => ∀ z ∈ Γ, ∀ z' ∈ Γ, z ≠ z' → Disjoint (zs z) (zs z')) with hS
  set Ym : Finset Zt → Finset Yt := fun Γ => Finset.univ.filter
    (fun y => ¬ Disjoint (cy y) (Γ.biUnion cr)) with hYm
  have h1 : ∀ Γ : Finset Zt, (∏ z ∈ Γ, τ z) * Complex.exp (∑ y ∈ Ym Γ, β y) =
      ∑ Dy ∈ (Ym Γ).powerset, (∏ y ∈ Dy, (Complex.exp (β y) - 1)) * ∏ z ∈ Γ, τ z := by
    intro Γ
    rw [Complex.exp_sum, ← Finset.sum_mul]
    have : ∏ y ∈ Ym Γ, Complex.exp (β y) = ∏ y ∈ Ym Γ, (1 + (Complex.exp (β y) - 1)) :=
      Finset.prod_congr rfl (fun y _ => by ring)
    rw [this, Finset.prod_one_add, mul_comm]
  refine (Finset.sum_congr rfl (fun Γ _ => h1 Γ)).trans ?_
  rw [Finset.sum_sigma' S (fun Γ => (Ym Γ).powerset)
    (fun Γ Dy => (∏ y ∈ Dy, (Complex.exp (β y) - 1)) * ∏ z ∈ Γ, τ z)]
  symm
  refine Finset.sum_nbij' (fun D => (⟨D.toRight, D.toLeft⟩ : Σ _ : Finset Zt, Finset Yt))
    (fun x => x.2.disjSum x.1) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    have hA : gasA cy zs cr D := (Finset.mem_filter.mp hD).2
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA.1⟩, ?_⟩
    rw [Finset.mem_powerset]
    intro y hy
    obtain ⟨z, hz, hnd⟩ := hA.2 y hy
    simp only [hYm, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hd
    exact hnd (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem cr hz) hd)
  · rintro ⟨Γ, Dy⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hΓ, hDy⟩ := hx
    rw [Finset.mem_powerset] at hDy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa using (Finset.mem_filter.mp hΓ).2
    · intro y hy
      simp only [Finset.toLeft_disjSum] at hy
      have := hDy hy
      simp only [hYm, Finset.mem_filter, Finset.mem_univ, true_and] at this
      rw [Finset.disjoint_biUnion_right] at this
      push Not at this
      obtain ⟨z, hz, hnd⟩ := this
      exact ⟨z, by simpa using hz, hnd⟩
  · intro D _
    simp [Finset.toLeft_disjSum_toRight]
  · rintro ⟨Γ, Dy⟩ _
    simp
  · intro D _
    simp only []
    rw [prod_gasW]

end Gas

end Balaban.Polymer
