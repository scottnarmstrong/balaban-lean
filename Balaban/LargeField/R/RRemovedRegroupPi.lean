/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Balaban.LargeField.Operators.PiTools

/-!
# The regrouping of the removed-outcome window integral: measure preserving equivalences (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, step (2).  Generic measure-theoretic tools for the
regrouping `Θ`: relabelling the coordinates of a finite product along an equivalence of index sets
with a measure preserving equivalence on each coordinate (`exists_reindex_equiv`), regrouping the
coordinates indexed by `Σ j, A j ⊕ B j` as a family of pairs (`exists_decomp_equiv`), and the
rearrangement of seven factors of a product (`measurePreserving_shuffle7`).  Each statement names
the equivalence together with its values on the coordinates.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory

section Reindex

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- **Relabelling the coordinates of a finite product** along `G : κ ≃ ι`, with a measure
preserving equivalence `e j : γ (G j) ≃ᵐ β j` on each coordinate: a measure preserving measurable
equivalence whose `j`-th coordinate is `e j` of the `G j`-th coordinate. -/
theorem exists_reindex_equiv (G : κ ≃ ι) {β : κ → Type*} {γ : ι → Type*}
    [∀ j, MeasurableSpace (β j)] [∀ i, MeasurableSpace (γ i)]
    (μ : ∀ i, Measure (γ i)) [∀ i, SigmaFinite (μ i)] (ν : ∀ j, Measure (β j))
    [∀ j, SigmaFinite (ν j)] (e : ∀ j, γ (G j) ≃ᵐ β j)
    (he : ∀ j, MeasurePreserving (e j) (μ (G j)) (ν j)) :
    ∃ Ψ : (∀ i, γ i) ≃ᵐ (∀ j, β j), MeasurePreserving Ψ (Measure.pi μ) (Measure.pi ν) ∧
      ∀ x j, Ψ x j = e j (x (G j)) := by
  let Ψ' : (∀ j, β j) ≃ᵐ (∀ i, γ i) :=
    (MeasurableEquiv.piCongrRight fun j => (e j).symm).trans (MeasurableEquiv.piCongrLeft γ G)
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun j => (e j).symm)
      (Measure.pi ν) (Measure.pi fun j => μ (G j)) :=
    measurePreserving_pi ν (fun j => μ (G j)) (f := fun j => (e j).symm)
      (fun j => (he j).symm (e j))
  have h2 := measurePreserving_piCongrLeft μ G
  have h3 : MeasurePreserving Ψ' (Measure.pi ν) (Measure.pi μ) := h2.comp h1
  refine ⟨Ψ'.symm, h3.symm Ψ', fun x j => ?_⟩
  have hΨ : ∀ (y : ∀ j, β j) (j : κ), Ψ' y (G j) = (e j).symm (y j) := by
    intro y j
    show Equiv.piCongrLeft γ G (fun j => (e j).symm (y j)) (G j) = _
    exact Equiv.piCongrLeft_apply_apply (P := γ) G (fun j => (e j).symm (y j)) j
  have h5 := congrFun (Ψ'.apply_symm_apply x) (G j)
  rw [hΨ] at h5
  rw [← h5]
  simp

end Reindex


section Decomp

variable {J ι : Type*} [Fintype J] [Fintype ι] {A B : J → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)]

/-- **Regrouping the coordinates indexed by `Σ j, A j ⊕ B j` as a family of pairs**, with a measure
preserving equivalence on each coordinate. -/
theorem exists_decomp_equiv (G : (Σ j, A j ⊕ B j) ≃ ι) {β : (Σ j, A j ⊕ B j) → Type*}
    {γ : ι → Type*} [∀ s, MeasurableSpace (β s)] [∀ i, MeasurableSpace (γ i)]
    (μ : ∀ i, Measure (γ i)) [∀ i, SigmaFinite (μ i)] (ν : ∀ s, Measure (β s))
    [∀ s, SigmaFinite (ν s)] (e : ∀ s, γ (G s) ≃ᵐ β s)
    (he : ∀ s, MeasurePreserving (e s) (μ (G s)) (ν s)) :
    ∃ Ψ : (∀ i, γ i) ≃ᵐ (∀ j, (∀ a : A j, β ⟨j, Sum.inl a⟩) × (∀ b : B j, β ⟨j, Sum.inr b⟩)),
      MeasurePreserving Ψ (Measure.pi μ)
        (Measure.pi fun j => (Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
          (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)) ∧
      ∀ x j, Ψ x j = (fun a => e ⟨j, Sum.inl a⟩ (x (G ⟨j, Sum.inl a⟩)),
        fun b => e ⟨j, Sum.inr b⟩ (x (G ⟨j, Sum.inr b⟩))) := by
  obtain ⟨Ψ1, h1, c1⟩ := exists_reindex_equiv G μ ν e he
  have h2 := PiTools.measurePreserving_piCurry (κ := fun j => A j ⊕ B j)
    (fun (j : J) (t : A j ⊕ B j) => β ⟨j, t⟩) (fun j t => ν ⟨j, t⟩)
  have h3 : ∀ j, MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun t : A j ⊕ B j => β ⟨j, t⟩))
      (Measure.pi fun t : A j ⊕ B j => ν ⟨j, t⟩)
      ((Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
        (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)) := fun j =>
    measurePreserving_sumPiEquivProdPi fun t : A j ⊕ B j => ν ⟨j, t⟩
  have h4 := measurePreserving_pi (fun j => Measure.pi fun t : A j ⊕ B j => ν ⟨j, t⟩)
    (fun j => (Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
        (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)) (f := fun j =>
      (MeasurableEquiv.sumPiEquivProdPi (fun t : A j ⊕ B j => β ⟨j, t⟩))) h3
  let Ψ : (∀ i, γ i) ≃ᵐ (∀ j, (∀ a : A j, β ⟨j, Sum.inl a⟩) × (∀ b : B j, β ⟨j, Sum.inr b⟩)) :=
    (Ψ1.trans (MeasurableEquiv.piCurry (fun (j : J) (t : A j ⊕ B j) => β ⟨j, t⟩))).trans
      (MeasurableEquiv.piCongrRight fun j =>
        MeasurableEquiv.sumPiEquivProdPi (fun t : A j ⊕ B j => β ⟨j, t⟩))
  refine ⟨Ψ, h4.comp (h2.comp h1), fun x j => ?_⟩
  refine Prod.ext (funext fun a => ?_) (funext fun b => ?_)
  · exact c1 x ⟨j, Sum.inl a⟩
  · exact c1 x ⟨j, Sum.inr b⟩

end Decomp


section Shuffle

variable {a b c d e f g : Type*} [MeasurableSpace a] [MeasurableSpace b] [MeasurableSpace c]
  [MeasurableSpace d] [MeasurableSpace e] [MeasurableSpace f] [MeasurableSpace g]
  (μa : Measure a) (μb : Measure b) (μc : Measure c) (μd : Measure d) (μe : Measure e)
  (μf : Measure f) (μg : Measure g) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd]
  [SFinite μe] [SFinite μf] [SFinite μg]

/-- Exchange of the first two factors of a right nested product. -/
theorem measurePreserving_swap12 :
    MeasurePreserving (fun p : b × (c × d) => (p.2.1, (p.1, p.2.2)))
      (μb.prod (μc.prod μd)) (μc.prod (μb.prod μd)) := by
  have h1 := (measurePreserving_prodAssoc μb μc μd).symm
  have h2 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have h3 := measurePreserving_prodAssoc μc μb μd
  exact h3.comp (h2.comp h1)

/-- **Rearrangement of seven factors** of a product measure: the first, second and fifth factors
form the window group, the fourth stays alone, the third, sixth and seventh form the last group. -/
theorem measurePreserving_shuffle7 :
    MeasurePreserving
      (fun p : (a × (b × c)) × ((d × (e × f)) × g) =>
        ((p.1.1, (p.1.2.1, p.2.1.2.1)), (p.2.1.1, (p.1.2.2, (p.2.1.2.2, p.2.2)))))
      ((μa.prod (μb.prod μc)).prod ((μd.prod (μe.prod μf)).prod μg))
      ((μa.prod (μb.prod μe)).prod (μd.prod (μc.prod (μf.prod μg)))) := by
  -- right part: `(d × (e × f)) × g → d × (e × (f × g))`
  have hR1 := (measurePreserving_prodAssoc μd (μe.prod μf) μg)
  have hR2 := (MeasurePreserving.id μd).prod (measurePreserving_prodAssoc μe μf μg)
  have hR := (MeasurePreserving.id (μa.prod (μb.prod μc))).prod (hR2.comp hR1)
  -- left part: `(a × (b × c)) × Q → a × (b × (c × Q))`
  have hL1 := measurePreserving_prodAssoc μa (μb.prod μc) (μd.prod (μe.prod (μf.prod μg)))
  have hL2 := (MeasurePreserving.id μa).prod
    (measurePreserving_prodAssoc μb μc (μd.prod (μe.prod (μf.prod μg))))
  -- permutation `c × (d × (e × R)) → e × (d × (c × R))`
  have hP1 := measurePreserving_swap12 μc μd (μe.prod (μf.prod μg))
  have hP2 := (MeasurePreserving.id μd).prod (measurePreserving_swap12 μc μe (μf.prod μg))
  have hP3 := measurePreserving_swap12 μd μe (μc.prod (μf.prod μg))
  have hP := hP3.comp (hP2.comp hP1)
  have hM := (MeasurePreserving.id μa).prod ((MeasurePreserving.id μb).prod hP)
  -- back to the nested form
  have hB1 := (measurePreserving_prodAssoc μb μe (μd.prod (μc.prod (μf.prod μg)))).symm
  have hB2 := (MeasurePreserving.id μa).prod hB1
  have hB3 := (measurePreserving_prodAssoc μa (μb.prod μe) (μd.prod (μc.prod (μf.prod μg)))).symm
  exact hB3.comp (hB2.comp (hM.comp (hL2.comp (hL1.comp hR))))

/-- **The rearrangement of seven factors as a measurable equivalence** (see
`measurePreserving_shuffle7`). -/
theorem exists_shuffle7_equiv :
    ∃ sh : (a × (b × c)) × ((d × (e × f)) × g) ≃ᵐ (a × (b × e)) × (d × (c × (f × g))),
      MeasurePreserving sh
        ((μa.prod (μb.prod μc)).prod ((μd.prod (μe.prod μf)).prod μg))
        ((μa.prod (μb.prod μe)).prod (μd.prod (μc.prod (μf.prod μg)))) ∧
      ∀ p, sh p = ((p.1.1, (p.1.2.1, p.2.1.2.1)), (p.2.1.1, (p.1.2.2, (p.2.1.2.2, p.2.2)))) := by
  let sh : (a × (b × c)) × ((d × (e × f)) × g) ≃ᵐ (a × (b × e)) × (d × (c × (f × g))) :=
    { toFun := fun p => ((p.1.1, (p.1.2.1, p.2.1.2.1)), (p.2.1.1, (p.1.2.2, (p.2.1.2.2, p.2.2))))
      invFun := fun q => ((q.1.1, (q.1.2.1, q.2.2.1)), ((q.2.1, (q.1.2.2, q.2.2.2.1)), q.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      measurable_toFun := by
        show Measurable fun p : (a × (b × c)) × ((d × (e × f)) × g) =>
          ((p.1.1, (p.1.2.1, p.2.1.2.1)), (p.2.1.1, (p.1.2.2, (p.2.1.2.2, p.2.2))))
        fun_prop
      measurable_invFun := by
        show Measurable fun q : (a × (b × e)) × (d × (c × (f × g))) =>
          ((q.1.1, (q.1.2.1, q.2.2.1)), ((q.2.1, (q.1.2.2, q.2.2.2.1)), q.2.2.2.2))
        fun_prop }
  exact ⟨sh, measurePreserving_shuffle7 μa μb μc μd μe μf μg, fun _ => rfl⟩

end Shuffle

end Balaban.LargeField
