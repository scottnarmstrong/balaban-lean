/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupPi

/-!
# Splitting the coordinates of a finite product, with explicit coordinate formulas (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (2).  The regrouping `exists_regroup` of W912 hides
the coordinates that are not kept; the Gaussian integration needs them.  Here the coordinates of a finite
product `∀ i, α i` are split by one predicate (`exists_split1`), by three pairwise disjoint predicates
(`exists_split_three`), the three parts being relabelled along given equivalences and the rest kept as a
product over the remaining coordinates.  Every part is read off the coordinates by an explicit formula.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory

section Split

variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]

open Classical in
/-- **Splitting the coordinates of a product by one predicate**: the coordinates satisfying `Q`, relabelled
along `e`, and the others. -/
theorem exists_split1 (Q : ι → Prop) {β : Type} [Fintype β] (e : β ≃ {i // Q i}) :
    ∃ Ψ : (∀ i, α i) ≃ᵐ (∀ b : β, α (e b).1) × (∀ t : {i // ¬ Q i}, α t.1),
      MeasurePreserving Ψ (Measure.pi μ)
        ((Measure.pi fun b : β => μ (e b).1).prod (Measure.pi fun t : {i // ¬ Q i} => μ t.1)) ∧
      (∀ x b, (Ψ x).1 b = x (e b).1) ∧ (∀ x t, (Ψ x).2 t = x t.1) := by
  classical
  obtain ⟨Ψ1, h1, c1⟩ := exists_reindex_equiv e (β := fun b => α (e b).1)
    (γ := fun i : {i // Q i} => α i.1) (fun i => μ i.1) (fun b => μ (e b).1)
    (fun b => MeasurableEquiv.refl _) (fun b => MeasurePreserving.id _)
  refine ⟨(MeasurableEquiv.piEquivPiSubtypeProd α Q).trans
    (MeasurableEquiv.prodCongr Ψ1 (MeasurableEquiv.refl _)), ?_, ?_, ?_⟩
  · exact (h1.prod (MeasurePreserving.id _)).comp (measurePreserving_piEquivPiSubtypeProd μ Q)
  · intro x b
    exact c1 _ b
  · intro x t
    rfl

open Classical in
/-- **Splitting the coordinates of a product by three pairwise disjoint predicates** `Q₁, Q₂, Q₃`, the
three parts relabelled along `e₁, e₂, e₃`, and the remaining coordinates (satisfying none of them). -/
theorem exists_split_three (Q1 Q2 Q3 : ι → Prop) (h12 : ∀ i, Q2 i → ¬ Q1 i)
    (h13 : ∀ i, Q3 i → ¬ Q1 i) (h23 : ∀ i, Q3 i → ¬ Q2 i)
    {β1 β2 β3 : Type} [Fintype β1] [Fintype β2] [Fintype β3] (e1 : β1 ≃ {i // Q1 i})
    (e2 : β2 ≃ {i // Q2 i}) (e3 : β3 ≃ {i // Q3 i}) :
    ∃ Ψ : (∀ i, α i) ≃ᵐ (∀ b : β1, α (e1 b).1) × ((∀ b : β2, α (e2 b).1) ×
        ((∀ b : β3, α (e3 b).1) ×
          (∀ t : {t : {t : {i // ¬ Q1 i} // ¬ Q2 t.1} // ¬ Q3 t.1.1}, α t.1.1.1))),
      MeasurePreserving Ψ (Measure.pi μ)
        ((Measure.pi fun b : β1 => μ (e1 b).1).prod
          ((Measure.pi fun b : β2 => μ (e2 b).1).prod
            ((Measure.pi fun b : β3 => μ (e3 b).1).prod
              (Measure.pi fun t : {t : {t : {i // ¬ Q1 i} // ¬ Q2 t.1} // ¬ Q3 t.1.1} =>
                μ t.1.1.1)))) ∧
      (∀ x b, (Ψ x).1 b = x (e1 b).1) ∧ (∀ x b, (Ψ x).2.1 b = x (e2 b).1) ∧
      (∀ x b, (Ψ x).2.2.1 b = x (e3 b).1) ∧ (∀ x t, (Ψ x).2.2.2 t = x t.1.1.1) := by
  classical
  obtain ⟨Ψ1, hm1, c1, d1⟩ := exists_split1 μ Q1 e1
  let e2' : β2 ≃ {t : {i // ¬ Q1 i} // Q2 t.1} :=
    { toFun := fun b => ⟨⟨(e2 b).1, h12 _ (e2 b).2⟩, (e2 b).2⟩
      invFun := fun t => e2.symm ⟨t.1.1, t.2⟩
      left_inv := fun b => by simp
      right_inv := fun t => by simp }
  obtain ⟨Ψ2, hm2, c2, d2⟩ := exists_split1 (α := fun t : {i // ¬ Q1 i} => α t.1)
    (fun t => μ t.1) (fun t => Q2 t.1) e2'
  let e3' : β3 ≃ {t : {t : {i // ¬ Q1 i} // ¬ Q2 t.1} // Q3 t.1.1} :=
    { toFun := fun b => ⟨⟨⟨(e3 b).1, h13 _ (e3 b).2⟩, h23 _ (e3 b).2⟩, (e3 b).2⟩
      invFun := fun t => e3.symm ⟨t.1.1.1, t.2⟩
      left_inv := fun b => by simp
      right_inv := fun t => by simp }
  obtain ⟨Ψ3, hm3, c3, d3⟩ := exists_split1 (α := fun t : {t : {i // ¬ Q1 i} // ¬ Q2 t.1} => α t.1.1)
    (fun t => μ t.1.1) (fun t => Q3 t.1.1) e3'
  refine ⟨Ψ1.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (Ψ2.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) Ψ3))), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod hm3 |>.comp hm2)).comp hm1
  · intro x b
    exact c1 x b
  · intro x b
    exact (c2 (Ψ1 x).2 b).trans (d1 x _)
  · intro x b
    exact (c3 (Ψ2 (Ψ1 x).2).2 b).trans ((d2 (Ψ1 x).2 _).trans (d1 x _))
  · intro x t
    exact (d3 (Ψ2 (Ψ1 x).2).2 t).trans ((d2 (Ψ1 x).2 _).trans (d1 x _))

open Classical in
/-- **Splitting the coordinates of a product along core coordinates and two more predicates**: the
coordinates `κ s`, `s : Σ j, A j ⊕ B j` (injective, read through `e s : α (κ s) ≃ᵐ β s` as a family of
pairs; `Q₁` is the predicate of being such a coordinate), the coordinates satisfying `Q₂` and those
satisfying `Q₃` (relabelled along `e₂`, `e₃`; all three families pairwise disjoint), and the remaining
coordinates. -/
theorem exists_core_split_two {J : Type} [Fintype J] {A B : J → Type} [∀ j, Fintype (A j)]
    [∀ j, Fintype (B j)] (κ : (Σ j, A j ⊕ B j) → ι) (hκ : Function.Injective κ)
    {β : (Σ j, A j ⊕ B j) → Type} [∀ s, MeasurableSpace (β s)] (ν : ∀ s, Measure (β s))
    [∀ s, SigmaFinite (ν s)] (e : ∀ s, α (κ s) ≃ᵐ β s)
    (he : ∀ s, MeasurePreserving (e s) (μ (κ s)) (ν s)) (Q1 Q2 Q3 : ι → Prop)
    (hQ1 : ∀ i, Q1 i ↔ i ∈ Set.range κ)
    (h2 : ∀ s, ¬ Q2 (κ s)) (h3 : ∀ s, ¬ Q3 (κ s)) (h23 : ∀ i, Q3 i → ¬ Q2 i)
    {β2 β3 : Type} [Fintype β2] [Fintype β3] (e2 : β2 ≃ {i // Q2 i}) (e3 : β3 ≃ {i // Q3 i}) :
    ∃ Ψ : (∀ i, α i) ≃ᵐ
        (∀ j, (∀ a : A j, β ⟨j, Sum.inl a⟩) × (∀ b : B j, β ⟨j, Sum.inr b⟩)) ×
        ((∀ b : β2, α (e2 b).1) × ((∀ b : β3, α (e3 b).1) ×
          (∀ t : {t : {t : {i // ¬ Q1 i} // ¬ Q2 t.1} // ¬ Q3 t.1.1}, α t.1.1.1))),
      MeasurePreserving Ψ (Measure.pi μ)
        ((Measure.pi fun j => (Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
          (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)).prod
          ((Measure.pi fun b : β2 => μ (e2 b).1).prod
            ((Measure.pi fun b : β3 => μ (e3 b).1).prod
              (Measure.pi fun t : {t : {t : {i // ¬ Q1 i} // ¬ Q2 t.1} // ¬ Q3 t.1.1} =>
                μ t.1.1.1)))) ∧
      (∀ x j, (Ψ x).1 j = (fun a => e ⟨j, Sum.inl a⟩ (x (κ ⟨j, Sum.inl a⟩)),
        fun b => e ⟨j, Sum.inr b⟩ (x (κ ⟨j, Sum.inr b⟩)))) ∧
      (∀ x b, (Ψ x).2.1 b = x (e2 b).1) ∧ (∀ x b, (Ψ x).2.2.1 b = x (e3 b).1) ∧
      (∀ x t, (Ψ x).2.2.2 t = x t.1.1.1) := by
  classical
  let e1 : (Σ j, A j ⊕ B j) ≃ {i // Q1 i} :=
    (Equiv.ofInjective κ hκ).trans (Equiv.subtypeEquivRight fun i => (hQ1 i).symm)
  obtain ⟨Ψ, hm, c1, c2, c3, c4⟩ := exists_split_three μ Q1 Q2 Q3
    (fun i hi hr => by obtain ⟨s, rfl⟩ := (hQ1 _).mp hr; exact h2 s hi)
    (fun i hi hr => by obtain ⟨s, rfl⟩ := (hQ1 _).mp hr; exact h3 s hi) h23 e1 e2 e3
  obtain ⟨Ψd, hmd, cd⟩ := exists_decomp_equiv (G := Equiv.refl (Σ j, A j ⊕ B j))
    (γ := fun s => α (e1 s).1) (β := β) (fun s => μ (e1 s).1) ν (fun s => e s) (fun s => he s)
  have hmain := (hmd.prod (MeasurePreserving.id _)).comp hm
  refine ⟨Ψ.trans (MeasurableEquiv.prodCongr Ψd (MeasurableEquiv.refl _)), ?_, ?_, ?_, ?_, ?_⟩
  · exact hmain
  · intro x j
    refine (cd (Ψ x).1 j).trans ?_
    refine Prod.ext (funext fun a => ?_) (funext fun b => ?_)
    · show e _ ((Ψ x).1 _) = _
      rw [c1]
      rfl
    · show e _ ((Ψ x).1 _) = _
      rw [c1]
      rfl
  · intro x b
    exact c2 x b
  · intro x b
    exact c3 x b
  · intro x t
    exact c4 x t

end Split

section Assemble

variable {X1 X2 X3 a b c d e f g : Type} [MeasurableSpace X1] [MeasurableSpace X2]
  [MeasurableSpace X3] [MeasurableSpace a] [MeasurableSpace b] [MeasurableSpace c]
  [MeasurableSpace d] [MeasurableSpace e] [MeasurableSpace f] [MeasurableSpace g]
  {ν1 : Measure X1} {ν2 : Measure X2} {ν3 : Measure X3} {μa : Measure a} {μb : Measure b}
  {μc : Measure c} {μd : Measure d} {μe : Measure e} {μf : Measure f} {μg : Measure g}
  [SFinite ν1] [SFinite ν2] [SFinite ν3] [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd]
  [SFinite μe] [SFinite μf] [SFinite μg]

/-- **Assembling the regrouping from the regroupings of the three groups of variables** (outputs, internal
variables, inner outputs): the window group `(a, b, e)` is formed of the first coordinate of the outputs,
of their second one and of the second one of the internal variables; the core group `d` and the
remaining coordinates `(c, f, g)` are kept separate. -/
theorem exists_assemble (Ψo : X1 ≃ᵐ a × (b × c))
    (hΨo : MeasurePreserving Ψo ν1 (μa.prod (μb.prod μc)))
    (Ψx : X2 ≃ᵐ d × (e × f)) (hΨx : MeasurePreserving Ψx ν2 (μd.prod (μe.prod μf)))
    (Ψw : X3 ≃ᵐ g) (hΨw : MeasurePreserving Ψw ν3 μg) :
    ∃ Θ : X1 × (X2 × X3) ≃ᵐ (a × (b × e)) × (d × (c × (f × g))),
      MeasurePreserving Θ (ν1.prod (ν2.prod ν3))
        ((μa.prod (μb.prod μe)).prod (μd.prod (μc.prod (μf.prod μg)))) ∧
      ∀ ω, Θ ω = (((Ψo ω.1).1, ((Ψo ω.1).2.1, (Ψx ω.2.1).2.1)),
        ((Ψx ω.2.1).1, ((Ψo ω.1).2.2, ((Ψx ω.2.1).2.2, Ψw ω.2.2)))) := by
  obtain ⟨sh, hsh, csh⟩ := exists_shuffle7_equiv μa μb μc μd μe μf μg
  refine ⟨(MeasurableEquiv.prodCongr Ψo (MeasurableEquiv.prodCongr Ψx Ψw)).trans sh,
    hsh.comp (hΨo.prod (hΨx.prod hΨw)), fun ω => csh _⟩

end Assemble

end Balaban.LargeField
