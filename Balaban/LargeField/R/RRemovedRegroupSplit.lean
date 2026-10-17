/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupCore
public import Balaban.LargeField.R.RRemovedKernel

/-!
# The regrouping of the removed-outcome window integral: the outputs and the core split (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, step (2).  The outputs `ψ_k↾Z` of the pre-operator
are regrouped into `ψ_k↾Z₀` and the tree group (the blocks of `V₂` satisfying `P₂`, all inside
`Z ∖ Z₀`), the remaining outputs being integrated first; the internal variables are regrouped along an
injective family of core coordinates (`exists_coreRegroup`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Split3

variable {ι β1 β2 : Type} [Fintype ι] [Fintype β1] [Fintype β2] {E : Type} [MeasurableSpace E]
  (μ : Measure E) [SigmaFinite μ]

/-- **A three-way split of the coordinates of a product** `ι → E` by two disjoint predicates, the
first two parts read through relabellings `e₁ : β₁ ≃ {Q₁}`, `e₂ : β₂ ≃ {Q₂}`; the remaining
coordinates are the third factor. -/
theorem exists_split3 (Q1 Q2 : ι → Prop) (hQ : ∀ i, Q2 i → ¬ Q1 i) (e1 : β1 ≃ {i // Q1 i})
    (e2 : β2 ≃ {i // Q2 i}) :
    ∃ (L : Type) (_ : MeasurableSpace L) (μL : Measure L) (_ : SFinite μL)
      (Ψ : (ι → E) ≃ᵐ (β1 → E) × ((β2 → E) × L)),
      MeasurePreserving Ψ (Measure.pi fun _ : ι => μ)
        ((Measure.pi fun _ : β1 => μ).prod ((Measure.pi fun _ : β2 => μ).prod μL)) ∧
      (∀ x b, (Ψ x).1 b = x (e1 b).1) ∧ (∀ x b, (Ψ x).2.1 b = x (e2 b).1) := by
  classical
  let Q2' : {i // ¬ Q1 i} → Prop := fun i => Q2 i.1
  let e2' : β2 ≃ {i : {i // ¬ Q1 i} // Q2' i} :=
    { toFun := fun b => ⟨⟨(e2 b).1, hQ _ (e2 b).2⟩, (e2 b).2⟩
      invFun := fun x => e2.symm ⟨x.1.1, x.2⟩
      left_inv := fun b => by simp
      right_inv := fun x => by simp }
  obtain ⟨Ψ1, h1, c1⟩ := exists_reindex_equiv e1 (β := fun _ => E) (γ := fun _ : {i // Q1 i} => E)
    (fun _ => μ) (fun _ => μ) (fun _ => MeasurableEquiv.refl E) (fun _ => MeasurePreserving.id _)
  obtain ⟨Ψ2, h2, c2⟩ := exists_reindex_equiv e2' (β := fun _ => E)
    (γ := fun _ : {i : {i // ¬ Q1 i} // Q2' i} => E)
    (fun _ => μ) (fun _ => μ) (fun _ => MeasurableEquiv.refl E) (fun _ => MeasurePreserving.id _)
  let O1 := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) Q1
  let O2 := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {i // ¬ Q1 i} => E) Q2'
  let Ψ : (ι → E) ≃ᵐ (β1 → E) × ((β2 → E) × (∀ i : {i : {i // ¬ Q1 i} // ¬ Q2' i}, E)) :=
    O1.trans (MeasurableEquiv.prodCongr Ψ1 (O2.trans (MeasurableEquiv.prodCongr Ψ2
      (MeasurableEquiv.refl _))))
  refine ⟨∀ i : {i : {i // ¬ Q1 i} // ¬ Q2' i}, E, inferInstance,
    Measure.pi fun _ : {i : {i // ¬ Q1 i} // ¬ Q2' i} => μ, inferInstance, Ψ, ?_, ?_, ?_⟩
  · have hO1 := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) Q1
    have hO2 := measurePreserving_piEquivPiSubtypeProd (fun _ : {i // ¬ Q1 i} => μ) Q2'
    have hA := h2.prod (MeasurePreserving.id (Measure.pi fun _ : {i : {i // ¬ Q1 i} // ¬ Q2' i} => μ))
    have hB := h1.prod (hA.comp hO2)
    exact hB.comp hO1
  · intro x b
    exact c1 _ b
  · intro x b
    exact c2 _ b

end Split3

section Out

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))
  (V2 : Set (BlockAt S n M K k)) (P2 : BlockAt S n M K k → Prop)

/-- **The regrouping of the outputs `ψ_k↾Z`** into `ψ_k↾Z₀`, the tree group `(V₂, P₂)` and the
remaining outputs `L`; `Z₀ ⊆ Z` and the tree group lies in `Z ∖ Z₀` (`hZ0`, `hV2`, typing data).
The value of the first factor at a block of `Z₀` is the output at that block, the value of the second
at a block of the tree group is the output at that block. -/
theorem exists_outRegroup
    (hZ0 : ∀ y ∈ Vblk R a k, y ∈ Z0 → ZBlk a k y)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R a k ∧ ZBlk a k y ∧ y ∉ Z0) :
    ∃ (L : Type) (_ : MeasurableSpace L) (μL : Measure L) (_ : SFinite μL)
      (Ψ : OutZ N R a k ≃ᵐ OutZero N R a k Z0 × (OutPart N V2 P2 × L)),
      MeasurePreserving Ψ (outPartMeasure N (Vblk R a k) (ZBlk a k))
        ((outPartMeasure N (Vblk R a k) (· ∈ Z0)).prod ((outPartMeasure N V2 P2).prod μL)) ∧
      (∀ o (y : {y // y ∈ Vblk R a k ∧ y ∈ Z0}),
        (Ψ o).1 y = o ⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩) ∧
      (∀ o (y : {y // y ∈ V2 ∧ P2 y}),
        (Ψ o).2.1 y = o ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩) := by
  let e1 : {y // y ∈ Vblk R a k ∧ y ∈ Z0} ≃
      {i : {y // y ∈ Vblk R a k ∧ ZBlk a k y} // i.1 ∈ Z0} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩, y.2.2⟩
      invFun := fun i => ⟨i.1.1, i.1.2.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {y // y ∈ V2 ∧ P2 y} ≃
      {i : {y // y ∈ Vblk R a k ∧ ZBlk a k y} // i.1 ∈ V2 ∧ P2 i.1} :=
    { toFun := fun y => ⟨⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩, y.2⟩
      invFun := fun i => ⟨i.1.1, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨L, hL, μL, hμL, Ψ, h, c1, c2⟩ := exists_split3
    (ι := {y // y ∈ Vblk R a k ∧ ZBlk a k y}) (E := EuclideanSpace ℝ (Fin N)) volume
    (fun i => i.1 ∈ Z0) (fun i => i.1 ∈ V2 ∧ P2 i.1)
    (fun i hi h1 => (hV2 i.1 hi.1 hi.2).2.2 h1) e1 e2
  exact ⟨L, hL, μL, hμL, Ψ, h, c1, c2⟩

end Out

section Core

variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
  {J : Type} [Fintype J] {A B : J → Type} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]

/-- **The regrouping of a product along an injective family of core coordinates**: the coordinates
`κ s`, `s : Σ j, A j ⊕ B j`, are read through the measure preserving equivalences `e s` as a family of
pairs, the coordinates in the set `T` (disjoint from them) are kept, and the remaining coordinates
form the last factor. -/
theorem exists_coreRegroup (κ : (Σ j, A j ⊕ B j) → ι) (hκ : Function.Injective κ)
    {β : (Σ j, A j ⊕ B j) → Type} [∀ s, MeasurableSpace (β s)] (ν : ∀ s, Measure (β s))
    [∀ s, SigmaFinite (ν s)] (e : ∀ s, α (κ s) ≃ᵐ β s)
    (he : ∀ s, MeasurePreserving (e s) (μ (κ s)) (ν s)) (T : Set ι) [Fintype ↑T]
    (hT : ∀ s, κ s ∉ T) :
    ∃ (L : Type) (_ : MeasurableSpace L) (μL : Measure L) (_ : SFinite μL)
      (Ψ : (∀ i, α i) ≃ᵐ
        (∀ j, (∀ a : A j, β ⟨j, Sum.inl a⟩) × (∀ b : B j, β ⟨j, Sum.inr b⟩)) ×
          ((∀ t : ↥T, α t.1) × L)),
      MeasurePreserving Ψ (Measure.pi μ)
        ((Measure.pi fun j => (Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
          (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)).prod
          ((Measure.pi fun t : ↥T => μ t.1).prod μL)) ∧
      (∀ x j, (Ψ x).1 j = (fun a => e ⟨j, Sum.inl a⟩ (x (κ ⟨j, Sum.inl a⟩)),
        fun b => e ⟨j, Sum.inr b⟩ (x (κ ⟨j, Sum.inr b⟩)))) ∧
      (∀ x (t : ↥T), (Ψ x).2.1 t = x t.1) := by
  classical
  let Q : ι → Prop := fun i => i ∈ Set.range κ
  let _inst : Fintype {i // Q i} := Subtype.fintype Q
  let G : (Σ j, A j ⊕ B j) ≃ {i // Q i} := Equiv.ofInjective κ hκ
  obtain ⟨Ψ1, h1, c1⟩ := exists_decomp_equiv G (β := β) (γ := fun i : {i // Q i} => α i.1)
    (fun i => μ i.1) ν e he
  let Q2 : {i // ¬ Q i} → Prop := fun i => i.1 ∈ T
  let G2 : ↥T ≃ {i : {i // ¬ Q i} // Q2 i} :=
    { toFun := fun t => ⟨⟨t.1, fun ⟨s, hs⟩ => hT s (hs ▸ t.2)⟩, t.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨Ψ2, h2, c2⟩ := exists_reindex_equiv G2 (β := fun t : ↥T => α t.1)
    (γ := fun i : {i : {i // ¬ Q i} // Q2 i} => α i.1.1)
    (fun i => μ i.1.1) (fun t => μ t.1) (fun t => MeasurableEquiv.refl _)
    (fun t => MeasurePreserving.id _)
  let O1 := MeasurableEquiv.piEquivPiSubtypeProd α Q
  let O2 := MeasurableEquiv.piEquivPiSubtypeProd (fun i : {i // ¬ Q i} => α i.1) Q2
  let Ψ : (∀ i, α i) ≃ᵐ
      (∀ j, (∀ a : A j, β ⟨j, Sum.inl a⟩) × (∀ b : B j, β ⟨j, Sum.inr b⟩)) ×
        ((∀ t : ↥T, α t.1) × (∀ i : {i : {i // ¬ Q i} // ¬ Q2 i}, α i.1.1)) :=
    O1.trans (MeasurableEquiv.prodCongr Ψ1 (O2.trans (MeasurableEquiv.prodCongr Ψ2
      (MeasurableEquiv.refl _))))
  refine ⟨∀ i : {i : {i // ¬ Q i} // ¬ Q2 i}, α i.1.1, inferInstance,
    Measure.pi fun i : {i : {i // ¬ Q i} // ¬ Q2 i} => μ i.1.1, inferInstance, Ψ, ?_, ?_, ?_⟩
  · have hO1 := measurePreserving_piEquivPiSubtypeProd μ Q
    have hO2 := measurePreserving_piEquivPiSubtypeProd (fun i : {i // ¬ Q i} => μ i.1) Q2
    have hA := h2.prod (MeasurePreserving.id
      (Measure.pi fun i : {i : {i // ¬ Q i} // ¬ Q2 i} => μ i.1.1))
    have hB := h1.prod (hA.comp hO2)
    exact hB.comp hO1
  · intro x j
    exact c1 _ j
  · intro x t
    exact c2 _ t

end Core

section Regroup

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- A relabelling of the type of a variable value along an equality of the spin flags. -/
theorem exists_varVal_equiv (b b' : Bool) (hb : b = b') :
    ∃ e : VarVal N b ≃ᵐ VarVal N b', MeasurePreserving e (varMeasure N b) (varMeasure N b') ∧
      ∀ v, VarVal.toEuc (e v) = VarVal.toEuc v := by
  subst hb
  exact ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun _ => rfl⟩

/-- The value of a non-spin variable as a vector. -/
theorem exists_varVal_equiv_euc (b : Bool) (hb : b = false) :
    ∃ e : VarVal N b ≃ᵐ EuclideanSpace ℝ (Fin N),
      MeasurePreserving e (varMeasure N b) (volume : Measure (EuclideanSpace ℝ (Fin N))) ∧
      ∀ v, e v = VarVal.toEuc v := by
  subst hb
  exact ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun _ => rfl⟩

end Regroup

end Balaban.LargeField
