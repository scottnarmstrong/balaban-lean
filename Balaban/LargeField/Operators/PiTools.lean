module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product-measure tools for the composition of bounds (Lemma II.5.13)

* `lintegral_fintype_prod_eq_prod`: the `ℝ≥0∞` version of Fubini for a product of functions of
  independent coordinates;
* `lintegral_split`: splitting the coordinates of a finite product by a predicate;
* `measurePreserving_piCurry`, `measurePreserving_fibreMap`: regrouping the coordinates of a
  finite product along a colouring, and `lintegral_prod_fibres`;
* `measurePreserving_reindex`: relabelling the coordinates along an equivalence, with a
  measure-preserving map on each coordinate;
* `measurePreserving_decompMap`: regrouping the coordinates along an equivalence with
  `Σ j, A j ⊕ B j` as a family of pairs of configurations.
-/

@[expose] public section

namespace Balaban.LargeField.PiTools

open MeasureTheory ENNReal

universe u v

/-- The `ℝ≥0∞` version of Fubini for a product of functions of independent coordinates. -/
theorem lintegral_fintype_prod_eq_prod (ι : Type u) [Fintype ι] : ∀ {E : ι → Type v}
    [∀ i, MeasurableSpace (E i)] {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : ι) → E i → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {E : ι → Type v}
      [∀ i, MeasurableSpace (E i)] {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
      (f : (i : ι) → E i → ℝ≥0∞) (_ : ∀ i, Measurable (f i)),
      ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i)) ?_ ?_ ?_ ι
  · intro α β _ e ih E mE μ _ f hf
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (E := fun a => E (e a)) (μ := fun a => μ (e a)) (fun a => f (e a))
      (fun a => hf _)
    rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [h]
  · intro E mE μ _ f _
    simp
  · intro α _ ih E mE μ _ f hf
    rw [← Measure.pi_map_piOptionEquivProd μ]
    rw [lintegral_map_equiv _ (MeasurableEquiv.piOptionEquivProd E).symm]
    have key : ∀ a : ((i : α) → E (some i)) × E none,
        ∏ i, f i ((MeasurableEquiv.piOptionEquivProd E).symm a i) =
          (∏ i : α, f (some i) (a.1 i)) * f none a.2 := by
      intro a
      rw [Fintype.prod_option]
      have h1 : (MeasurableEquiv.piOptionEquivProd E).symm a none = a.2 := rfl
      have h2 : ∀ i, (MeasurableEquiv.piOptionEquivProd E).symm a (some i) = a.1 i := fun i => rfl
      rw [h1]; simp_rw [h2]; ring
    simp_rw [key]
    rw [lintegral_prod_mul (f := fun y : (i : α) → E (some i) => ∏ i : α, f (some i) (y i))
      (g := f none) (μ := Measure.pi fun i => μ (some i)) (ν := μ none)
      (Finset.measurable_prod _ fun i _ => (hf (some i)).comp (measurable_pi_apply i)).aemeasurable
      (hf none).aemeasurable]
    rw [ih (fun i => f (some i)) (fun i => hf _), Fintype.prod_option]
    ring


theorem measurePreserving_piCurry {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ j, Fintype (κ j)]
    (X : (j : ι) → κ j → Type*) [∀ j k, MeasurableSpace (X j k)]
    (μ : ∀ j k, Measure (X j k)) [∀ j k, SigmaFinite (μ j k)] :
    MeasurePreserving (MeasurableEquiv.piCurry X)
      (Measure.pi fun a : (Σ j, κ j) => μ a.1 a.2)
      (Measure.pi fun j => Measure.pi fun k => μ j k) := by
  set e := MeasurableEquiv.piCurry X with he
  have hsymm : MeasurePreserving e.symm (Measure.pi fun j => Measure.pi fun k => μ j k)
      (Measure.pi fun a : (Σ j, κ j) => μ a.1 a.2) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
    have hpre : e.symm ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun j => Set.pi Set.univ fun k => s ⟨j, k⟩ := by
      ext g
      simp [he, MeasurableEquiv.piCurry]
      exact ⟨fun h i j => h ⟨i, j⟩, fun h ⟨i, j⟩ => h i j⟩
    rw [e.symm.map_apply, hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun a : (Σ j, κ j) => μ a.1 a.2 (s a))).symm
  simpa using MeasurePreserving.symm e.symm hsymm


section Fibre

variable {ι J : Type*} [Fintype ι] [Fintype J] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]

/-- The configurations of the coordinates of colour `j`. -/
abbrev Fibre (α : ι → Type*) (c : ι → J) (j : J) : Type _ := ∀ i : {i // c i = j}, α i

/-- Restriction of a configuration to the fibres of a colouring. -/
def fibreMap (c : ι → J) (x : ∀ i, α i) : ∀ j, Fibre α c j := fun _ i => x i.1

omit [Fintype ι] [Fintype J] in
theorem measurable_fibreMap (c : ι → J) : Measurable (fibreMap (α := α) c) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_iff.mpr fun i => measurable_pi_apply i.1

theorem measurePreserving_fibreMap [DecidableEq J] (c : ι → J) :
    MeasurePreserving (fibreMap (α := α) c) (Measure.pi μ)
      (Measure.pi fun j => Measure.pi fun i : {i // c i = j} => μ i.1) := by
  classical
  let e : (Σ j, {i // c i = j}) ≃ ι := Equiv.sigmaFiberEquiv c
  have h1 := (measurePreserving_piCongrLeft μ e).symm (MeasurableEquiv.piCongrLeft α e)
  have h2 := measurePreserving_piCurry (fun (j : J) (i : {i // c i = j}) => α i.1)
    (fun j i => μ i.1)
  have h3 := h2.comp h1
  convert h3 using 1
  ext x j i
  rfl


theorem lintegral_prod_fibres [DecidableEq J] (c : ι → J)
    (F : ∀ j, Fibre α c j → ℝ≥0∞) (hF : ∀ j, Measurable (F j)) :
    ∫⁻ x, ∏ j, F j (fibreMap c x j) ∂(Measure.pi μ) =
      ∏ j, ∫⁻ y, F j y ∂(Measure.pi fun i : {i // c i = j} => μ i.1) := by
  rw [← lintegral_fintype_prod_eq_prod J F hF (μ := fun j => Measure.pi fun i : {i // c i = j} => μ i.1)]
  exact (measurePreserving_fibreMap μ c).lintegral_comp
    (f := fun y => ∏ j, F j (y j))
    (Finset.measurable_prod _ fun j _ => (hF j).comp (measurable_pi_apply j))

end Fibre

section Split

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]

/-- Splitting the coordinates of a finite product by a predicate: integral over the coordinates
satisfying `Q` outside, the others inside. -/
theorem lintegral_split (Q : ι → Prop) [DecidablePred Q] (F : (∀ i, α i) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ x, F x ∂(Measure.pi μ) =
      ∫⁻ z : (∀ i : {i // Q i}, α i), ∫⁻ w : (∀ i : {i // ¬ Q i}, α i),
        F ((MeasurableEquiv.piEquivPiSubtypeProd α Q).symm (z, w))
          ∂(Measure.pi fun i : {i // ¬ Q i} => μ i) ∂(Measure.pi fun i : {i // Q i} => μ i) := by
  have hmp := (measurePreserving_piEquivPiSubtypeProd μ Q).symm (MeasurableEquiv.piEquivPiSubtypeProd α Q)
  rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  exact lintegral_prod (fun a => F ((MeasurableEquiv.piEquivPiSubtypeProd α Q).symm a))
    (hF.comp (MeasurableEquiv.measurable _)).aemeasurable

end Split

section Reindex

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem measurePreserving_reindex (e : κ ≃ ι) {β : κ → Type*} {γ : ι → Type*}
    [∀ j, MeasurableSpace (β j)] [∀ i, MeasurableSpace (γ i)]
    (μ : ∀ i, Measure (γ i)) [∀ i, SigmaFinite (μ i)] (ν : ∀ j, Measure (β j))
    [∀ j, SigmaFinite (ν j)] (φ : ∀ j, γ (e j) → β j)
    (hφ : ∀ j, MeasurePreserving (φ j) (μ (e j)) (ν j)) :
    MeasurePreserving (fun (x : ∀ i, γ i) j => φ j (x (e j))) (Measure.pi μ) (Measure.pi ν) := by
  have h1 := (measurePreserving_piCongrLeft μ e).symm (MeasurableEquiv.piCongrLeft γ e)
  have h2 := measurePreserving_pi (fun j => μ (e j)) ν hφ
  exact h2.comp h1

end Reindex


section Decomp

variable {J ι : Type*} {A B : J → Type*} {α : ι → Type*} {W : (Σ j, A j ⊕ B j) → Type*}

/-- The regrouping map: a configuration on an index set bijective with `Σ j, A j ⊕ B j`, read as
a family over `j` of pairs (configuration on `A j`, configuration on `B j`). -/
def decompMap (G : (Σ j, A j ⊕ B j) ≃ ι) (φ : ∀ s, α (G s) → W s) (x : ∀ i, α i) :
    ∀ j, (∀ a : A j, W ⟨j, Sum.inl a⟩) × (∀ b : B j, W ⟨j, Sum.inr b⟩) :=
  fun j => (fun a => φ ⟨j, Sum.inl a⟩ (x (G ⟨j, Sum.inl a⟩)),
    fun b => φ ⟨j, Sum.inr b⟩ (x (G ⟨j, Sum.inr b⟩)))

theorem measurePreserving_decompMap [Fintype J] [Fintype ι] [∀ j, Fintype (A j)]
    [∀ j, Fintype (B j)] [∀ i, MeasurableSpace (α i)] [∀ s, MeasurableSpace (W s)]
    (G : (Σ j, A j ⊕ B j) ≃ ι) (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (ν : ∀ s, Measure (W s)) [∀ s, SigmaFinite (ν s)]
    (φ : ∀ s, α (G s) → W s) (hφ : ∀ s, MeasurePreserving (φ s) (μ (G s)) (ν s)) :
    MeasurePreserving (decompMap G φ) (Measure.pi μ)
      (Measure.pi fun j => (Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
        (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)) := by
  have h1 := measurePreserving_reindex G μ ν φ hφ
  have h2 := measurePreserving_piCurry (κ := fun j => A j ⊕ B j)
    (fun (j : J) (t : A j ⊕ B j) => W ⟨j, t⟩) (fun j t => ν ⟨j, t⟩)
  have h3 : ∀ j, MeasurePreserving
      (MeasurableEquiv.sumPiEquivProdPi (fun t : A j ⊕ B j => W ⟨j, t⟩))
      (Measure.pi fun t : A j ⊕ B j => ν ⟨j, t⟩)
      ((Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
        (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)) := fun j =>
    measurePreserving_sumPiEquivProdPi fun t : A j ⊕ B j => ν ⟨j, t⟩
  have h4 := measurePreserving_pi (fun j => Measure.pi fun t : A j ⊕ B j => ν ⟨j, t⟩)
    (fun j => (Measure.pi fun a : A j => ν ⟨j, Sum.inl a⟩).prod
        (Measure.pi fun b : B j => ν ⟨j, Sum.inr b⟩)) (f := fun j =>
      (MeasurableEquiv.sumPiEquivProdPi (fun t : A j ⊕ B j => W ⟨j, t⟩))) h3
  have h5 := h4.comp (h2.comp h1)
  convert h5 using 1
  funext x j
  rfl

end Decomp


section ThreeWay

variable {ι β₁ β₂ E : Type*} [Fintype ι] [Fintype β₁] [Fintype β₂] [MeasurableSpace E]
  (μ : Measure E) [SigmaFinite μ]

/-- Splitting a product measure on `ι → E` by a predicate `Q` and reading the two parts through
relabellings `e₁ : β₁ ≃ {Q}`, `e₂ : β₂ ≃ {¬Q}`: the integral of a product of a function of the
first part and a function of the second part is the product of the integrals. -/
theorem lintegral_mul_split (Q : ι → Prop) [DecidablePred Q] (e₁ : β₁ ≃ {i // Q i})
    (e₂ : β₂ ≃ {i // ¬ Q i}) (G : (β₁ → E) → ℝ≥0∞) (hG : Measurable G)
    (h : (β₂ → E) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ o : ι → E, G (fun b => o (e₁ b).1) * h (fun b => o (e₂ b).1)
        ∂(Measure.pi fun _ => μ) =
      (∫⁻ u, G u ∂(Measure.pi fun _ : β₁ => μ)) * ∫⁻ v, h v ∂(Measure.pi fun _ : β₂ => μ) := by
  have hmeas : Measurable fun o : ι → E => G (fun b => o (e₁ b).1) * h (fun b => o (e₂ b).1) :=
    (hG.comp (measurable_pi_iff.mpr fun b => measurable_pi_apply _)).mul
      (hh.comp (measurable_pi_iff.mpr fun b => measurable_pi_apply _))
  rw [lintegral_split (fun _ => μ) Q _ hmeas]
  have hz : MeasurePreserving (fun z : ∀ i : {i // Q i}, E => fun b : β₁ => z (e₁ b))
      (Measure.pi fun _ : {i // Q i} => μ) (Measure.pi fun _ : β₁ => μ) :=
    measurePreserving_reindex e₁ (fun _ => μ) (fun _ => μ) (fun _ v => v)
      (fun _ => MeasurePreserving.id _)
  have hw : MeasurePreserving (fun z : ∀ i : {i // ¬ Q i}, E => fun b : β₂ => z (e₂ b))
      (Measure.pi fun _ : {i // ¬ Q i} => μ) (Measure.pi fun _ : β₂ => μ) :=
    measurePreserving_reindex e₂ (fun _ => μ) (fun _ => μ) (fun _ v => v)
      (fun _ => MeasurePreserving.id _)
  have e1 : ∀ (zG : ∀ i : {i // Q i}, E) (wN : ∀ i : {i // ¬ Q i}, E),
      G (fun b => ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) Q).symm (zG, wN))
        (e₁ b).1) *
      h (fun b => ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) Q).symm (zG, wN))
        (e₂ b).1) = G (fun b => zG (e₁ b)) * h (fun b => wN (e₂ b)) := by
    intro zG wN
    congr 2
    · funext b
      simp [MeasurableEquiv.piEquivPiSubtypeProd, (e₁ b).2]
    · funext b
      simp [MeasurableEquiv.piEquivPiSubtypeProd, (e₂ b).2]
  simp_rw [e1]
  have e2 : ∀ zG : ∀ i : {i // Q i}, E,
      ∫⁻ wN : ∀ i : {i // ¬ Q i}, E, G (fun b => zG (e₁ b)) * h (fun b => wN (e₂ b))
        ∂(Measure.pi fun _ : {i // ¬ Q i} => μ) =
      G (fun b => zG (e₁ b)) * ∫⁻ v, h v ∂(Measure.pi fun _ : β₂ => μ) := by
    intro zG
    have hm : Measurable fun wN : ∀ i : {i // ¬ Q i}, E => h (fun b => wN (e₂ b)) :=
      hh.comp hw.measurable
    rw [lintegral_const_mul (G fun b => zG (e₁ b)) hm]
    congr 1
    exact hw.lintegral_comp hh
  simp_rw [e2]
  have hm : Measurable fun zG : ∀ i : {i // Q i}, E => G (fun b => zG (e₁ b)) :=
    hG.comp hz.measurable
  rw [lintegral_mul_const _ hm]
  congr 1
  exact hz.lintegral_comp hG

end ThreeWay

end Balaban.LargeField.PiTools
