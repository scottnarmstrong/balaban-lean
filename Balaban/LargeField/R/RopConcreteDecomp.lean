/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib

/-!
# The product decomposition of the block-field space along disjoint blocks (P7 (1.3)-(1.6))

For disjoint finite sets of blocks `B c`, `c ∈ ι`, the space of fields `T → ℝ^N` is identified, measure-preservingly,
with `(Π_c ℝ^{B c × N}) × ℝ^{outside}` (`decompME`): the variables `ψ_k↾Z₀(c)` of the components and the remaining
variables `ψ_k↾(⋃ Z₀(c))ᶜ`.  The components are `EuclideanSpace`s, as in `SuppSpace`.  The proof composes the
currying `ψ ↦ (ψ(z, i))`, the reindexing along `decompIdx`, and the splitting of a sum index
(`measurePreserving_piCurry_symm'` is the missing measure statement for the currying of a finite product).
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory

namespace Balaban.LargeField

theorem measurePreserving_piCurry_symm' {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (μ : ∀ i j, Measure (X i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm
      (Measure.pi fun i => Measure.pi fun j => μ i j)
      (Measure.pi fun p : (i : ι) × κ i => μ p.1 p.2) where
  measurable := (MeasurableEquiv.piCurry X).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have : (MeasurableEquiv.piCurry X).symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s ⟨i, j⟩)) := by
      ext f
      simp [Set.mem_pi, MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry, Sigma.forall]
    rw [this, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_sigma]

section Decomp

variable {T : Type} [Fintype T] {ι : Type} [Fintype ι] (B : ι → Finset T) (N : ℕ)

/-- The coordinates `(z, i)` outside every `B c`. -/
def ZeroOutIdx : Type := {j : (_ : T) × Fin N // ∀ c, j.1 ∉ B c}

noncomputable instance : Fintype (ZeroOutIdx B N) := by classical exact Subtype.fintype _

variable {B N}

/-- The index equivalence. -/
noncomputable def decompIdx (hB : ∀ c c', c ≠ c' → Disjoint (B c) (B c')) :
    (ZeroOutIdx B N ⊕ (c : ι) × (↥(B c) × Fin N)) ≃ ((_ : T) × Fin N) :=
  Equiv.ofBijective (Sum.elim (fun y => y.1) (fun p => ⟨p.2.1.1, p.2.2⟩)) (by
    classical
    constructor
    · rintro (y | ⟨c, z, i⟩) (y' | ⟨c', z', i'⟩) h
      · simp only [Sum.elim_inl] at h; exact congrArg _ (Subtype.ext h)
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        have h1 : (y.1).1 = z'.1 := congrArg Sigma.fst h
        exact absurd (h1 ▸ z'.2) (y.2 c')
      · simp only [Sum.elim_inl, Sum.elim_inr] at h
        have h1 : (y'.1).1 = z.1 := (congrArg Sigma.fst h).symm
        exact absurd (h1 ▸ z.2) (y'.2 c)
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff] at h
        obtain ⟨h1, h2⟩ := h
        have hc : c = c' := by
          by_contra hne
          exact Finset.disjoint_left.1 (hB c c' hne) z.2 (h1 ▸ z'.2)
        subst hc
        have : z = z' := Subtype.ext h1
        have : i = i' := eq_of_heq h2
        subst_vars; rfl
    · rintro ⟨z, i⟩
      by_cases h : ∃ c, z ∈ B c
      · obtain ⟨c, hc⟩ := h
        exact ⟨Sum.inr ⟨c, ⟨z, hc⟩, i⟩, rfl⟩
      · exact ⟨Sum.inl ⟨⟨z, i⟩, fun c hc => h ⟨c, hc⟩⟩, rfl⟩)


/-- The measurable equivalence. -/
noncomputable def decompME (hB : ∀ c c', c ≠ c' → Disjoint (B c) (B c')) :
    ((_ : T) → Fin N → ℝ) ≃ᵐ
      ((c : ι) → EuclideanSpace ℝ (↥(B c) × Fin N)) × (ZeroOutIdx B N → ℝ) :=
  (MeasurableEquiv.piCurry (fun (_ : T) (_ : Fin N) => ℝ)).symm.trans <|
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (decompIdx (N := N) hB)).symm.trans <|
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)).trans <|
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.piCurry (fun (c : ι) (_ : ↥(B c) × Fin N) => ℝ))).trans <|
  (MeasurableEquiv.prodComm).trans <|
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.piCongrRight (fun c => MeasurableEquiv.toLp 2 (↥(B c) × Fin N → ℝ)))
    (MeasurableEquiv.refl _)

theorem decompME_fst (hB : ∀ c c', c ≠ c' → Disjoint (B c) (B c')) (ψ : (_ : T) → Fin N → ℝ) (c : ι) :
    (decompME hB ψ).1 c = WithLp.toLp 2 (fun p : ↥(B c) × Fin N => ψ p.1 p.2) := rfl

theorem decompME_snd (hB : ∀ c c', c ≠ c' → Disjoint (B c) (B c')) (ψ : (_ : T) → Fin N → ℝ)
    (y : ZeroOutIdx B N) : (decompME hB ψ).2 y = ψ y.1.1 y.1.2 := rfl

theorem decompME_mp (hB : ∀ c c', c ≠ c' → Disjoint (B c) (B c')) :
    MeasurePreserving (decompME (N := N) hB) volume (volume.prod volume) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piCurry (fun (_ : T) (_ : Fin N) => ℝ)).symm volume volume :=
    measurePreserving_piCurry_symm' (fun _ _ => volume)
  have h2 : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (decompIdx (N := N) hB)).symm volume volume :=
    MeasurePreserving.symm _ (volume_measurePreserving_piCongrLeft (fun _ => ℝ) (decompIdx (N := N) hB))
  have h3 := volume_measurePreserving_sumPiEquivProdPi (fun _ : ZeroOutIdx B N ⊕ ((c : ι) × (↥(B c) × Fin N)) => ℝ)
  have h4 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ZeroOutIdx B N → ℝ))
      (MeasurableEquiv.piCurry (fun (c : ι) (_ : ↥(B c) × Fin N) => ℝ))) (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod
      (MeasurePreserving.symm _ (measurePreserving_piCurry_symm' (fun (_ : ι) (_ : ↥(B _) × Fin N) => (volume : Measure ℝ))))
  have h5 : MeasurePreserving (MeasurableEquiv.prodComm (α := ZeroOutIdx B N → ℝ) (β := (c : ι) → ↥(B c) × Fin N → ℝ))
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  have h6 : MeasurePreserving (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrRight (fun c => MeasurableEquiv.toLp 2 (↥(B c) × Fin N → ℝ)))
      (MeasurableEquiv.refl (ZeroOutIdx B N → ℝ))) (volume.prod volume) (volume.prod volume) :=
    (measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun c => PiLp.volume_preserving_toLp _)).prod
      (MeasurePreserving.id volume)
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))

end Decomp


end Balaban.LargeField
