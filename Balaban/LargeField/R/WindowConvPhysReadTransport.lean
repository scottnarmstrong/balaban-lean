/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvDef

/-!
# Transport of a restricted action between two generating sets on the same torus

P7 p. 501 (2.14)-(2.16); P6 pp. 6-7 (2.13)-(2.16).  Let `Xl` be a region of a generating set `Gl`
and `Xw` a region of a generating set `Gw`, the two tori being identified by a bijection `e` that
commutes with the lattice steps.  If `e` carries the sites of `Xw` to those of `Xl`, the layer
indices and the blocks of the sites agree, the data agree on the sites, and every neighbour of a
site of `Xw` lies in the first domain of `Gl`, then the restricted action of `Xl` at the field
transported from a field `φw` of `Gw` equals the restricted action of `Xw` at `φw`.

The transported field is `φl p = φ̄w (e⁻¹ p)`, the extension of `φw` by the data of `Gw`.  All four
reads of the action (block averages, mass terms, internal bonds and crossing bonds with their
collar endpoints) are compared term by term.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

section Transport

variable {d L N N₀w kw N₀l kl : ℕ} [NeZero N₀w] [NeZero N₀l] [NeZero L] {ϱw ϱl : ℝ}
  {Gw : GeneratingSet d L N₀w kw ϱw} {Gl : GeneratingSet d L N₀l kl ϱl}

/-- The field of `Gl` obtained from a field `φw` of `Gw` along an identification `e` of the tori:
the extension of `φw` by the data `Ψw`, read at `e⁻¹`. -/
noncomputable def transportField (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl))
    (Ψw : Torus d (N₀w * L ^ kw) → Fin N → ℂ) (φw : Gw.Ω 1 × Fin N → ℂ) :
    Gl.Ω 1 × Fin N → ℂ :=
  fun p => barField Gw Ψw φw (e.symm p.1) p.2

variable (e : Torus d (N₀w * L ^ kw) ≃ Torus d (N₀l * L ^ kl))
  (Xw : Region Gw) (Xl : Region Gl) (Dw : BgData Gw N) (Dl : BgData Gl N)
  (φw : Gw.Ω 1 × Fin N → ℂ)

theorem transportField_barField {x : Torus d (N₀w * L ^ kw)} (hx : e x ∈ Gl.Ω 1) (i : Fin N) :
    barField Gl Dl.Ψ (transportField (Gl := Gl) e Dw.Ψ φw) (e x) i = barField Gw Dw.Ψ φw x i := by
  classical
  simp [barField, hx, transportField]

theorem transportField_svec {y : Torus d (N₀w * L ^ kw)} (hy : y ∈ Gw.Ω 1) (hy' : e y ∈ Gl.Ω 1)
    (i : Fin N) :
    svec Gl (transportField (Gl := Gl) e Dw.Ψ φw) (e y) i = svec Gw φw y i := by
  have h1 := svec_of_mem Gl (transportField (Gl := Gl) e Dw.Ψ φw) ⟨e y, hy'⟩ i
  have h2 := svec_of_mem Gw φw ⟨y, hy⟩ i
  simp only at h1 h2
  rw [h1, h2]
  classical
  unfold transportField barField
  simp [hy]

variable {e Xw Xl Dw Dl φw}

/-- **Transport of the restricted action** between two generating sets (P7 (2.14)-(2.16)). -/
theorem actionRegionC_transport
    (he : ∀ x μ, e (x + Pi.single μ 1) = e x + Pi.single μ 1)
    (hsites : ∀ x, x ∈ Xw.sites ↔ e x ∈ Xl.sites)
    (hlay : ∀ x ∈ Xw.sites, Gl.layerIndex (e x) = Gw.layerIndex x)
    (hblk : ∀ x ∈ Xw.sites, ∀ y, y ∈ Gl.blk (Gl.layerIndex (e x)) (e x) ↔
      e.symm y ∈ Gw.blk (Gw.layerIndex x) x)
    (hnb : ∀ x ∈ Xw.sites, ∀ μ : Fin d,
      e (x + Pi.single μ 1) ∈ Gl.Ω 1 ∧ e (x - Pi.single μ 1) ∈ Gl.Ω 1)
    (hΨ : ∀ x ∈ Xw.sites, Dl.Ψ (e x) = Dw.Ψ x)
    (hh : ∀ x ∈ Xw.sites, Dl.h (e x) = Dw.h x) (a : ℕ → ℝ) (ν : ℝ) :
    actionRegionC Xl a ν Dl (transportField (Gl := Gl) e Dw.Ψ φw) =
      actionRegionC Xw a ν Dw φw := by
  classical
  have hXl : ∀ x ∈ Xw.sites, e x ∈ Gl.Ω 1 := fun x hx => Xl.sub_Ω ((hsites x).1 hx)
  have hXw : ∀ x ∈ Xw.sites, x ∈ Gw.Ω 1 := fun x hx => Xw.sub_Ω hx
  have hmap : Xl.sites = Xw.sites.map e.toEmbedding := by
    ext y
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro hy
      exact ⟨e.symm y, (hsites _).2 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hsites x).1 hx
  have hsv : ∀ x ∈ Xw.sites, ∀ i, svec Gl (transportField (Gl := Gl) e Dw.Ψ φw) (e x) i =
      svec Gw φw x i := fun x hx i => transportField_svec e Dw φw (hXw x hx) (hXl x hx) i
  have hbav : ∀ x ∈ Xw.sites, ∀ i, blockAvg Gl (transportField (Gl := Gl) e Dw.Ψ φw) (e x) i =
      blockAvg Gw φw x i := by
    intro x hx i
    unfold blockAvg
    rw [hlay x hx]
    congr 1
    have hset : Gl.blk (Gw.layerIndex x) (e x) = (Gw.blk (Gw.layerIndex x) x).map e.toEmbedding := by
      ext y
      simp only [Finset.mem_map, Equiv.coe_toEmbedding]
      rw [← hlay x hx, hblk x hx y]
      rw [hlay x hx]
      constructor
      · intro hy; exact ⟨e.symm y, hy, by simp⟩
      · rintro ⟨z, hz, rfl⟩; simpa using hz
    rw [hset, Finset.sum_map]
    refine Finset.sum_congr rfl fun y hy => ?_
    exact hsv y (Xw.blockClosed x hx y hy) i
  have hlev : ∀ x ∈ Xw.sites, levelCoeff Gl a (e x) = levelCoeff Gw a x := by
    intro x hx
    unfold levelCoeff
    rw [hlay x hx]
  have h1 : Xl.blockPair a (fun x i => Dl.Ψ x i -
      blockAvg Gl (transportField (Gl := Gl) e Dw.Ψ φw) x i)
      (fun x i => Dl.Ψ x i - blockAvg Gl (transportField (Gl := Gl) e Dw.Ψ φw) x i) =
      Xw.blockPair a (fun x i => Dw.Ψ x i - blockAvg Gw φw x i)
        (fun x i => Dw.Ψ x i - blockAvg Gw φw x i) := by
    unfold Region.blockPair
    rw [hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Equiv.coe_toEmbedding]
    rw [hlev x hx]
    simp only [hΨ x hx, hbav x hx]
  have h3 : Xl.massPair (fun x i => svec Gl (transportField (Gl := Gl) e Dw.Ψ φw) x i - Dl.h x i)
      (fun x i => svec Gl (transportField (Gl := Gl) e Dw.Ψ φw) x i - Dl.h x i) =
      Xw.massPair (fun x i => svec Gw φw x i - Dw.h x i)
        (fun x i => svec Gw φw x i - Dw.h x i) := by
    unfold Region.massPair
    rw [hmap, Finset.sum_map]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Equiv.coe_toEmbedding]
    simp only [hsv x hx, hh x hx]
  have hwt : ∀ x μ, Xl.starWeight (e x) μ = Xw.starWeight x μ := by
    intro x μ
    unfold Region.starWeight
    rw [← he x μ]
    simp only [← hsites]
  have h2 : Xl.bondPair (barField Gl Dl.Ψ (transportField (Gl := Gl) e Dw.Ψ φw))
      (barField Gl Dl.Ψ (transportField (Gl := Gl) e Dw.Ψ φw)) =
      Xw.bondPair (barField Gw Dw.Ψ φw) (barField Gw Dw.Ψ φw) := by
    unfold Region.bondPair
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [hwt x μ]
    by_cases hw : Xw.starWeight x μ = 0
    · simp [hw]
    · have hor : x ∈ Xw.sites ∨ x + Pi.single μ 1 ∈ Xw.sites := by
        by_contra hcon
        push Not at hcon
        apply hw
        unfold Region.starWeight
        simp [hcon.1, hcon.2]
      have hb : e x ∈ Gl.Ω 1 ∧ e (x + Pi.single μ 1) ∈ Gl.Ω 1 := by
        rcases hor with h | h
        · exact ⟨hXl x h, (hnb x h μ).1⟩
        · refine ⟨?_, hXl _ h⟩
          have := (hnb _ h μ).2
          rwa [add_sub_cancel_right] at this
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [← he x μ, transportField_barField e Dw Dl φw hb.1 i,
        transportField_barField e Dw Dl φw hb.2 i]
  unfold actionRegionC
  rw [h1, h2, h3]

end Transport

end Balaban.LargeField.ActionConv
