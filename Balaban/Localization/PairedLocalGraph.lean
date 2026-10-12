/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpLocal
public import Balaban.Localization.I5Local

/-!
# The paired graph criterion (VMOD-12 §1, §1.1)

For a set `Y` of sites, the component maps `B_H(Y)` (live eligible centres whose footprint meets
`Y`) and `A_H(Y)` (parameters of `𝒞` incident to such a centre) of VMOD-12 (1.2); the four
geometric statements G-site, G-foot, G-par, G-cell imply that `(Y, A_H(Y))` is a union of
components of the incidence graph (`incUnion_of_geom`), and `A_H(Y)` consists of cells inside `Y`.
The cross-footprint lemma (1.4) is `SYF_cross`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Maps

variable (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
  (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
  (Y : Finset (CTorus d L N₁ m₁ K))

open Classical in
/-- **(1.2)** `B_H(Y)`: the eligible live centres of the cover whose footprint meets `Y`. -/
noncomputable def compCentres : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  C.cubeIdx.filter fun z => EligC C X₁ 𝒞 z ∧ LiveI H z ∧ ∃ x ∈ footprint H a ν z, x ∈ Y

open Classical in
/-- **(1.2)** `A_H(Y)`: the parameters of `𝒞` incident to a centre of `B_H(Y)`. -/
noncomputable def compParams : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  𝒞.filter fun P => ∃ z ∈ compCentres C H a ν X₁ 𝒞 Y, P ∈ C.Qset z

variable {C H a ν X₁ 𝒞 Y}

theorem mem_compCentres {z : ℕ × CTorus d L N₁ m₁ K} :
    z ∈ compCentres C H a ν X₁ 𝒞 Y ↔
      EligC C X₁ 𝒞 z ∧ LiveI H z ∧ ∃ x ∈ footprint H a ν z, x ∈ Y := by
  classical
  unfold compCentres
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h⟩⟩

theorem mem_compParams {P : ℕ × CTorus d L N₁ m₁ K} :
    P ∈ compParams C H a ν X₁ 𝒞 Y ↔
      P ∈ 𝒞 ∧ ∃ z ∈ compCentres C H a ν X₁ 𝒞 Y, P ∈ C.Qset z := by
  classical
  unfold compParams
  rw [Finset.mem_filter]

/-- **The paired graph criterion (VMOD-12 (1.3))**: G-site, G-foot, G-par, G-cell for an operator
`H` imply that `(Y, A_H(Y))` is a union of components of the incidence graph of `(C, H)`, and the
cells of `A_H(Y)` lie in `Y`. -/
theorem incUnion_of_geom
    (hsite : ∀ x ∈ Y, x ∈ incSites C H a ν X₁ 𝒞 → ∀ y ∈ incSites C H a ν X₁ 𝒞, Adj x y → y ∈ Y)
    (hfoot : ∀ z ∈ compCentres C H a ν X₁ 𝒞 Y, ∀ x ∈ footprint H a ν z, x ∈ Y)
    (hpar : ∀ z, EligC C X₁ 𝒞 z → LiveI H z → ∀ P ∈ C.Qset z, P ∈ 𝒞 →
      P ∈ compParams C H a ν X₁ 𝒞 Y → z ∈ compCentres C H a ν X₁ 𝒞 Y)
    (hcell : ∀ P ∈ compParams C H a ν X₁ 𝒞 Y, ∀ x ∈ cubeP P, x ∈ Y) :
    IsIncUnion C H a ν X₁ 𝒞 Y (compParams C H a ν X₁ 𝒞 Y) ∧
      ∀ P ∈ compParams C H a ν X₁ 𝒞 Y, P ∈ 𝒞 ∧ ∀ x ∈ cubeP P, x ∈ Y := by
  refine ⟨⟨{v | match v with
      | .inl x => x ∈ Y
      | .inr (.inl z) => z ∈ compCentres C H a ν X₁ 𝒞 Y
      | .inr (.inr P) => P ∈ compParams C H a ν X₁ 𝒞 Y}, ?_, fun x => Iff.rfl,
      fun P => Iff.rfl⟩, fun P hP => ⟨(mem_compParams.1 hP).1, hcell P hP⟩⟩
  have g2 : ∀ x z, x ∈ Y → (EligC C X₁ 𝒞 z ∧ LiveI H z ∧ x ∈ footprint H a ν z) →
      z ∈ compCentres C H a ν X₁ 𝒞 Y := fun x z hx h => mem_compCentres.2 ⟨h.1, h.2.1, x, h.2.2, hx⟩
  have g4 : ∀ z P, z ∈ compCentres C H a ν X₁ 𝒞 Y →
      (EligC C X₁ 𝒞 z ∧ LiveI H z ∧ P ∈ C.Qset z ∧ P ∈ 𝒞) → P ∈ compParams C H a ν X₁ 𝒞 Y :=
    fun z P hz h => mem_compParams.2 ⟨h.2.2.2, z, hz, h.2.2.1⟩
  intro u v hadj hu
  obtain ⟨-, h | h⟩ := hadj
  · rcases u with x | z | P <;> rcases v with y | z' | P' <;> simp only [incRel] at h <;>
      first
        | exact hsite _ hu h.1 _ h.2.1 h.2.2
        | exact g2 _ _ hu h
        | exact hfoot _ hu _ h.2.2
        | exact g4 _ _ hu h
  · rcases u with x | z | P <;> rcases v with y | z' | P' <;> simp only [incRel] at h <;>
      first
        | exact hsite _ hu h.2.1 _ h.1 h.2.2.symm
        | exact g2 _ _ hu h
        | exact hfoot _ hu _ h.2.2
        | exact g4 _ _ hu h
        | exact hpar _ h.1 h.2.1 _ h.2.2.1 h.2.2.2 hu

/-- **The cross-footprint lemma (VMOD-12 (1.4))**: a point of `Ω₁(H_∂)` and `Ω₁(H_-)` in the
footprint sites of the old operator `H_-` lies in those of `H_∂`, given the incidence-union property
for `H_∂`.  (VMOD-12 states the hypothesis as `x ∈ Ω₁(H_∂)` only; the landed `SYF_subset_Y` it
cites needs `x ∈ Ω₁(H_-)`, so that membership is a hypothesis here.) -/
theorem SYF_cross {ϱ' : ℝ} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hb : IsIncUnion C Hb a ν X₁ 𝒞 Y A)
    {x : CTorus d L N₁ m₁ K} (hxm : x ∈ H.Ω 1) (hxb : x ∈ Hb.Ω 1)
    (hx : x ∈ SYF C H a ν X₁ 𝒞 Y) : x ∈ SYF C Hb a ν X₁ 𝒞 Y := by
  classical
  have hxY : x ∈ Y := SYF_subset_Y (x := ⟨x, hxm⟩) hx
  unfold SYF at hx ⊢
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨hzc, hE, hL, -⟩ := Finset.mem_filter.1 hz
  have hLb : LiveI Hb z := ⟨⟨x, hxb⟩, hxz⟩
  refine Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hzc, hE, hLb, ?_⟩, hxz⟩
  rcases hb.dichotomy hE hLb with ⟨h, -⟩ | h
  · exact h
  · exact absurd hxY (h _ (mem_footprint_self (b := ⟨x, hxb⟩) hxz))

end Maps

end Balaban.Localization.Dec2
