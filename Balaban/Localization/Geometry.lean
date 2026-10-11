/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.AbstractExpansion
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card

/-!
# The component `Y(𝒞)` and the abstract form of (GM1)

* `patchUnion X₁ P C = X₁ ∪ ⋃_{i ∈ C} P i` (this is `V(𝒞)`) and `componentOf G X₁ V`, the set of
  sites of `V` reachable from `X₁` inside `V` (this is `Y(𝒞)` for `V = V(𝒞)`).  With
  `Y C := componentOf G X₁ (patchUnion X₁ P C)` these are the data of `abstract_expansion`.
* `card_layer_biUnion_le` is (GM1) in abstract form: if each patch `i` has an enlargement
  `D i` of at most `G₀` cubes, all in the layer of the patch, then the cubes of `X₁ ∪ ⋃ D i`
  outside `X₁` in layer `n` number at most `G₀` times the patches of layer `n` in `C`.
-/

@[expose] public section

namespace Balaban.Localization

variable {Ω ι : Type*}

/-- `V(𝒞) = X₁ ∪ ⋃_{P ∈ 𝒞} P`. -/
def patchUnion (X₁ : Set Ω) (P : ι → Set Ω) (C : Finset ι) : Set Ω :=
  X₁ ∪ ⋃ i ∈ C, P i

/-- The set of sites reachable from `X₁` by a path of adjacent sites inside `V`. -/
def componentOf (G : SimpleGraph Ω) (X₁ V : Set Ω) : Set Ω :=
  {x | ∃ y ∈ X₁, Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∈ V ∧ b ∈ V) y x}

theorem subset_componentOf (G : SimpleGraph Ω) (X₁ V : Set Ω) : X₁ ⊆ componentOf G X₁ V :=
  fun y hy => ⟨y, hy, Relation.ReflTransGen.refl⟩

theorem componentOf_subset (G : SimpleGraph Ω) {X₁ V : Set Ω} (hX : X₁ ⊆ V) :
    componentOf G X₁ V ⊆ V := by
  rintro x ⟨y, hy, h⟩
  induction h with
  | refl => exact hX hy
  | tail _ hbc _ => exact hbc.2.2

theorem componentOf_mono (G : SimpleGraph Ω) {X₁ V V' : Set Ω} (h : V ⊆ V') :
    componentOf G X₁ V ⊆ componentOf G X₁ V' := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, hy, Relation.ReflTransGen.mono (fun a b hab => ⟨hab.1, h hab.2.1, h hab.2.2⟩) y x hxy⟩

/-- (GM1), abstract form. -/
theorem card_layer_biUnion_le {κ ν : Type*} [DecidableEq κ] [DecidableEq ν] [DecidableEq ι]
    (D : ι → Finset κ) (G₀ : ℕ) (hD : ∀ i, (D i).card ≤ G₀) (lay : κ → ν) (patchLayer : ι → ν)
    (hlay : ∀ i, ∀ c ∈ D i, lay c = patchLayer i) (X₁ : Finset κ) (C : Finset ι) (n : ν) :
    (((X₁ ∪ C.biUnion D) \ X₁).filter (fun c => lay c = n)).card ≤
      G₀ * (C.filter (fun i => patchLayer i = n)).card := by
  have hsub : ((X₁ ∪ C.biUnion D) \ X₁).filter (fun c => lay c = n) ⊆
      (C.filter (fun i => patchLayer i = n)).biUnion D := by
    intro c hc
    rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hc
    obtain ⟨⟨hc1 | hc1, hc2⟩, hc3⟩ := hc
    · exact absurd hc1 hc2
    · obtain ⟨i, hi, hci⟩ := Finset.mem_biUnion.mp hc1
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, by rw [← hlay i c hci]; exact hc3⟩,
        hci⟩
  rw [mul_comm]
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul _ _ _ fun i _ => hD i)

end Balaban.Localization
