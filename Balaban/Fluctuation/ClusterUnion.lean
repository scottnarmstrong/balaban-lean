/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Subadditivity of a size along connected families

If a size `φ` on finite sets is subadditive for two nonempty overlapping sets,
`φ (X ∪ Y) ≤ φ X + φ Y + c`, then along a family indexed by the vertices of a connected graph,
each adjacent pair overlapping, `φ (⋃ f i) ≤ ∑ φ (f i) + c (n - 1)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Finset

variable {B ι : Type*} [DecidableEq B] [DecidableEq ι]

/-- **Subadditivity along a connected family** (induced subgraph on a finite set of indices). -/
theorem phi_union_le (φ : Finset B → ℝ) (c : ℝ)
    (hbin : ∀ X Y : Finset B, X.Nonempty → Y.Nonempty → ¬ Disjoint X Y →
      φ (X ∪ Y) ≤ φ X + φ Y + c)
    (G : SimpleGraph ι) (f : ι → Finset B) (hf : ∀ i, (f i).Nonempty)
    (hadj : ∀ i j, G.Adj i j → ¬ Disjoint (f i) (f j)) :
    ∀ (n : ℕ) (I : Finset ι), I.card = n + 1 → (G.induce (I : Set ι)).Connected →
      φ (I.biUnion f) ≤ ∑ i ∈ I, φ (f i) + c * n := by
  intro n
  induction n with
  | zero =>
    intro I hI _
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hI
    simp
  | succ n ih =>
    intro I hI hconn
    have hI2 : 1 < I.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hI2
    have : Nontrivial (↥(I : Set ι)) := ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩⟩
    have : Finite (↥(I : Set ι)) := inferInstance
    obtain ⟨u, hu⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
    have huI : u.1 ∈ I := u.2
    have hcard : (I.erase u.1).card = n + 1 := by rw [Finset.card_erase_of_mem huI]; omega
    let g : (G.induce (I : Set ι)).induce {u}ᶜ →g G.induce ((I.erase u.1 : Finset ι) : Set ι) :=
      { toFun := fun v => ⟨v.1.1, by
          have := v.2
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at this
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          exact ⟨v.1.2, fun h => this (Subtype.ext h)⟩⟩
        map_rel' := fun {a b} h => by simpa using h }
    have hg : Function.Surjective g := by
      rintro ⟨y, hy⟩
      have hy' : y ∈ I.erase u.1 := hy
      rw [Finset.mem_erase] at hy'
      exact ⟨⟨⟨y, hy'.2⟩, fun h => hy'.1 (congrArg Subtype.val h)⟩, rfl⟩
    have hconn' : (G.induce ((I.erase u.1 : Finset ι) : Set ι)).Connected := hu.map g hg
    have ih' := ih (I.erase u.1) hcard hconn'
    -- `u` is adjacent to a vertex of `I.erase u`
    obtain ⟨w, hwI, hw⟩ : ∃ w ∈ I, G.Adj u.1 w := by
      obtain ⟨c, hc, hcu⟩ := Finset.exists_mem_ne (by omega : 1 < I.card) u.1
      obtain ⟨p⟩ := hconn.preconnected u ⟨c, hc⟩
      cases p with
      | nil => exact absurd rfl hcu
      | @cons _ v _ hadj' q => exact ⟨v.1, v.2, hadj'⟩
    have hwE : w ∈ I.erase u.1 :=
      Finset.mem_erase.2 ⟨fun h => G.loopless.irrefl u.1 (h ▸ hw), hwI⟩
    have hne : ((I.erase u.1).biUnion f).Nonempty := by
      obtain ⟨x, hx⟩ := hf w
      exact ⟨x, Finset.mem_biUnion.2 ⟨w, hwE, hx⟩⟩
    have hov : ¬ Disjoint ((I.erase u.1).biUnion f) (f u.1) := by
      obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.1 (hadj _ _ hw)
      exact Finset.not_disjoint_iff.2 ⟨x, Finset.mem_biUnion.2 ⟨w, hwE, hx2⟩, hx1⟩
    have hbi : I.biUnion f = (I.erase u.1).biUnion f ∪ f u.1 := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
      constructor
      · rintro ⟨i, hi, hx⟩
        by_cases hiu : i = u.1
        · exact Or.inr (hiu ▸ hx)
        · exact Or.inl ⟨i, ⟨hiu, hi⟩, hx⟩
      · rintro (⟨i, ⟨_, hi⟩, hx⟩ | hx)
        · exact ⟨i, hi, hx⟩
        · exact ⟨u.1, huI, hx⟩
    rw [hbi]
    have := hbin _ _ hne (hf u.1) hov
    have hsum : ∑ i ∈ I, φ (f i) = ∑ i ∈ I.erase u.1, φ (f i) + φ (f u.1) := by
      rw [Finset.sum_erase_add _ _ huI]
    rw [hsum]
    push_cast
    linarith

end Balaban.Fluctuation
