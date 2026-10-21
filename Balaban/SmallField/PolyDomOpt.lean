/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6Terms

/-!
# Optimal connecting structures of a polymer

The covering size `d_j(X) = treeLenCovOne m₀ j X` of a polymer `X ∈ 𝒟_j` is an infimum over the
admissible triples `(𝒦, W, E)`: a chosen family of `π'_j`-cubes of `X`, a connected structure of
sites `W ⊆ X` with bonds `E` meeting every chosen cube.  On a finite torus the costs of the admissible
triples form a finite set, nonempty for a polymer (`W = X`, `E` all bonds of `X`), so the infimum is
attained: there is an optimal triple (`exists_opt_of_isPolyDom`).  This supplies the chosen
families `𝒦X` and the optimal structures `hopt` of the labels of the class chain.

* `connStruct_nbrPairs`: the sites of a nonempty connected set with all its bonds form a connected
  structure;
* `admissible_of_isPolyDom`, `exists_opt_of_isPolyDom`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- **The sites of a nonempty connected set with all its bonds form a connected structure.** -/
theorem connStruct_nbrPairs {Y : Set (CTorus d L N₁ m₁ k)} (hne : Y.Nonempty)
    (hcon : ∀ x ∈ Y, ∀ y ∈ Y, Relation.ReflTransGen (fun a b => a ∈ Y ∧ b ∈ Y ∧ Nbr a b) x y) :
    ConnStruct (Set.toFinite Y).toFinset
      (((Set.toFinite Y).toFinset ×ˢ (Set.toFinite Y).toFinset).filter (fun p => Nbr p.1 p.2)) ∧
      (↑(Set.toFinite Y).toFinset : Set (CTorus d L N₁ m₁ k)) = Y := by
  set W : Finset (CTorus d L N₁ m₁ k) := (Set.toFinite Y).toFinset with hW
  have hWY : ∀ x, x ∈ W ↔ x ∈ Y := fun x => by simp [hW]
  refine ⟨⟨?_, ?_, ?_⟩, by simp [hW]⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, (hWY x).2 hx⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  · intro x hx y hy
    refine Relation.ReflTransGen.mono ?_ x y (hcon x ((hWY x).1 hx) y ((hWY y).1 hy))
    intro a b ⟨ha, hb, hab⟩
    left
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨(hWY a).2 ha, (hWY b).2 hb⟩, hab⟩

/-- **A polymer has an admissible triple** of the covering size: its chosen family, its sites and
all its bonds. -/
theorem admissible_of_isPolyDom {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X) :
    ∃ (𝒦 : Set (CTorus d L N₁ m₁ k)) (W : Finset (CTorus d L N₁ m₁ k))
      (E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k)),
      ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W := by
  classical
  obtain ⟨hne, ⟨𝒦, hK1, hK2⟩, hcon⟩ := hX
  obtain ⟨hcs, hWY⟩ := connStruct_nbrPairs hne hcon
  refine ⟨𝒦, _, _, ⟨hK1, hK2⟩, hcs, hWY.le, fun b hb => ?_⟩
  have hpos : 0 < L * cellSide L m₀ m₁ j := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L))
    (cellSide_pos m₀ m₁ j)
  refine ⟨b, ?_, mem_box_self b hpos⟩
  have : b ∈ X := (hK1 b hb).2 (mem_box_self b hpos)
  rw [← hWY] at this
  exact_mod_cast this

/-- **The covering size of a polymer is attained** by an admissible triple: the costs of the
admissible triples of the finite torus form a finite nonempty set. -/
theorem exists_opt_of_isPolyDom {m₀ j : ℕ} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X) :
    ∃ (𝒦 : Set (CTorus d L N₁ m₁ k)) (W : Finset (CTorus d L N₁ m₁ k))
      (E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k)),
      ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W ∧
        bondCost (scaleW L m₀ m₁ j) E = treeLenCovOne m₀ j X := by
  set S : Set ℝ := {x | ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧
    MeetsOne m₀ j 𝒦 W ∧ x = bondCost (scaleW L m₀ m₁ j) E} with hS
  have hne : S.Nonempty := by
    obtain ⟨𝒦, W, E, h1, h2, h3, h4⟩ := admissible_of_isPolyDom hX
    exact ⟨_, 𝒦, W, E, h1, h2, h3, h4, rfl⟩
  have hfin : S.Finite := by
    refine (Set.finite_range fun E : Finset (CTorus d L N₁ m₁ k × CTorus d L N₁ m₁ k) =>
      bondCost (scaleW L m₀ m₁ j) E).subset ?_
    rintro x ⟨-, -, E, -, -, -, -, rfl⟩
    exact ⟨E, rfl⟩
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, h5⟩ := hne.csInf_mem hfin
  exact ⟨𝒦, W, E, h1, h2, h3, h4, h5.symm⟩

end Balaban.SmallField.Def6
