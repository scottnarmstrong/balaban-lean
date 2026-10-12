/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvIdentity
import Mathlib.Tactic.Ring

/-!
# Additivity over disjoint regions (P631 §3: "regional block, bond and mass sums are additive
under the half-bond convention, including their interface allocation")

For pairwise disjoint regions `R i` (finite unions of cubes), the restricted action `A_D`, the
counterterm `C_D` and the surface term `S_D` of the union are the sums over `i`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

namespace Region

/-- The empty region. -/
def bot : Region G where
  sites := ∅
  sub_Ω := Finset.empty_subset _
  blockClosed := fun x hx => by simp at hx

/-- The union of a finite family of regions. -/
noncomputable def iUnion {ι : Type*} [DecidableEq ι] (s : Finset ι) (R : ι → Region G) :
    Region G where
  sites := s.biUnion fun i => (R i).sites
  sub_Ω := Finset.biUnion_subset.2 fun i _ => (R i).sub_Ω
  blockClosed := fun x hx y hy => by
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨i, hi, (R i).blockClosed x hxi y hy⟩

/-- The union of two regions. -/
def sup (D E : Region G) : Region G where
  sites := D.sites ∪ E.sites
  sub_Ω := Finset.union_subset D.sub_Ω E.sub_Ω
  blockClosed := fun x hx y hy => by
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_union_left _ (D.blockClosed x h y hy)
    · exact Finset.mem_union_right _ (E.blockClosed x h y hy)

/-- A functional of regions is additive over disjoint unions. -/
def IsAdditive (F : Region G → ℂ) : Prop :=
  ∀ D E : Region G, Disjoint D.sites E.sites → F (D.sup E) = F D + F E

theorem IsAdditive.bot {F : Region G → ℂ} (hF : IsAdditive F) : F Region.bot = 0 := by
  have := hF Region.bot Region.bot (by simp [Region.bot])
  have e : (Region.bot : Region G).sup Region.bot = Region.bot := by
    ext1; simp [Region.sup, Region.bot]
  rw [e] at this
  linear_combination -this

theorem IsAdditive.iUnion {F : Region G → ℂ} (hF : IsAdditive F) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (R : ι → Region G)
    (hd : (s : Set ι).PairwiseDisjoint fun i => (R i).sites) :
    F (Region.iUnion s R) = ∑ i ∈ s, F (R i) := by
  induction s using Finset.induction_on with
  | empty =>
    have e : Region.iUnion (∅ : Finset ι) R = Region.bot := by
      ext1; simp [Region.iUnion, Region.bot]
    rw [e, hF.bot]; simp
  | insert a s ha ih =>
    have e : Region.iUnion (insert a s) R = (R a).sup (Region.iUnion s R) := by
      ext1; simp [Region.iUnion, Region.sup, Finset.biUnion_insert]
    have hd' : (s : Set ι).PairwiseDisjoint fun i => (R i).sites :=
      hd.subset (by simp)
    rw [e, hF _ _ ?_, ih hd', Finset.sum_insert ha]
    simp only [Region.iUnion]
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hd (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

/-- The union of regions with the given sites, for functionals depending on the sites only. -/
theorem eq_iUnion_of_sites {ι : Type*} [DecidableEq ι] (s : Finset ι) (R : ι → Region G)
    (X : Region G) (h : X.sites = s.biUnion fun i => (R i).sites) :
    X = Region.iUnion s R := by
  ext1; exact h

theorem starWeight_sup (D E : Region G) (hd : Disjoint D.sites E.sites)
    (x : Torus d (N₀ * L ^ K)) (μ : Fin d) :
    (D.sup E).starWeight x μ = D.starWeight x μ + E.starWeight x μ := by
  have h1 : ∀ y, (if y ∈ (D.sup E).sites then (1 : ℝ) else 0) =
      (if y ∈ D.sites then 1 else 0) + (if y ∈ E.sites then 1 else 0) := fun y => by
    simp only [Region.sup, Finset.mem_union]
    by_cases h : y ∈ D.sites
    · have : y ∉ E.sites := fun h' => Finset.disjoint_left.1 hd h h'
      simp [h, this]
    · by_cases h' : y ∈ E.sites <;> simp [h, h']
  unfold starWeight
  rw [h1 x, h1 (x + Pi.single μ 1)]
  ring

theorem blockPair_additive (a : ℕ → ℝ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    IsAdditive fun D : Region G => D.blockPair a p q := fun D E hd => by
  unfold blockPair
  show ∑ x ∈ D.sites ∪ E.sites, _ = _
  rw [Finset.sum_union hd]

theorem massPair_additive (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    IsAdditive fun D : Region G => D.massPair p q := fun D E hd => by
  unfold massPair
  show ∑ x ∈ D.sites ∪ E.sites, _ = _
  rw [Finset.sum_union hd]

theorem sitePair_additive (α : G.Ω 1 → ℂ) (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    IsAdditive fun D : Region G => D.sitePair α p q := fun D E hd => by
  unfold sitePair
  show ∑ x ∈ D.sites ∪ E.sites, _ = _
  rw [Finset.sum_union hd]

theorem bondPair_additive (p q : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    IsAdditive fun D : Region G => D.bondPair p q := fun D E hd => by
  unfold bondPair
  simp only [starWeight_sup D E hd, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]

theorem starPair_additive (w f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    IsAdditive fun D : Region G => D.starPair w f := fun D E hd => by
  have g := fun D : Region G => bondPair_green D w f
  have e1 := bondPair_additive (G := G) w f D E hd
  have e2 := massPair_additive (G := G) w (fun x i => negLap (fun y => f y i) x) D E hd
  have gD := g D
  have gE := g E
  have gS := g (D.sup E)
  simp only at e1 e2
  linear_combination e1 - e2 - (gS - gD - gE)

theorem IsAdditive.add {F H : Region G → ℂ} (hF : IsAdditive F) (hH : IsAdditive H) :
    IsAdditive fun D => F D + H D := fun D E hd => by
  simp only [hF D E hd, hH D E hd]; ring

theorem IsAdditive.const_mul {F : Region G → ℂ} (hF : IsAdditive F) (c : ℂ) :
    IsAdditive fun D => c * F D := fun D E hd => by
  simp only [hF D E hd]; ring

theorem actionRegionC_additive (a : ℕ → ℝ) (ν : ℝ) (Dat : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) :
    IsAdditive fun D : Region G => actionRegionC D a ν Dat φ := by
  unfold actionRegionC
  exact ((blockPair_additive a _ _).const_mul _).add ((bondPair_additive _ _).const_mul _)
    |>.add ((massPair_additive _ _).const_mul _)

theorem counterC_additive (a : ℕ → ℝ) (ν β b e : ℝ) (Dat Du : BgData G N)
    (φ φu : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) (br : MassBranch) :
    IsAdditive fun D : Region G => counterC D a ν β b e Dat Du φ φu α br := by
  unfold counterC counterP counterQ counterR
  refine IsAdditive.add (IsAdditive.add ?_ ?_) ?_
  · exact (((blockPair_additive a _ _).add ((bondPair_additive _ _).const_mul _)).add
      ((massPair_additive _ _).const_mul _))
  · exact (((blockPair_additive a _ _).const_mul _).add
      (((bondPair_additive _ _).add (sitePair_additive α _ _)).const_mul _)).add
      ((massPair_additive _ _).const_mul _)
  · exact (((massPair_additive _ _).const_mul _).add ((massPair_additive _ _).const_mul _)).add
      ((massPair_additive _ _).const_mul _)

end Region

end Balaban.LargeField.ActionConv
