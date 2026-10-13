/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RootPavingMap
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Localization.BlockCount
public import Balaban.Localization.MooreDegree
public import Balaban.Localization.P6ActiveHalo
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The canonical hull of a set of cut parameters (DETCAUCHY.md §3, package `DetCauchyHull`)

The localized expansion of the normalization factor assigns to a set `J` of cut parameters
(patches `Pset m₁ P`, of side `L ^ (P.1 + m₁)`) that is connected to a root cube a set of level-`K`
cubes (cells of side `a_K = L ^ (K + m₀ + m₁)`).  This file constructs that set of cubes and proves
the geometry that the bound `exp(-λ |J|) ≤ exp(-κ dExt(hull))` needs.

* `piHull m₀ S`: the level-`K` cubes contained in some aligned `π′_K` box (aligned at `a_K`, side
  `L a_K`) that meets the site set `S`.  `sitesOf (piHull m₀ S)` is the union of these boxes
  (`sitesOf_piHull`); it is a union of `π′_K` boxes (`chosenOne_piHull`), contains `S`
  (`subset_sitesOf_piHull`) and lies in the `L a_K`-neighbourhood of `S` (`exists_near_of_mem_piHull`).
* `hullOf m₀ z J`: the hull of the union of the root cube `rootCube z` and the patches of `J`.
* `RootConnected`: the Moore-touch graph on the patches of `J` and the root cube is connected.
* `isPolyDom_hullOf`: if `RootConnected`, the sites of the hull form a polymer (`IsPolyDom`) and
  `rootCube z ∈ hullOf z J`.
* `dExt_hullOf_le`: `dExt (hullOf z J) ≤ 2 d L · |J|`.
* `card_hullOf_le`, `hullOf_mono`: the hull has at most `L^(2d) (|J| + 1)` cubes and is monotone in `J`.
* `piHull_image`, `hullOf_covariant`: equivariance under the paving symmetries.

Assumptions: `L ^ m₀ ∣ N₁` (cells divide the torus), `2 ≤ L` (so that an aligned `π′_K` box contains
two cells in each direction), and `P.1 ≤ K` for the patches of `J`.  The torus is **not** assumed to
be wider than a `π′_K` box: when a box wraps around, it is the image of the box in the covering
lattice and all statements hold as stated.

This file makes no statement about the determinant, the cut differences or any coefficient.  Which
sets `J` occur (the support statement), the count of `J` per hull, the chart and the rates are
separate packages.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

section Hull

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- The bases of the aligned `π′_K` boxes (aligned at `a_K = L ^ (K + m₀ + m₁)`, side `L a_K`) that
meet the site set `S`. -/
def piBases (m₀ : ℕ) (S : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {b | Aligned (cellSide L m₀ m₁ K) b ∧ (box b (L * cellSide L m₀ m₁ K) ∩ S).Nonempty}

open Classical in
/-- **The `π′_K`-hull of a site set `S`.**  The set of level-`K` cubes (cells of side `a_K`) that
are contained in some aligned `π′_K` box (side `L a_K`, base aligned at `a_K`) meeting `S`. -/
noncomputable def piHull (m₀ : ℕ) (S : Set (CTorus d L N₁ m₁ K)) :
    Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :=
  Finset.univ.filter fun c =>
    ∃ b ∈ piBases m₀ S, box c.1 (cellSide L m₀ m₁ K) ⊆ box b (L * cellSide L m₀ m₁ K)

variable {m₀ : ℕ}

theorem mem_piHull {S : Set (CTorus d L N₁ m₁ K)}
    {c : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ} :
    c ∈ piHull m₀ S ↔
      ∃ b ∈ piBases m₀ S, box c.1 (cellSide L m₀ m₁ K) ⊆ box b (L * cellSide L m₀ m₁ K) := by
  classical
  simp [piHull]

theorem piHull_mono {S S' : Set (CTorus d L N₁ m₁ K)} (h : S ⊆ S') :
    piHull m₀ S ⊆ piHull m₀ S' := by
  intro c hc
  obtain ⟨b, ⟨hb, x, hx, hxS⟩, hcb⟩ := mem_piHull.1 hc
  exact mem_piHull.2 ⟨b, ⟨hb, x, hx, h hxS⟩, hcb⟩

theorem cellSide_le_mul : cellSide L m₀ m₁ K ≤ L * cellSide L m₀ m₁ K :=
  Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L))

theorem mul_cellSide_pos : 0 < L * cellSide L m₀ m₁ K :=
  Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ K)

/-- **T1.**  The sites of the hull are the union of the `π′_K` boxes meeting `S`. -/
theorem sitesOf_piHull (hN : L ^ m₀ ∣ N₁) (S : Set (CTorus d L N₁ m₁ K)) :
    sitesOf (piHull m₀ S) = ⋃ b ∈ piBases m₀ S, box b (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  ext z
  simp only [mem_sitesOf, Set.mem_iUnion]
  constructor
  · rintro ⟨c, hc, hz⟩
    obtain ⟨b, hb, hcb⟩ := mem_piHull.1 hc
    exact ⟨b, hb, hcb hz⟩
  · rintro ⟨b, hb, hz⟩
    refine ⟨⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z, Set.subset_univ _⟩, ?_,
      mem_box_cbase ha0 z⟩
    exact mem_piHull.2 ⟨b, hb, cell_subset_cube hdvd ha0 hb.1 hz⟩

/-- **T1.**  The sites of the hull are covered by the `π′_K` boxes meeting `S`, i.e. they form a
union of `π′_K` cubes with the chosen family `piBases m₀ S`. -/
theorem chosenOne_piHull (hN : L ^ m₀ ∣ N₁) (S : Set (CTorus d L N₁ m₁ K)) :
    ChosenOne (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K (sitesOf (piHull m₀ S))
      (piBases m₀ S) := by
  have h := sitesOf_piHull hN S
  refine ⟨fun b hb => ⟨hb.1, ?_⟩, fun z hz => ?_⟩
  · rw [h]; exact Set.subset_iUnion₂ (s := fun b (_ : b ∈ piBases m₀ S) =>
      box b (L * cellSide L m₀ m₁ K)) b hb
  · rw [h] at hz
    obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨b, hb, hzb⟩

/-- **T1.**  The hull contains `S`. -/
theorem subset_sitesOf_piHull (hN : L ^ m₀ ∣ N₁) (S : Set (CTorus d L N₁ m₁ K)) :
    S ⊆ sitesOf (piHull m₀ S) := by
  rw [sitesOf_piHull hN]
  intro s hs
  refine Set.mem_iUnion₂.2 ⟨cbase (cellSide L m₀ m₁ K) s, ⟨aligned_cbase s, s, ?_, hs⟩, ?_⟩
  · exact box_mono _ cellSide_le_mul (mem_box_cbase (cellSide_pos m₀ m₁ K) s)
  · exact box_mono _ cellSide_le_mul (mem_box_cbase (cellSide_pos m₀ m₁ K) s)

/-- **T1.**  Every site of the hull is within sup-distance `< L a_K` of `S`: there are `s ∈ S` and
coordinatewise natural numbers `u, v < L a_K` with `x + v = s + u` in the torus. -/
theorem exists_near_of_mem_piHull (hN : L ^ m₀ ∣ N₁) {S : Set (CTorus d L N₁ m₁ K)}
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ sitesOf (piHull m₀ S)) :
    ∃ s ∈ S, ∃ u v : Fin d → ℕ, (∀ μ, u μ < L * cellSide L m₀ m₁ K) ∧
      (∀ μ, v μ < L * cellSide L m₀ m₁ K) ∧ x + natT v = s + natT u := by
  rw [sitesOf_piHull hN] at hx
  obtain ⟨b, ⟨-, s, ⟨w', hw', hs⟩, hsS⟩, ⟨w, hw, hxw⟩⟩ := Set.mem_iUnion₂.1 hx
  refine ⟨s, hsS, w, w', hw, hw', ?_⟩
  rw [hxw, hs]; abel

end Hull

end Balaban.Fluctuation
