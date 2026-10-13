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


/-! ### Two Moore-touching sites lie in a common `π′_K` box -/

theorem exists_box_of_near (hL : 2 ≤ L) {x y : CTorus d L N₁ m₁ K} (h : Near 1 1 x y) :
    ∃ b, Aligned (cellSide L m₀ m₁ K) b ∧ x ∈ box b (L * cellSide L m₀ m₁ K) ∧
      y ∈ box b (L * cellSide L m₀ m₁ K) := by
  obtain ⟨q, hq, hy⟩ := near_one_iff.1 h
  have ha0 : 0 < cellSide L m₀ m₁ K := cellSide_pos m₀ m₁ K
  have h2a : 2 * cellSide L m₀ m₁ K ≤ L * cellSide L m₀ m₁ K := Nat.mul_le_mul_right _ hL
  let ε : Fin d → ℕ := fun μ => if q μ = -1 then 1 else 0
  let δ : Fin d → ℕ := fun μ => if q μ = 1 then 1 else 0
  let u : CTorus d L N₁ m₁ K := x - natT ε
  have hx : x = u + natT ε := by simp [u]
  have hyu : y = u + natT δ := by
    funext μ
    have hqμ := abs_le.1 (hq μ)
    simp only [Pi.add_apply, natT_apply, u, Pi.sub_apply, ε, δ]
    rw [hy μ]
    rcases (by omega : q μ = -1 ∨ q μ = 0 ∨ q μ = 1) with h | h | h
    · simp [h]; ring
    · simp [h]
    · simp [h]
  set b := cbase (cellSide L m₀ m₁ K) u with hb
  have hub : u = b + natT (fun μ => (u μ).val % cellSide L m₀ m₁ K) := by
    rw [hb, cbase_eq_sub]; abel
  refine ⟨b, aligned_cbase u, ?_, ?_⟩
  · refine ⟨(fun μ => (u μ).val % cellSide L m₀ m₁ K) + ε, fun μ => ?_, ?_⟩
    · have h1 := Nat.mod_lt (u μ).val ha0
      have h3 : ε μ ≤ 1 := by simp only [ε]; split_ifs <;> omega
      simp only [Pi.add_apply]; omega
    · rw [natT_add, ← add_assoc, ← hub, ← hx]
  · refine ⟨(fun μ => (u μ).val % cellSide L m₀ m₁ K) + δ, fun μ => ?_, ?_⟩
    · have h1 := Nat.mod_lt (u μ).val ha0
      have h3 : δ μ ≤ 1 := by simp only [δ]; split_ifs <;> omega
      simp only [Pi.add_apply]; omega
    · rw [natT_add, ← add_assoc, ← hub, ← hyu]

/-! ### Paths of controlled length in a box -/

/-- A box is connected from its corner with at most `∑ w` bonds: there is a connected structure
inside `R` containing `b` and `b + w`. -/
theorem pathStr_box {n : ℕ} (b : Torus d n) (w : Fin d → ℕ) (R : Set (Torus d n))
    (hR : ∀ w' : Fin d → ℕ, (∀ μ, w' μ ≤ w μ) → b + natT w' ∈ R) :
    ∃ (W : Finset (Torus d n)) (E : Finset (Torus d n × Torus d n)), ConnStruct W E ∧
      (↑W ⊆ R) ∧ b ∈ W ∧ b + natT w ∈ W ∧ E.card ≤ ∑ μ, w μ := by
  classical
  have key := chain_of_steps (d := d)
    (fun (m : ℕ) (x y : Torus d n) => ∃ (W : Finset (Torus d n))
      (E : Finset (Torus d n × Torus d n)), ConnStruct W E ∧ (↑W ⊆ R) ∧ x ∈ W ∧ y ∈ W ∧
        E.card ≤ m)
    (fun w' => b + natT w') ?_ ?_ (∑ μ, w μ) w rfl ?_
  · simpa [natT_zero] using key
  · refine ⟨{b + natT 0}, ∅, connStruct_singleton _, ?_, by simp, by simp, by simp⟩
    intro x hx
    rw [Finset.mem_coe, Finset.mem_singleton] at hx
    subst hx
    exact hR 0 (fun _ => Nat.zero_le _)
  · rintro m m' x y z ⟨W, E, h1, h2, h3, h4, h5⟩ ⟨W', E', h1', h2', h3', h4', h5'⟩
    refine ⟨W ∪ W', E ∪ E', h1.union h1' ⟨y, h4, h3'⟩, ?_, Finset.mem_union_left _ h3,
      Finset.mem_union_right _ h4', ?_⟩
    · intro t ht
      rcases Finset.mem_union.1 ht with ht | ht
      · exact h2 ht
      · exact h2' ht
    · exact (Finset.card_union_le _ _).trans (add_le_add h5 h5')
  · intro w' μ hw'
    have h1 : b + natT w' ∈ R := hR w' (fun ν => by
      have := hw' ν; simp only [Pi.add_apply] at this; omega)
    have h2 : b + natT (w' + Pi.single μ 1) ∈ R := hR _ (fun ν => hw' ν)
    have hn : Nbr (b + natT w') (b + natT (w' + Pi.single μ 1)) := by
      refine ⟨μ, Or.inl ?_⟩
      rw [natT_add, natT_single, add_assoc]
    refine ⟨{b + natT w', b + natT (w' + Pi.single μ 1)}, {(b + natT w', b + natT (w' + Pi.single μ 1))},
      connStruct_edge hn, ?_, by simp, by simp, by simp⟩
    intro t ht
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact h1
    · exact h2

/-! ### Links between touching sets -/

theorem anchor_mem_box (hN : L ^ m₀ ∣ N₁) {p : CTorus d L N₁ m₁ K}
    (hp : Aligned (cellSide L m₀ m₁ K) p) {A : Set (CTorus d L N₁ m₁ K)}
    (hAp : A ⊆ box p (cellSide L m₀ m₁ K)) {b : CTorus d L N₁ m₁ K}
    (hb : Aligned (cellSide L m₀ m₁ K) b) {x : CTorus d L N₁ m₁ K} (hx : x ∈ A)
    (hxb : x ∈ box b (L * cellSide L m₀ m₁ K)) : p ∈ box b (L * cellSide L m₀ m₁ K) := by
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  have h1 := cell_subset_cube hdvd ha0 hb hxb
  rw [cbase_eq_of_mem_box hdvd hp (hAp hx)] at h1
  exact h1 (mem_box_self p ha0)

/-- Two Moore-touching sets `A ⊆ S` and `B`, each inside one cell, are joined by a connected
structure with at most `2 d L a_K` bonds inside the hull of `S`, containing the two cell bases. -/
theorem exists_link (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {S A B : Set (CTorus d L N₁ m₁ K)}
    {pA pB : CTorus d L N₁ m₁ K} (hpA : Aligned (cellSide L m₀ m₁ K) pA)
    (hpB : Aligned (cellSide L m₀ m₁ K) pB) (hA : A ⊆ S)
    (hAp : A ⊆ box pA (cellSide L m₀ m₁ K)) (hBp : B ⊆ box pB (cellSide L m₀ m₁ K))
    (htouch : MooreTouch A B) :
    ∃ (W : Finset (CTorus d L N₁ m₁ K)) (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W E ∧ (↑W ⊆ sitesOf (piHull m₀ S)) ∧ pA ∈ W ∧ pB ∈ W ∧
        E.card ≤ 2 * d * (L * cellSide L m₀ m₁ K) := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := htouch
  obtain ⟨b, hb, hxb, hyb⟩ := exists_box_of_near (m₀ := m₀) hL hxy
  have hbS : b ∈ piBases m₀ S := ⟨hb, x, hxb, hA hx⟩
  have hβ : box b (L * cellSide L m₀ m₁ K) ⊆ sitesOf (piHull m₀ S) := by
    rw [sitesOf_piHull hN]
    exact Set.subset_iUnion₂ (s := fun b (_ : b ∈ piBases m₀ S) =>
      box b (L * cellSide L m₀ m₁ K)) b hbS
  obtain ⟨wA, hwA, hA'⟩ := anchor_mem_box hN hpA hAp hb hx hxb
  obtain ⟨wB, hwB, hB'⟩ := anchor_mem_box hN hpB hBp hb hy hyb
  obtain ⟨W₁, E₁, c1, s1, b1, p1, e1⟩ := pathStr_box b wA (box b (L * cellSide L m₀ m₁ K))
    (fun w' hw' => mem_box_add b (fun μ => lt_of_le_of_lt (hw' μ) (hwA μ)))
  obtain ⟨W₂, E₂, c2, s2, b2, p2, e2⟩ := pathStr_box b wB (box b (L * cellSide L m₀ m₁ K))
    (fun w' hw' => mem_box_add b (fun μ => lt_of_le_of_lt (hw' μ) (hwB μ)))
  refine ⟨W₁ ∪ W₂, E₁ ∪ E₂, c1.union c2 ⟨b, b1, b2⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · exact hβ (s1 ht)
    · exact hβ (s2 ht)
  · exact Finset.mem_union_left _ (hA' ▸ p1)
  · exact Finset.mem_union_right _ (hB' ▸ p2)
  · have hsA : ∑ μ, wA μ ≤ d * (L * cellSide L m₀ m₁ K) := by
      calc ∑ μ, wA μ ≤ ∑ _μ : Fin d, (L * cellSide L m₀ m₁ K) :=
            Finset.sum_le_sum fun μ _ => (hwA μ).le
        _ = d * (L * cellSide L m₀ m₁ K) := by simp
    have hsB : ∑ μ, wB μ ≤ d * (L * cellSide L m₀ m₁ K) := by
      calc ∑ μ, wB μ ≤ ∑ _μ : Fin d, (L * cellSide L m₀ m₁ K) :=
            Finset.sum_le_sum fun μ _ => (hwB μ).le
        _ = d * (L * cellSide L m₀ m₁ K) := by simp
    calc (E₁ ∪ E₂).card ≤ E₁.card + E₂.card := Finset.card_union_le _ _
      _ ≤ d * (L * cellSide L m₀ m₁ K) + d * (L * cellSide L m₀ m₁ K) :=
          add_le_add (e1.trans hsA) (e2.trans hsB)
      _ = 2 * d * (L * cellSide L m₀ m₁ K) := by ring

/-! ### The hull of the root cube and the patches of `J` -/

variable (m₀) in
/-- The sites of the root cube `rootCube z` (the cell of side `a_K` containing the root site). -/
def rootSet (z : RootIdx d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  box (rootCube (m₀ := m₀) z).1 (cellSide L m₀ m₁ K)

variable (m₀) in
/-- The union of the root cube and of the patches `Pset m₁ P`, `P ∈ J`. -/
def hullSet (z : RootIdx d L N₁ m₁ K) (J : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    Set (CTorus d L N₁ m₁ K) :=
  rootSet m₀ z ∪ ⋃ P ∈ J, Pset m₁ P

variable (m₀) in
/-- **The hull of `(z, J)`.**  The `π′_K`-hull (`piHull`) of the union of the root cube `rootCube z`
and the patches `Pset m₁ P`, `P ∈ J`: the level-`K` cubes contained in an aligned `π′_K` box that
meets the root cube or a patch of `J`. -/
noncomputable def hullOf (z : RootIdx d L N₁ m₁ K) (J : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ) :=
  piHull m₀ (hullSet m₀ z J)

/-- The nodes of the Moore-touch graph: the root (`none`) and the patches of `J` (`some P`). -/
def JNode (J : Finset (ℕ × CTorus d L N₁ m₁ K)) (A : Option (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  A = none ∨ ∃ P ∈ J, A = some P

variable (m₀) in
/-- The set of sites of a node: the root cube, or the patch. -/
def nodeSet (z : RootIdx d L N₁ m₁ K) :
    Option (ℕ × CTorus d L N₁ m₁ K) → Set (CTorus d L N₁ m₁ K)
  | none => rootSet m₀ z
  | some P => Pset m₁ P

variable (m₀) in
/-- The base of the cell of side `a_K` that contains the node. -/
def nodeAnchor (z : RootIdx d L N₁ m₁ K) :
    Option (ℕ × CTorus d L N₁ m₁ K) → CTorus d L N₁ m₁ K
  | none => (rootCube (m₀ := m₀) z).1
  | some P => cbase (cellSide L m₀ m₁ K) P.2

variable (m₀) in
/-- **Connectedness to the root.**  Every patch of `J` is joined to the root cube by a chain of
sets (the root cube and patches of `J`) in which consecutive sets Moore-touch (`MooreTouch`, i.e.
some two of their sites differ by at most one in every coordinate).  Equivalently the Moore-touch
graph on `J` together with the root cube is connected. -/
def RootConnected (z : RootIdx d L N₁ m₁ K) (J : Finset (ℕ × CTorus d L N₁ m₁ K)) : Prop :=
  ∀ P ∈ J, Relation.ReflTransGen
    (fun A B : Option (ℕ × CTorus d L N₁ m₁ K) =>
      JNode J A ∧ JNode J B ∧ MooreTouch (nodeSet m₀ z A) (nodeSet m₀ z B)) none (some P)

theorem rootConnected_empty (z : RootIdx d L N₁ m₁ K) : RootConnected m₀ z ∅ := by
  intro P hP; exact absurd hP (Finset.notMem_empty P)

theorem mem_hullSet {z : RootIdx d L N₁ m₁ K} {J : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {x : CTorus d L N₁ m₁ K} :
    x ∈ hullSet m₀ z J ↔ ∃ A, JNode J A ∧ x ∈ nodeSet m₀ z A := by
  constructor
  · rintro (h | h)
    · exact ⟨none, Or.inl rfl, h⟩
    · obtain ⟨P, hP, hx⟩ := Set.mem_iUnion₂.1 h
      exact ⟨some P, Or.inr ⟨P, hP, rfl⟩, hx⟩
  · rintro ⟨A, hA | ⟨P, hP, rfl⟩, hx⟩
    · subst hA; exact Or.inl hx
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨P, hP, hx⟩)

theorem nodeSet_subset_hullSet {z : RootIdx d L N₁ m₁ K} {J : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {A : Option (ℕ × CTorus d L N₁ m₁ K)} (hA : JNode J A) :
    nodeSet m₀ z A ⊆ hullSet m₀ z J := fun _ hx => mem_hullSet.2 ⟨A, hA, hx⟩

theorem nodeSet_subset_box {z : RootIdx d L N₁ m₁ K} {J : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hJK : ∀ P ∈ J, P.1 ≤ K) {A : Option (ℕ × CTorus d L N₁ m₁ K)} (hA : JNode J A) :
    nodeSet m₀ z A ⊆ box (nodeAnchor m₀ z A) (cellSide L m₀ m₁ K) := by
  rcases hA with rfl | ⟨P, hP, rfl⟩
  · exact Set.Subset.rfl
  · exact Pset_subset_topCell m₀ (hJK P hP)

theorem nodeAnchor_aligned (z : RootIdx d L N₁ m₁ K) (A : Option (ℕ × CTorus d L N₁ m₁ K)) :
    Aligned (cellSide L m₀ m₁ K) (nodeAnchor m₀ z A) := by
  cases A with
  | none => exact (rootCube (m₀ := m₀) z).2.1
  | some P => exact aligned_cbase P.2

theorem nodeSet_nonempty (z : RootIdx d L N₁ m₁ K) (A : Option (ℕ × CTorus d L N₁ m₁ K)) :
    (nodeSet m₀ z A).Nonempty := by
  cases A with
  | none => exact ⟨_, mem_box_self _ (cellSide_pos m₀ m₁ K)⟩
  | some P => exact ⟨P.2, self_mem_Pset P⟩

/-- **T2 (root).**  The root cube belongs to the hull. -/
theorem rootCube_mem_hullOf (z : RootIdx d L N₁ m₁ K) (J : Finset (ℕ × CTorus d L N₁ m₁ K)) :
    rootCube (m₀ := m₀) z ∈ hullOf m₀ z J := by
  refine mem_piHull.2 ⟨(rootCube (m₀ := m₀) z).1, ⟨(rootCube (m₀ := m₀) z).2.1,
    (rootCube (m₀ := m₀) z).1, mem_box_self _ mul_cellSide_pos, Or.inl (mem_box_self _
      (cellSide_pos m₀ m₁ K))⟩, box_mono _ cellSide_le_mul⟩

/-- **T4.**  The hull is monotone in `J`. -/
theorem hullOf_mono (z : RootIdx d L N₁ m₁ K) {J J' : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (h : J ⊆ J') : hullOf m₀ z J ⊆ hullOf m₀ z J' := by
  refine piHull_mono (fun x hx => ?_)
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 hx
    exact Or.inr (Set.mem_iUnion₂.2 ⟨P, h hP, hxP⟩)

/-- A `π′_K` box meeting the root cube or a patch of `J` contains the base of the cell of that
node. -/
theorem exists_node_of_piBases (hN : L ^ m₀ ∣ N₁) {z : RootIdx d L N₁ m₁ K}
    {J : Finset (ℕ × CTorus d L N₁ m₁ K)} (hJK : ∀ P ∈ J, P.1 ≤ K)
    {b : CTorus d L N₁ m₁ K} (hb : b ∈ piBases m₀ (hullSet m₀ z J)) :
    ∃ A, JNode J A ∧ nodeAnchor m₀ z A ∈ box b (L * cellSide L m₀ m₁ K) := by
  obtain ⟨hba, s, hsb, hs⟩ := hb
  obtain ⟨A, hA, hsA⟩ := mem_hullSet.1 hs
  exact ⟨A, hA, anchor_mem_box hN (nodeAnchor_aligned z A) (nodeSet_subset_box hJK hA) hba hsA
    hsb⟩

theorem nodeAnchor_mem_sitesOf (hN : L ^ m₀ ∣ N₁) {z : RootIdx d L N₁ m₁ K}
    {J : Finset (ℕ × CTorus d L N₁ m₁ K)} (hJK : ∀ P ∈ J, P.1 ≤ K)
    {A : Option (ℕ × CTorus d L N₁ m₁ K)} (hA : JNode J A) :
    nodeAnchor m₀ z A ∈ sitesOf (hullOf m₀ z J) := by
  obtain ⟨x, hx⟩ := nodeSet_nonempty (m₀ := m₀) z A
  have hb : nodeAnchor m₀ z A ∈ piBases m₀ (hullSet m₀ z J) :=
    ⟨nodeAnchor_aligned z A, x, box_mono _ cellSide_le_mul (nodeSet_subset_box hJK hA hx),
      nodeSet_subset_hullSet hA hx⟩
  unfold hullOf
  rw [sitesOf_piHull hN]
  exact Set.mem_iUnion₂.2 ⟨_, hb, mem_box_self _ mul_cellSide_pos⟩

/-- **The connected structure through the hull.**  If `(z, J)` is connected to the root, there is a
connected lattice structure inside the sites of the hull that contains the cell base of the root
and of every patch of `J` and has at most `|J| · 2 d L a_K` bonds. -/
theorem exists_connStruct_hullOf (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (z : RootIdx d L N₁ m₁ K)
    (J : Finset (ℕ × CTorus d L N₁ m₁ K)) (hJK : ∀ P ∈ J, P.1 ≤ K)
    (hconn : RootConnected m₀ z J) :
    ∃ (W : Finset (CTorus d L N₁ m₁ K)) (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W E ∧ (↑W ⊆ sitesOf (hullOf m₀ z J)) ∧
        (∀ A, JNode J A → nodeAnchor m₀ z A ∈ W) ∧
        E.card ≤ J.card * (2 * d * (L * cellSide L m₀ m₁ K)) := by
  classical
  set ℓ := 2 * d * (L * cellSide L m₀ m₁ K) with hℓ
  let F : Finset (Option (ℕ × CTorus d L N₁ m₁ K)) := insert none (J.image some)
  have hF : ∀ A, A ∈ F ↔ JNode J A := by
    intro A
    simp only [F, Finset.mem_insert, Finset.mem_image, JNode]
    constructor
    · rintro (h | ⟨P, hP, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨P, hP, rfl⟩
    · rintro (h | ⟨P, hP, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨P, hP, rfl⟩
  have hFcard : F.card ≤ J.card + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  have key : ∀ n : ℕ, ∀ Z : Finset (Option (ℕ × CTorus d L N₁ m₁ K)), Z ⊆ F → none ∈ Z →
      (F \ Z).card = n →
      (∃ (W : Finset (CTorus d L N₁ m₁ K))
          (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
        ConnStruct W E ∧ (↑W ⊆ sitesOf (hullOf m₀ z J)) ∧
          (∀ A ∈ Z, nodeAnchor m₀ z A ∈ W) ∧ E.card ≤ (Z.card - 1) * ℓ) →
      ∃ (W : Finset (CTorus d L N₁ m₁ K))
          (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
        ConnStruct W E ∧ (↑W ⊆ sitesOf (hullOf m₀ z J)) ∧
          (∀ A ∈ F, nodeAnchor m₀ z A ∈ W) ∧ E.card ≤ (F.card - 1) * ℓ := by
    intro n
    induction n with
    | zero =>
      intro Z hZF _ hcard hinv
      have hFZ : F ⊆ Z := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hcard)
      have hZ : Z = F := Finset.Subset.antisymm hZF hFZ
      subst hZ; exact hinv
    | succ n ih =>
      intro Z hZF hnone hcard hinv
      obtain ⟨W, E, hc, hWX, hWanc, hE⟩ := hinv
      obtain ⟨A, hAF, hAZ, B, hBZ, htouch⟩ : ∃ A ∈ F, A ∉ Z ∧ ∃ B ∈ Z,
          MooreTouch (nodeSet m₀ z A) (nodeSet m₀ z B) := by
        have hne : (F \ Z).Nonempty := Finset.card_pos.1 (by omega)
        obtain ⟨A₀, hA₀⟩ := hne
        rw [Finset.mem_sdiff] at hA₀
        rcases (hF A₀).1 hA₀.1 with rfl | ⟨P, hP, rfl⟩
        · exact absurd hnone hA₀.2
        · have chain : ∀ A', Relation.ReflTransGen
              (fun A B : Option (ℕ × CTorus d L N₁ m₁ K) =>
                JNode J A ∧ JNode J B ∧ MooreTouch (nodeSet m₀ z A) (nodeSet m₀ z B)) none A' →
              A' ∈ Z ∨ ∃ A ∈ F, A ∉ Z ∧ ∃ B ∈ Z,
                MooreTouch (nodeSet m₀ z A) (nodeSet m₀ z B) := by
            intro A' h
            induction h with
            | refl => exact Or.inl hnone
            | @tail b c _ hbc ih =>
              rcases ih with hb | hex
              · by_cases hc' : c ∈ Z
                · exact Or.inl hc'
                · exact Or.inr ⟨c, (hF c).2 hbc.2.1, hc', b, hb, hbc.2.2.symm⟩
              · exact Or.inr hex
          rcases chain _ (hconn P hP) with h | h
          · exact absurd h hA₀.2
          · exact h
      have hAJ := (hF A).1 hAF
      have hBJ := (hF B).1 (hZF hBZ)
      obtain ⟨W', E', hc', hW'X, hpA, hpB, hE'⟩ := exists_link (m₀ := m₀) hN hL
        (nodeAnchor_aligned z A) (nodeAnchor_aligned z B) (nodeSet_subset_hullSet hAJ)
        (nodeSet_subset_box hJK hAJ) (nodeSet_subset_box hJK hBJ) htouch
      obtain ⟨k, hk⟩ : ∃ k, Z.card = k + 1 :=
        ⟨Z.card - 1, by have := Finset.card_pos.2 ⟨none, hnone⟩; omega⟩
      refine ih (insert A Z) (Finset.insert_subset hAF hZF) (Finset.mem_insert_of_mem hnone) ?_
        ⟨W ∪ W', E ∪ E', hc.union hc' ⟨_, hWanc B hBZ, hpB⟩, ?_, ?_, ?_⟩
      · rw [Finset.sdiff_insert, Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hAF, hAZ⟩), hcard]
        rfl
      · intro t ht
        rcases Finset.mem_union.1 ht with ht | ht
        · exact hWX ht
        · exact hW'X ht
      · intro A'' hA''
        rcases Finset.mem_insert.1 hA'' with rfl | h
        · exact Finset.mem_union_right _ hpA
        · exact Finset.mem_union_left _ (hWanc _ h)
      · have hE2 : E.card ≤ k * ℓ := by rw [hk] at hE; simpa using hE
        rw [Finset.card_insert_of_notMem hAZ, hk]
        simp only [Nat.add_sub_cancel]
        calc (E ∪ E').card ≤ E.card + E'.card := Finset.card_union_le _ _
          _ ≤ k * ℓ + ℓ := add_le_add hE2 hE'
          _ = (k + 1) * ℓ := by ring
  have hnodeF : ∀ A ∈ F, nodeAnchor m₀ z A ∈ sitesOf (hullOf m₀ z J) := fun A hA =>
    nodeAnchor_mem_sitesOf hN hJK ((hF A).1 hA)
  have hbase : ∃ (W : Finset (CTorus d L N₁ m₁ K))
      (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W E ∧ (↑W ⊆ sitesOf (hullOf m₀ z J)) ∧
        (∀ A ∈ ({none} : Finset (Option (ℕ × CTorus d L N₁ m₁ K))), nodeAnchor m₀ z A ∈ W) ∧
        E.card ≤ (({none} : Finset (Option (ℕ × CTorus d L N₁ m₁ K))).card - 1) * ℓ := by
    refine ⟨{nodeAnchor m₀ z none}, ∅, connStruct_singleton _, ?_, ?_, by simp⟩
    · intro t ht
      rw [Finset.mem_coe, Finset.mem_singleton] at ht
      subst ht
      exact hnodeF none ((hF none).2 (Or.inl rfl))
    · intro A hA
      rw [Finset.mem_singleton] at hA
      subst hA; exact Finset.mem_singleton_self _
  obtain ⟨W, E, hc, hWX, hWanc, hE⟩ := key (F \ {none}).card {none}
    (Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)) (Finset.mem_singleton_self _) rfl
    hbase
  refine ⟨W, E, hc, hWX, fun A hA => hWanc A ((hF A).2 hA), ?_⟩
  calc E.card ≤ (F.card - 1) * ℓ := hE
    _ ≤ J.card * ℓ := Nat.mul_le_mul_right _ (by omega)

/-- **T2.**  If the root cube and the patches of `J` are connected for Moore adjacency, the sites of
the hull form a polymer: a nonempty, nearest-neighbour connected union of `π′_K` cubes. -/
theorem isPolyDom_hullOf (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (z : RootIdx d L N₁ m₁ K)
    (J : Finset (ℕ × CTorus d L N₁ m₁ K)) (hJK : ∀ P ∈ J, P.1 ≤ K)
    (hconn : RootConnected m₀ z J) : IsPolyDom m₀ K (sitesOf (hullOf m₀ z J)) := by
  obtain ⟨W, E, hc, hWX, hWanc, -⟩ := exists_connStruct_hullOf hN hL z J hJK hconn
  set X := sitesOf (hullOf m₀ z J) with hX
  have hsymm : ∀ a b : CTorus d L N₁ m₁ K, (a ∈ X ∧ b ∈ X ∧ Nbr a b) → (b ∈ X ∧ a ∈ X ∧ Nbr b a) :=
    fun a b h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have hbox : ∀ b ∈ piBases m₀ (hullSet m₀ z J), ∀ x ∈ box b (L * cellSide L m₀ m₁ K),
      Relation.ReflTransGen (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) b x := by
    intro b hb x hx
    have hβ : box b (L * cellSide L m₀ m₁ K) ⊆ X := by
      rw [hX, hullOf, sitesOf_piHull hN]
      exact Set.subset_iUnion₂ (s := fun b (_ : b ∈ piBases m₀ (hullSet m₀ z J)) =>
        box b (L * cellSide L m₀ m₁ K)) b hb
    obtain ⟨w, hw, rfl⟩ := hx
    have := reach_box b w (box b (L * cellSide L m₀ m₁ K))
      (fun w' hw' => mem_box_add b (fun μ => lt_of_le_of_lt (hw' μ) (hw μ)))
    exact Relation.ReflTransGen.mono (fun a c h => ⟨hβ h.2.1, hβ h.2.2, h.1.2⟩) _ _ this
  have hanc : ∀ x ∈ X, ∃ A, JNode J A ∧ Relation.ReflTransGen
      (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) x (nodeAnchor m₀ z A) := by
    intro x hx
    rw [hX, hullOf, sitesOf_piHull hN] at hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨A, hA, hAb⟩ := exists_node_of_piBases hN hJK hb
    exact ⟨A, hA, (rtg_symm hsymm (hbox b hb x hxb)).trans (hbox b hb _ hAb)⟩
  have hstruct : ∀ A B, JNode J A → JNode J B → Relation.ReflTransGen
      (fun a b => a ∈ X ∧ b ∈ X ∧ Nbr a b) (nodeAnchor m₀ z A) (nodeAnchor m₀ z B) := by
    intro A B hA hB
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _
      (hc.2.2 _ (hWanc A hA) _ (hWanc B hB))
    rcases hab with hab | hab
    · obtain ⟨h1, h2, h3⟩ := hc.2.1 _ hab
      exact ⟨hWX h1, hWX h2, h3⟩
    · obtain ⟨h1, h2, h3⟩ := hc.2.1 _ hab
      exact ⟨hWX h2, hWX h1, h3.symm⟩
  refine ⟨⟨_, nodeAnchor_mem_sitesOf hN hJK (Or.inl rfl : JNode J none)⟩,
    ⟨_, chosenOne_piHull hN _⟩, fun x hx y hy => ?_⟩
  obtain ⟨A, hA, hxA⟩ := hanc x hx
  obtain ⟨B, hB, hyB⟩ := hanc y hy
  exact (hxA.trans (hstruct A B hA hB)).trans (rtg_symm hsymm hyB)

/-- **T3 (size, (8)).**  If `(z, J)` is connected to the root,
`dExt (hullOf z J) ≤ 2 d L · |J| + 0`.  The slope `2 d L` and the constant term `0` depend only on
`d` and `L`; they do not depend on `K`, `m₀`, the torus, or the layers of the patches. -/
theorem dExt_hullOf_le (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) (z : RootIdx d L N₁ m₁ K)
    (J : Finset (ℕ × CTorus d L N₁ m₁ K)) (hJK : ∀ P ∈ J, P.1 ≤ K)
    (hconn : RootConnected m₀ z J) :
    dExt (hullOf m₀ z J) ≤ (2 * d * L : ℝ) * J.card + 0 := by
  classical
  have hpoly := isPolyDom_hullOf hN hL z J hJK hconn
  obtain ⟨W, E, hc, hWX, hWanc, hE⟩ := exists_connStruct_hullOf hN hL z J hJK hconn
  have hmeet : MeetsOne m₀ K (piBases m₀ (hullSet m₀ z J)) W := by
    intro b hb
    obtain ⟨A, hA, hAb⟩ := exists_node_of_piBases hN hJK hb
    exact ⟨_, hWanc A hA, hAb⟩
  rw [dExt_eq_sizeJ_of_isPolyDom hpoly]
  have h1 := treeLenCovOne_le_of_chosen (chosenOne_piHull hN (hullSet m₀ z J)) hc hWX hmeet
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hpos : (0 : ℝ) < (L : ℝ) ^ (m₀ + m₁ + K) := by positivity
  have hcost : bondCost (scaleW L m₀ m₁ K) E = (E.card : ℝ) / (L : ℝ) ^ (m₀ + m₁ + K) := by
    unfold bondCost scaleW
    simp [Finset.sum_const, div_eq_mul_inv]
  have ha : ((cellSide L m₀ m₁ K : ℕ) : ℝ) = (L : ℝ) ^ (m₀ + m₁ + K) := by
    unfold cellSide; push_cast; rw [show K + m₀ + m₁ = m₀ + m₁ + K by omega]
  have hEr : (E.card : ℝ) ≤ J.card * (2 * d * (L * (L : ℝ) ^ (m₀ + m₁ + K))) := by
    have := (Nat.cast_le (α := ℝ)).2 hE
    push_cast at this
    rwa [ha] at this
  have h2 : sizeJ m₀ K (sitesOf (hullOf m₀ z J)) ≤ bondCost (scaleW L m₀ m₁ K) E := h1
  refine h2.trans ?_
  rw [hcost, div_le_iff₀ hpos]
  nlinarith

/-- **T4.**  The hull has at most `L ^ (2 d) (|J| + 1)` cubes (this needs no connectedness). -/
theorem card_hullOf_le (hN : L ^ m₀ ∣ N₁) (z : RootIdx d L N₁ m₁ K)
    (J : Finset (ℕ × CTorus d L N₁ m₁ K)) (hJK : ∀ P ∈ J, P.1 ≤ K) :
    (hullOf m₀ z J).card ≤ L ^ d * L ^ d * (J.card + 1) := by
  classical
  have hdvd := cellSide_dvd (K := K) (m₁ := m₁) hN (le_refl K)
  have ha0 := cellSide_pos (L := L) m₀ m₁ K
  set X := sitesOf (hullOf m₀ z J) with hX
  let F : Finset (Option (ℕ × CTorus d L N₁ m₁ K)) := insert none (J.image some)
  have hFcard : F.card ≤ J.card + 1 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
  have hinj : (hullOf m₀ z J).card ≤ cellCount (cellSide L m₀ m₁ K) X := by
    unfold cellCount
    refine Finset.card_le_card_of_injOn (fun b => b.1) (fun b hb => ?_)
      (fun a _ b _ h => Subtype.ext h)
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, b.2.1, fun y hy => mem_sitesOf.2 ⟨b, hb, hy⟩⟩
  have hch := chosenOne_piHull (m₀ := m₀) hN (hullSet m₀ z J)
  have hmeet : ∀ b ∈ piBases m₀ (hullSet m₀ z J),
      ∃ x ∈ F.image (nodeAnchor m₀ z), x ∈ box b (L * cellSide L m₀ m₁ K) := by
    intro b hb
    obtain ⟨A, hA, hAb⟩ := exists_node_of_piBases hN hJK hb
    refine ⟨_, Finset.mem_image_of_mem _ ?_, hAb⟩
    simp only [F, Finset.mem_insert, Finset.mem_image]
    rcases hA with h | ⟨P, hP, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨P, hP, rfl⟩
  have h3 := cellCount_le hdvd ha0 (fun b hb => hb.1) hch.2 hmeet
  calc (hullOf m₀ z J).card ≤ cellCount (cellSide L m₀ m₁ K) X := hinj
    _ ≤ L ^ d * L ^ d * ((F.image (nodeAnchor m₀ z)).image (cbase (cellSide L m₀ m₁ K))).card :=
        h3
    _ ≤ L ^ d * L ^ d * (J.card + 1) := by
        refine Nat.mul_le_mul_left _ ?_
        exact Finset.card_image_le.trans (Finset.card_image_le.trans hFcard)

end Hull

end Balaban.Fluctuation
