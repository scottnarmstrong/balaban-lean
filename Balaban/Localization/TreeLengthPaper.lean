/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthCov
public import Balaban.Fluctuation.SizeModCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The papers' size `d_j(X)` against the chosen-cover size `treeLenCovOne`

P1 (2.26)-(2.27): `d_j(X)` is the length (in units of the cell side) of the shortest tree meeting
*every* `π'_j`-cube contained in the domain `X ∈ 𝒟_j`.  The landed `treeLenCovOne` also minimizes
over a chosen family of cubes covering `X`.

* `fullCover`: the family of all aligned cover cubes contained in `X`.
* `treeLenAll`: the papers' size.
* `fullCover_chosen`: `fullCover` is a chosen family of a domain.
* `treeLenCovOne_le_treeLenAll`: `treeLenCovOne ≤ treeLenAll`.
* `treeLenAll_le`: `treeLenAll ≤ (1 + 2 d L c₁) treeLenCovOne + 2 d L c₁`, `c₁ = (3(2L-1))^d`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Fluctuation Finset

section Paper

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] (m₀ j : ℕ)

/-- The family of all aligned `π'_j`-cubes (bases of boxes of side `L · cellSide`) contained
in `X`. -/
def fullCover (X : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {b | Aligned (cellSide L m₀ m₁ j) b ∧ box b (L * cellSide L m₀ m₁ j) ⊆ X}

/-- **The papers' size `d_j(X)`** (P1 (2.26)-(2.27)): the infimum of the normalized bond cost of
connected structures in `X` meeting every `π'_j`-cube contained in `X`. -/
noncomputable def treeLenAll (X : Set (CTorus d L N₁ m₁ K)) : ℝ :=
  sInf {x | ∃ W E, ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j (fullCover m₀ j X) W ∧
    x = bondCost (scaleW L m₀ m₁ j) E}

variable {m₀ j}

omit [NeZero N₁] [NeZero L] in
theorem fullCover_chosen {X : Set (CTorus d L N₁ m₁ K)} (hX : Balaban.Fluctuation.IsDj m₀ j X) :
    ChosenOne m₀ j X (fullCover m₀ j X) := by
  refine ⟨fun b hb => hb, fun z hz => ?_⟩
  obtain ⟨b, hb1, hb2, hb3⟩ := hX.2.1 z hz
  exact ⟨b, ⟨hb1, hb3⟩, hb2⟩

omit [NeZero N₁] [NeZero L] in
theorem chosen_of_admissible {X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ModAdmissible m₀ j Set.univ X 𝒦 W E) :
    ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j 𝒦 W := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨⟨h1, fun z hz => by simpa using h2 ⟨hz, Set.mem_univ z⟩⟩, h3, h4, h5⟩

omit [NeZero N₁] [NeZero L] in
theorem admissible_of_chosen {X 𝒦 : Set (CTorus d L N₁ m₁ K)}
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h : ChosenOne m₀ j X 𝒦) (h3 : ConnStruct W E) (h4 : ↑W ⊆ X) (h5 : MeetsOne m₀ j 𝒦 W) :
    ModAdmissible m₀ j Set.univ X 𝒦 W E := by
  refine ⟨h.1, fun z hz => ?_, h3, h4, h5⟩
  obtain ⟨b, hb, hzb⟩ := h.2 z hz.1
  exact Set.mem_iUnion₂.2 ⟨b, hb, hzb⟩

/-- A tree meeting every cube of `fullCover` exists in a domain. -/
theorem exists_tree_all {X : Set (CTorus d L N₁ m₁ K)} (hX : Balaban.Fluctuation.IsDj m₀ j X) :
    ∃ W E, ConnStruct W E ∧ (↑W ⊆ X) ∧ MeetsOne m₀ j (fullCover m₀ j X) W := by
  classical
  obtain ⟨hne, hU, hconn⟩ := hX
  have hL : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  refine ⟨Finset.univ.filter (· ∈ X),
    Finset.univ.filter fun p => p.1 ∈ X ∧ p.2 ∈ X ∧ Nbr p.1 p.2, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simp [hx]⟩
  · intro p hp
    simpa using (Finset.mem_filter.1 hp).2
  · intro x hx y hy
    have hx' : x ∈ X := by simpa using hx
    have hy' : y ∈ X := by simpa using hy
    refine Relation.ReflTransGen.mono (fun u v huv => ?_) x y (hconn x hx' y hy')
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl huv
  · intro x hx; simpa using hx
  · intro b hb
    refine ⟨b, ?_, mem_box_self b hL⟩
    simpa using hb.2 (mem_box_self b hL)

omit [NeZero N₁] [NeZero L] in
theorem treeLenAll_nonneg (X : Set (CTorus d L N₁ m₁ K)) : 0 ≤ treeLenAll m₀ j X := by
  refine Real.sInf_nonneg ?_
  rintro x ⟨W, E, -, -, -, rfl⟩
  exact bondCost_scaleW_nonneg E

/-- **`d^cov_j(X) ≤ d_j(X)`** (T2). -/
theorem treeLenCovOne_le_treeLenAll {X : Set (CTorus d L N₁ m₁ K)}
    (hX : Balaban.Fluctuation.IsDj m₀ j X) : treeLenCovOne m₀ j X ≤ treeLenAll m₀ j X := by
  obtain ⟨W₁, E₁, h1, h2, h3⟩ := exists_tree_all hX
  refine le_csInf ⟨_, W₁, E₁, h1, h2, h3, rfl⟩ ?_
  rintro x ⟨W, E, hW1, hW2, hW3, rfl⟩
  have hbdd : BddBelow {x | ∃ 𝒦 W E, ChosenOne m₀ j X 𝒦 ∧ ConnStruct W E ∧ (↑W ⊆ X) ∧
      MeetsOne m₀ j 𝒦 W ∧ x = bondCost (scaleW L m₀ m₁ j) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    exact bondCost_scaleW_nonneg E
  exact csInf_le hbdd ⟨_, W, E, fullCover_chosen hX, hW1, hW2, hW3, rfl⟩

/-- Extending a tree meeting a chosen family to one meeting all contained cubes: each extra cube
costs at most `2 d L`. -/
theorem extend_tree {X 𝒦 : Set (CTorus d L N₁ m₁ K)} (h𝒦 : ChosenOne m₀ j X 𝒦)
    {W : Finset (CTorus d L N₁ m₁ K)} {E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (hW : ConnStruct W E) (hWX : ↑W ⊆ X) (hmeet : MeetsOne m₀ j 𝒦 W) :
    ∃ W' E', ConnStruct W' E' ∧ (↑W' ⊆ X) ∧ MeetsOne m₀ j (fullCover m₀ j X) W' ∧
      bondCost (scaleW L m₀ m₁ j) E' ≤ bondCost (scaleW L m₀ m₁ j) E +
        (cellCount (cellSide L m₀ m₁ j) X : ℝ) * (2 * d * L) := by
  classical
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
  have haR : (a : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have hω : ∀ x y : CTorus d L N₁ m₁ K, 0 ≤ scaleW L m₀ m₁ j x y := fun x y => by
    unfold scaleW; positivity
  set ρ : ℝ := 2 * d * L with hρ
  -- every point of a contained cube is linked to the tree
  have hlink : ∀ b ∈ fullCover m₀ j X, ∃ p ∈ W, Linked X (scaleW L m₀ m₁ j) ρ p b := by
    intro b hb
    have hbX : b ∈ X := hb.2 (mem_box_self b (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) ha0))
    obtain ⟨K, hK, hbK⟩ := h𝒦.2 b hbX
    obtain ⟨p, hpW, hpK⟩ := hmeet K hK
    refine ⟨p, hpW, ?_⟩
    have := linked_box_pair (R := X) (ω := scaleW L m₀ m₁ j) hω K (L * a)
      (c := ((a : ℝ))⁻¹) (h𝒦.1 K hK).2 (fun x y _ _ => by
        unfold scaleW; rw [haR]) hpK hbK
    refine Covers.mono_c this (le_of_eq ?_)
    rw [hρ]; push_cast; field_simp
  have key : ∀ S : Finset (CTorus d L N₁ m₁ K), (∀ b ∈ S, b ∈ fullCover m₀ j X) →
      Covers X (scaleW L m₀ m₁ j) (bondCost (scaleW L m₀ m₁ j) E + S.card * ρ) (W ∪ S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨W, E, hW, hWX, by simp, by simp⟩
    | insert b S hb ih =>
      intro hS
      obtain ⟨p, hpW, hl⟩ := hlink b (hS b (Finset.mem_insert_self _ _))
      have h1 := ih fun c hc => hS c (Finset.mem_insert_of_mem hc)
      have h2 := Covers.join hω h1 hl ⟨p, Finset.mem_union_left _ hpW, by simp⟩
      refine (Covers.mono_A h2 ?_).mono_c (le_of_eq ?_)
      · intro x hx
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        tauto
      · rw [Finset.card_insert_of_notMem hb]; push_cast; ring
  set S : Finset (CTorus d L N₁ m₁ K) :=
    Finset.univ.filter fun b => b ∈ fullCover m₀ j X with hS
  obtain ⟨W', E', h1, h2, h3, h4⟩ := key S (fun b hb => (Finset.mem_filter.1 hb).2)
  have hcard : S.card ≤ cellCount a X := by
    unfold cellCount
    refine Finset.card_le_card fun b hb => ?_
    obtain ⟨hal, hbox⟩ := (Finset.mem_filter.1 hb).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hal, fun z hz => hbox ?_⟩
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w, fun μ => ?_, rfl⟩
    have := hw μ
    have h3 : a ≤ L * a := Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero (NeZero.ne L))
    rw [← ha] at *
    omega
  refine ⟨W', E', h1, h2, fun b hb => ⟨b, h3 (by simp [hS, hb]), mem_box_self b ?_⟩,
    h4.trans ?_⟩
  · exact Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) ha0
  · have : (S.card : ℝ) ≤ cellCount a X := by exact_mod_cast hcard
    have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
    nlinarith

/-- **Comparison of the two sizes** (T3): for a domain `X ∈ 𝒟_j`,
`d_j(X) ≤ (1 + 2 d L c₁) d^cov_j(X) + 2 d L c₁`, with `c₁ = (3 (2L-1))^d`
(`A = 1 + 2 d L c₁`, `B = 2 d L c₁`). -/
theorem treeLenAll_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : Balaban.Fluctuation.IsDj m₀ j X) :
    treeLenAll m₀ j X ≤ (1 + 2 * d * L * c1 d L) * treeLenCovOne m₀ j X + 2 * d * L * c1 d L := by
  obtain ⟨𝒦, W, E, h1, h2, h3, h4, he⟩ := treeLenCovOne_attained m₀ j X (by
    obtain ⟨𝒦, W, E, h⟩ := exists_admissible_of_IsDj (Ω := Set.univ) hX
    obtain ⟨a, b, c, d⟩ := chosen_of_admissible h
    exact ⟨𝒦, W, E, a, b, c, d⟩)
  obtain ⟨W', E', g1, g2, g3, g4⟩ := extend_tree h1 h2 h3 h4
  have hcell := cellCount_le_of_admissible hN hj (admissible_of_chosen h1 h2 h3 h4)
  rw [Set.inter_univ] at hcell
  have hbdd : BddBelow {x | ∃ W E, ConnStruct W E ∧ (↑W ⊆ X) ∧
      MeetsOne m₀ j (fullCover m₀ j X) W ∧ x = bondCost (scaleW L m₀ m₁ j) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨W, E, -, -, -, rfl⟩
    exact bondCost_scaleW_nonneg E
  refine (csInf_le hbdd ⟨W', E', g1, g2, g3, rfl⟩).trans (g4.trans ?_)
  rw [he] at hcell ⊢
  have hρ : (0 : ℝ) ≤ 2 * d * L := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcell hρ]

end Paper

end Balaban.Localization
