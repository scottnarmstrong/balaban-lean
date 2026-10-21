/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgHull
public import Balaban.Green.FinalBoxLocCount
public import Balaban.Polymer.RootedAnimals
import Mathlib.Tactic.Linarith

/-!
# The graph of cells with overlapping patches

The cells of the decoupling cover are the vertices of `Green.cellGraph (cellPatch C D)`: two distinct cells are
adjacent when their patches (`cellPatch`) meet.  Every patch lies within `9 L^{k+1+m₁}` of the base
of its cell (`supDist_cellPatch_le`), so the neighbours of a cell have bases within
`18 L^{k+1+m₁}` and are counted layer by layer by the cells of side `L^{n+m₁}` that meet a ball
(`card_cells_near_le`): the degree is at most `cellsNear d L k 18`, a number independent of `m₁`
(`cellPatch_degree_le`).  A rooted family of cells (`IsRootedFamily`) is rooted in this graph at the
cells whose patch meets the seed (`rooted_cellPatchGraph`), at most `cellsRoot d L k ρ` of them.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.LargeField Balaban.Fluctuation Finset

section Graph

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] (C : DecCover d L N₁ m₁ (k + 1))


omit [NeZero N₁] [NeZero L] in
theorem pow_dvd_cover_side {n : ℕ} (hn : n ≤ k + 1) : L ^ (n + m₁) ∣ N₁ * L ^ m₁ * L ^ (k + 1) := by
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
  rw [ht]
  exact ⟨N₁ * L ^ t, by ring⟩

theorem two_mul_div_side {n : ℕ} (hn : n ≤ k + 1) (c : ℕ) :
    2 * (c * L ^ (k + 1 + m₁)) / L ^ (n + m₁) = 2 * c * L ^ (k + 1 - n) := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
  have h1 : k + 1 - n = t := by omega
  rw [h1, ht, show 2 * (c * L ^ (n + t + m₁)) = (2 * c * L ^ t) * L ^ (n + m₁) by ring]
  exact Nat.mul_div_cancel _ (pow_pos hL0 _)


/-- The number of cells within sup-distance `R` of a site, `R = c · L^{k+1+m₁}`: the cells of layer
`n` have bases in the cells of side `L^{n+m₁}` that meet the ball. -/
def cellsNear (d L k c : ℕ) : ℕ := ∑ n ∈ Finset.Icc 1 (k + 1), (2 * c * L ^ (k + 1 - n) + 2) ^ d

/-- The same count for a ball of radius `9 L^{k+1+m₁} + ρ`. -/
def cellsRoot (d L k ρ : ℕ) : ℕ := ∑ n ∈ Finset.Icc 1 (k + 1), (18 * L ^ (k + 1 - n) + 2 * ρ + 2) ^ d

theorem cbase_eq_self_of_aligned' {n a : ℕ} [NeZero n] (ha : a ∣ n) (ha0 : 0 < a)
    {b : Torus d n} (hb : Aligned a b) : cbase a b = b :=
  cbase_eq_of_mem_box ha hb (mem_box_self b ha0)

/-- **Cells near a site.**  The cells (centres) whose base is within `c L^{k+1+m₁}` of a site number at
most `cellsNear d L k c`. -/
theorem card_cells_near_le_aux
    (hlay : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ k + 1)
    (hal : ∀ q ∈ C.cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2)
    (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (R : ℕ) :
    (C.cubeIdx.filter fun q => supDist z q.2 ≤ R).card ≤
      ∑ n ∈ Finset.Icc 1 (k + 1), (2 * R / L ^ (n + m₁) + 2) ^ d := by
  classical
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hsub : (C.cubeIdx.filter fun q => supDist z q.2 ≤ R) ⊆
      (Finset.Icc 1 (k + 1)).biUnion fun n =>
        (ballCells (L ^ (n + m₁)) z R).image fun b => (n, b) := by
    intro q hq
    obtain ⟨hqI, hqd⟩ := Finset.mem_filter.1 hq
    obtain ⟨h1, h2⟩ := hlay q hqI
    refine Finset.mem_biUnion.2 ⟨q.1, Finset.mem_Icc.2 ⟨h1, h2⟩, Finset.mem_image.2 ⟨q.2, ?_, rfl⟩⟩
    refine mem_ballCells.2 ⟨q.2, hqd, ?_⟩
    exact cbase_eq_self_of_aligned' (pow_dvd_cover_side h2) (pow_pos hL0 _) (hal q hqI)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 := (Finset.mem_Icc.1 hn).2
  have hdvd := pow_dvd_cover_side (L := L) (N₁ := N₁) (m₁ := m₁) hn2
  exact Finset.card_image_le.trans (card_ballCells_le hdvd (pow_pos hL0 _) z _)

theorem card_cells_near_le
    (hlay : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ k + 1)
    (hal : ∀ q ∈ C.cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2)
    (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (c : ℕ) :
    (C.cubeIdx.filter fun q => supDist z q.2 ≤ c * L ^ (k + 1 + m₁)).card ≤ cellsNear d L k c := by
  refine (card_cells_near_le_aux C hlay hal z _).trans (le_of_eq ?_)
  unfold cellsNear
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [two_mul_div_side (Finset.mem_Icc.1 hn).2]

theorem card_cells_root_le
    (hlay : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ k + 1)
    (hal : ∀ q ∈ C.cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2)
    (z : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (ρ : ℕ) :
    (C.cubeIdx.filter fun q => supDist z q.2 ≤ 9 * L ^ (k + 1 + m₁) + ρ).card ≤ cellsRoot d L k ρ := by
  refine (card_cells_near_le_aux C hlay hal z _).trans ?_
  unfold cellsRoot
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 := (Finset.mem_Icc.1 hn).2
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hb : 0 < L ^ (n + m₁) := pow_pos hL0 _
  have h1 : 2 * (9 * L ^ (k + 1 + m₁) + ρ) / L ^ (n + m₁) ≤ 18 * L ^ (k + 1 - n) + 2 * ρ := by
    have e : 2 * (9 * L ^ (k + 1 + m₁) + ρ) = 18 * L ^ (k + 1 + m₁) + 2 * ρ := by ring
    rw [e]
    have hdv : L ^ (n + m₁) ∣ 18 * L ^ (k + 1 + m₁) := by
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn2
      rw [ht]; exact ⟨18 * L ^ t, by ring⟩
    rw [Nat.add_div_of_dvd_right hdv]
    have h2 := two_mul_div_side (L := L) (m₁ := m₁) (k := k) hn2 9
    have h3 : 18 * L ^ (k + 1 + m₁) / L ^ (n + m₁) = 18 * L ^ (k + 1 - n) := by
      rw [show 18 * L ^ (k + 1 + m₁) = 2 * (9 * L ^ (k + 1 + m₁)) by ring, h2]
    rw [h3]
    have : 2 * ρ / L ^ (n + m₁) ≤ 2 * ρ := Nat.div_le_self _ _
    omega
  exact Nat.pow_le_pow_left (by omega) d

variable {C}

theorem supDist_cellPatch_le {D : ℕ} (hD : D ≤ L ^ (k + 1 + m₁)) (hm : 4 * L ^ 2 ≤ L ^ m₁)
    (hlay : ∀ q ∈ C.cubeIdx, q.1 ≤ k + 1) (i : ↥C.cubeIdx)
    {y : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ cellPatch C D i) :
    supDist i.1.2 y ≤ 9 * L ^ (k + 1 + m₁) := by
  obtain ⟨q, hq, hiq, hyq⟩ := hy
  exact supDist_boxNbhd_le C hD hm (hlay q hq) (hlay i.1 i.2) hiq hyq

open Classical in
/-- **Degree of the graph of cells.**  A cell is adjacent to at most `cellsNear d L k 18` others. -/
theorem cellPatch_degree_le {D : ℕ} (hD : D ≤ L ^ (k + 1 + m₁)) (hm : 4 * L ^ 2 ≤ L ^ m₁)
    (hlay : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ k + 1)
    (hal : ∀ q ∈ C.cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2) (i : ↥C.cubeIdx) :
    (Green.cellGraph (cellPatch C D)).degree i ≤ cellsNear d L k 18 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine le_trans ?_ (card_cells_near_le C hlay hal i.1.2 18)
  refine Finset.card_le_card_of_injOn Subtype.val (fun j hj => ?_) (fun _ _ _ _ h => Subtype.ext h)
  have hj' := (SimpleGraph.mem_neighborFinset _ _ _).1 (Finset.mem_coe.1 hj)
  obtain ⟨-, hr⟩ := (SimpleGraph.fromRel_adj _ _ _).1 hj'
  obtain ⟨y, hyi, hyj⟩ : (cellPatch C D i ∩ cellPatch C D j).Nonempty := by
    rcases hr with h | h
    · exact h
    · rwa [Set.inter_comm]
  refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨j.2, ?_⟩)
  have h1 := supDist_cellPatch_le hD hm (fun q hq => (hlay q hq).2) i hyi
  have h2 := supDist_cellPatch_le hD hm (fun q hq => (hlay q hq).2) j hyj
  have h3 := supDist_triangle i.1.2 y j.1.2
  rw [supDist_comm y j.1.2] at h3
  omega

theorem card_rootCells_le {D : ℕ} (hD : D ≤ L ^ (k + 1 + m₁)) (hm : 4 * L ^ 2 ≤ L ^ m₁)
    (hlay : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ k + 1)
    (hal : ∀ q ∈ C.cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2)
    (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) {ρs : ℕ}
    {S : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))} (hS : ∀ y ∈ S, supDist x y ≤ ρs) :
    (Green.rootCells (cellPatch C D) S).card ≤ cellsRoot d L k ρs := by
  classical
  refine le_trans ?_ (card_cells_root_le C hlay hal x ρs)
  refine Finset.card_le_card_of_injOn Subtype.val (fun j hj => ?_) (fun _ _ _ _ h => Subtype.ext h)
  obtain ⟨y, hyj, hyS⟩ := Green.mem_rootCells.1 (Finset.mem_coe.1 hj)
  refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨j.2, ?_⟩)
  have h1 := supDist_cellPatch_le hD hm (fun q hq => (hlay q hq).2) j hyj
  have h2 := hS y hyS
  have h3 := supDist_triangle x y j.1.2
  rw [supDist_comm y j.1.2] at h3
  omega

open Classical in
theorem walkIn_of_cellAdj {D : ℕ} {Cs : Finset ↥C.cubeIdx} {b c : ↥C.cubeIdx}
    (h : Green.CellAdj (cellPatch C D) Cs b c) : Polymer.WalkIn (Green.cellGraph (cellPatch C D)) Cs b c := by
  obtain ⟨hb, hc, hne⟩ := h
  by_cases hbc : b = c
  · subst hbc; exact Polymer.WalkIn.refl hb
  · refine ⟨SimpleGraph.Walk.cons (Green.cellGraph_adj _ hbc hne) SimpleGraph.Walk.nil, fun x hx => ?_⟩
    change x ∈ b :: [c] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption

open Classical in
/-- **A rooted family of cells is rooted in the graph of cells.** -/
theorem rooted_cellPatchGraph {D : ℕ} {S : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))}
    {Cs : Finset ↥C.cubeIdx} (h : Green.IsRootedFamily (cellPatch C D) S Cs) :
    Polymer.Rooted (Green.cellGraph (cellPatch C D)) ((Green.rootCells (cellPatch C D) S : Finset ↥C.cubeIdx) : Set ↥C.cubeIdx) Cs := by
  intro i hi
  obtain ⟨j, hj, hjS, hji⟩ := h i hi
  refine ⟨j, Finset.mem_coe.2 (Green.mem_rootCells.2 hjS), ?_⟩
  have key : ∀ i', Relation.ReflTransGen (Green.CellAdj (cellPatch C D) Cs) j i' →
      Polymer.WalkIn (Green.cellGraph (cellPatch C D)) Cs i' j := by
    intro i' h'
    induction h' with
    | refl => exact Polymer.WalkIn.refl hj
    | @tail b c _ hab ih =>
      exact (walkIn_of_cellAdj ⟨hab.2.1, hab.1, by rw [Set.inter_comm]; exact hab.2.2⟩).trans ih
  exact key i hji

end Graph


end Balaban.LargeField.Base
