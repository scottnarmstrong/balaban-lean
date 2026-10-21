/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalMacroCover
public import Balaban.Polymer.BlockTorus
public import Balaban.Polymer.Support
import Mathlib.Tactic.Linarith

/-!
# The graph of the macro cells

A6-3, gas layer. The macro cells of side `M_c` of a torus `𝕋_m` (`Green.macZ`, the cells of the cut
family of the localization) are the sites of the gas of the box integral. Two cells are adjacent
(`macCellGraph`) when they contain nearest-neighbour sites. Then:

* `macCellGraph_degree_le`: a cell has at most `16^d` neighbours (the neighbouring cells of a cell lie
  coordinatewise within `macNear2`, `macNear2_card_le`), independently of `M_c`;
* `macCellGraph_connected`: the graph is connected;
* `isAnimal_image_macZ`: the cells of a connected set of sites form a connected set of cells;
* `card_macZ_fibre_le`: a cell has at most `(2 M_c)^d` sites.
-/

@[expose] public section

open Finset

namespace Balaban.RootFSpine

open Balaban.Green Balaban.Polymer

variable {d m : ℕ} [NeZero m] (Mc : ℕ)

/-- **The graph of the macro cells**: two distinct cells are adjacent when they contain
nearest-neighbour sites of the torus. -/
def macCellGraph : SimpleGraph (MacIdx d m Mc) :=
  SimpleGraph.fromRel fun z z' => ∃ x x' : Torus d m, (blockGraph d m).Adj x x' ∧
    macZ Mc (x : L1Torus d m) = z ∧ macZ Mc (x' : L1Torus d m) = z'

variable {Mc}

/-- Nearest-neighbour sites differ by at most `1` in every coordinate (cyclically). -/
theorem natAbs_cycRep_sub_le_one_of_adj {x x' : Torus d m} (h : (blockGraph d m).Adj x x')
    (i : Fin d) : (cycRep (x' i - x i)).natAbs ≤ 1 := by
  obtain ⟨-, μ, hμ⟩ := h
  by_cases hi : i = μ
  · subst hi
    rcases hμ with h1 | h1
    · have : x' i - x i = ((1 : ℤ) : ZMod m) := by rw [h1]; simp
      exact (natAbs_cycRep_le_of_cast _ 1 this.symm).trans (by simp)
    · have : x' i - x i = ((-1 : ℤ) : ZMod m) := by rw [h1]; simp
      exact (natAbs_cycRep_le_of_cast _ (-1) this.symm).trans (by simp)
  · have : x' i - x i = ((0 : ℤ) : ZMod m) := by
      rcases hμ with h1 | h1 <;> rw [h1] <;> simp [Pi.single_eq_of_ne hi]
    exact (natAbs_cycRep_le_of_cast _ 0 this.symm).trans (by simp)

/-- The cells of nearest-neighbour sites are coordinatewise in `macNear2`. -/
theorem macZ_mem_macNear2_of_adj (hMc : 0 < Mc) {x x' : Torus d m}
    (h : (blockGraph d m).Adj x x') (i : Fin d) :
    macZ Mc (x' : L1Torus d m) i ∈ macNear2 Mc (macZ Mc (x : L1Torus d m) i) := by
  simp only [macNear2, mem_filter, mem_univ, true_and]
  refine ⟨x' i, x i, rfl, rfl, ?_⟩
  have := natAbs_cycRep_sub_le_one_of_adj h i
  omega

theorem macCellGraph_adj_mem (hMc : 0 < Mc) {z z' : MacIdx d m Mc} (h : (macCellGraph Mc).Adj z z') :
    z' ∈ Fintype.piFinset fun i => macNear2 Mc (z i) := by
  rw [macCellGraph, SimpleGraph.fromRel_adj] at h
  rw [Fintype.mem_piFinset]
  intro i
  rcases h.2 with ⟨x, x', hxx, rfl, rfl⟩ | ⟨x, x', hxx, rfl, rfl⟩
  · exact macZ_mem_macNear2_of_adj hMc hxx i
  · -- here `z = macZ x'`, `z' = macZ x`, and `x' ~ x`
    exact macZ_mem_macNear2_of_adj hMc hxx.symm i

open Classical in
/-- **A cell has at most `16^d` neighbours.** -/
theorem macCellGraph_degree_le (hMc : 0 < Mc) (z : MacIdx d m Mc) :
    (macCellGraph Mc).degree z ≤ 16 ^ d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  calc ((macCellGraph Mc).neighborFinset z).card ≤
        (Fintype.piFinset fun i => macNear2 Mc (z i)).card := by
        refine card_le_card fun z' hz' => ?_
        rw [SimpleGraph.mem_neighborFinset] at hz'
        exact macCellGraph_adj_mem hMc hz'
    _ = ∏ i, (macNear2 Mc (z i)).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, 16 := prod_le_prod fun i _ => macNear2_card_le hMc _
    _ = 16 ^ d := by simp

omit [NeZero m] in
/-- The cells of the sites of a nearest-neighbour step are equal or adjacent. -/
theorem macZ_eq_or_adj {x x' : Torus d m} (h : (blockGraph d m).Adj x x') :
    macZ Mc (x : L1Torus d m) = macZ Mc (x' : L1Torus d m) ∨
      (macCellGraph Mc).Adj (macZ Mc (x : L1Torus d m)) (macZ Mc (x' : L1Torus d m)) := by
  by_cases he : macZ Mc (x : L1Torus d m) = macZ Mc (x' : L1Torus d m)
  · exact Or.inl he
  · refine Or.inr ?_
    rw [macCellGraph, SimpleGraph.fromRel_adj]
    exact ⟨he, Or.inl ⟨x, x', h, rfl, rfl⟩⟩

omit [NeZero m] in
/-- Reachability of sites gives reachability of their cells. -/
theorem reachable_macZ {x x' : Torus d m} (h : (blockGraph d m).Reachable x x') :
    (macCellGraph Mc).Reachable (macZ Mc (x : L1Torus d m)) (macZ Mc (x' : L1Torus d m)) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
    rcases macZ_eq_or_adj (Mc := Mc) hadj with he | ha
    · rw [he]; exact ih
    · exact ha.reachable.trans ih

/-- **The graph of the macro cells is connected.** -/
theorem macCellGraph_connected (hconn : (blockGraph d m).Connected) :
    (macCellGraph (d := d) (m := m) Mc).Connected := by
  have hne : Nonempty (MacIdx d m Mc) := ⟨fun i => ⟨0, macK_pos m Mc⟩⟩
  refine ⟨fun z z' => ?_⟩
  obtain ⟨x, hx⟩ := macCore_nonempty (d := d) (m := m) (M := Mc) z
  obtain ⟨x', hx'⟩ := macCore_nonempty (d := d) (m := m) (M := Mc) z'
  have h1 := eq_macZ_of_mem_macCore hx
  have h2 := eq_macZ_of_mem_macCore hx'
  rw [h1, h2]
  exact reachable_macZ (hconn.preconnected (x : Torus d m) x')

omit [NeZero m] in
/-- **The cells of a connected set of sites are connected.** -/
theorem isAnimal_image_macZ {Y : Finset (Torus d m)} (hY : IsAnimal (blockGraph d m) Y) :
    IsAnimal (macCellGraph Mc) (Y.image fun x => macZ Mc (x : L1Torus d m)) := by
  rw [isAnimal_iff] at hY ⊢
  refine ⟨hY.1.image _, fun z hz z' hz' => ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hz
  obtain ⟨x', hx', rfl⟩ := mem_image.1 hz'
  have hp := hY.2 x hx x' hx'
  clear hz hz'
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    obtain ⟨hb, hc, hadj⟩ := hbc
    refine (ih hb).trans ?_
    rcases macZ_eq_or_adj (Mc := Mc) hadj with he | ha
    · rw [he]
    · exact Relation.ReflTransGen.single
        ⟨mem_image_of_mem _ hb, mem_image_of_mem _ hc, ha⟩

/-- A cell interval has at most `2 M_c` residues. -/
theorem macCell_card_le (hMc : 0 < Mc) (j : Fin (macK m Mc)) :
    (univ.filter fun v : ZMod m => macCell m Mc v = j).card ≤ 2 * Mc := by
  rcases lt_or_ge m Mc with h | h
  · calc _ ≤ (univ : Finset (ZMod m)).card := card_le_univ _
      _ = m := ZMod.card m
      _ ≤ 2 * Mc := by omega
  · calc _ ≤ (Finset.Ico ((j : ℕ) * Mc) ((j : ℕ) * Mc + 2 * Mc)).card := by
          refine Finset.card_le_card_of_injOn (fun v : ZMod m => v.val) (fun v hv => ?_)
            (ZMod.val_injective m).injOn
          rw [mem_coe, mem_Ico]
          exact macCell_val_bounds hMc h (mem_filter.1 hv).2
      _ = 2 * Mc := by simp

open Classical in
/-- **A cell has at most `(2 M_c)^d` sites.** -/
theorem card_macZ_fibre_le (hMc : 0 < Mc) (z : MacIdx d m Mc) :
    (univ.filter fun x : Torus d m => macZ Mc (x : L1Torus d m) = z).card ≤ (2 * Mc) ^ d := by
  have hsub : (univ.filter fun x : Torus d m => macZ Mc (x : L1Torus d m) = z) ⊆
      Fintype.piFinset fun i => univ.filter fun v : ZMod m => macCell m Mc v = z i := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    rw [← hx]; rfl
  calc _ ≤ _ := card_le_card hsub
    _ = ∏ i, (univ.filter fun v : ZMod m => macCell m Mc v = z i).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, 2 * Mc := prod_le_prod fun i _ => macCell_card_le hMc _
    _ = (2 * Mc) ^ d := by simp

end Balaban.RootFSpine
