/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModDefs
public import Balaban.Polymer.Animals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cell geometry for the modular covering size (FLUCTUATION.md §1.2)

The relation `Near r a u v` between aligned cell bases, the cell graph `cellGraph a n` (cells at
index distance `1`), the fact that the cells met by a connected structure form a connected set of
this graph (`connected_image_cbase`), balls and degrees, and the cells of `Z ∩ Ω` near the cells
met by an admissible structure (`exists_near_of_mem`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

section Near

variable {d n : ℕ}

theorem Near.refl (r a : ℕ) (u : Torus d n) : Near r a u u :=
  ⟨0, fun μ => by simp, by funext μ; simp⟩

theorem Near.symm {r a : ℕ} {u v : Torus d n} (h : Near r a u v) : Near r a v u := by
  obtain ⟨q, hq, rfl⟩ := h
  refine ⟨-q, fun μ => by simpa using hq μ, ?_⟩
  funext μ
  simp only [Pi.add_apply, Pi.neg_apply]
  push_cast
  ring

theorem Near.mono {r r' a : ℕ} {u v : Torus d n} (h : Near r a u v) (hr : r ≤ r') :
    Near r' a u v := by
  obtain ⟨q, hq, hv⟩ := h
  exact ⟨q, fun μ => (hq μ).trans (by exact_mod_cast hr), hv⟩

theorem Near.trans {r r' a : ℕ} {u v w : Torus d n} (h : Near r a u v) (h' : Near r' a v w) :
    Near (r + r') a u w := by
  obtain ⟨q, hq, rfl⟩ := h
  obtain ⟨q', hq', rfl⟩ := h'
  refine ⟨q + q', fun μ => ?_, ?_⟩
  · simp only [Pi.add_apply]
    calc |q μ + q' μ| ≤ |q μ| + |q' μ| := abs_add_le _ _
      _ ≤ r + r' := by exact_mod_cast add_le_add (hq μ) (hq' μ)
  · funext μ
    simp only [Pi.add_apply]
    push_cast
    ring

open Classical in
/-- The `Near`-ball has at most `(2r+1)^d` points. -/
theorem card_near_le [NeZero n] (r a : ℕ) (u : Torus d n) :
    (Finset.univ.filter fun v => Near r a u v).card ≤ (2 * r + 1) ^ d := by
  let g : (Fin d → ℤ) → Torus d n := fun q => u + fun μ => (((a : ℤ) * q μ : ℤ) : ZMod n)
  have hsub : (Finset.univ.filter fun v => Near r a u v) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) r).image g := by
    intro v hv
    obtain ⟨q, hq, hvq⟩ := (Finset.mem_filter.1 hv).2
    refine Finset.mem_image.2 ⟨q, ?_, hvq.symm⟩
    rw [Fintype.mem_piFinset]
    intro μ
    rw [Finset.mem_Icc]
    exact abs_le.1 (hq μ)
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) r).card := Finset.card_image_le
    _ = ∏ _μ : Fin d, (Finset.Icc (-(r : ℤ)) r).card := Fintype.card_piFinset _
    _ = (2 * r + 1) ^ d := by
        simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        congr 1; omega

end Near

section Step

variable {d n : ℕ} [NeZero n]

/-- Nearest-neighbour sites lie in equal or adjacent cells. -/
theorem near_cbase_of_nbr {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a) {x y : Torus d n} (h : Nbr x y) :
    Near 1 a (cbase a x) (cbase a y) := by
  have key : ∀ (x : Torus d n) (μ : Fin d),
      Near 1 a (cbase a x) (cbase a (x + Pi.single μ 1)) := by
    intro x μ
    set b := cbase a x with hb
    have hbal : Aligned a b := aligned_cbase x
    set r : Fin d → ℕ := fun ν => (x ν).val % a with hr
    have hx : x = b + natT r := by
      rw [hb, cbase_eq_sub]; abel
    have hrlt : ∀ ν, r ν < a := fun ν => Nat.mod_lt _ ha0
    set w : Fin d → ℕ := r + Pi.single μ 1 with hw
    have hy : x + Pi.single μ 1 = b + natT w := by
      conv_lhs => rw [hx]
      rw [hw, natT_add, natT_single, add_assoc]
    rw [hy, cbase_add ha hbal]
    refine ⟨fun ν => if ν = μ ∧ r μ + 1 = a then 1 else 0, fun ν => ?_, ?_⟩
    · dsimp only
      split_ifs <;> simp
    · funext ν
      simp only [Pi.add_apply, natT_apply]
      congr 1
      by_cases hν : ν = μ
      · subst hν
        have hwν : w ν = r ν + 1 := by simp [hw]
        rw [hwν]
        by_cases hra : r ν + 1 = a
        · simp [hra]
        · have : r ν + 1 < a := lt_of_le_of_ne (hrlt ν) hra
          rw [Nat.mod_eq_of_lt this]
          simp [hra]
      · have hwν : w ν = r ν := by simp [hw, hν]
        rw [hwν, Nat.mod_eq_of_lt (hrlt ν)]
        simp [hν]
  obtain ⟨μ, h | h⟩ := h
  · rw [h]; exact key x μ
  · rw [h]; exact (key y μ).symm

end Step

section Graph

variable {d n : ℕ}

/-- The graph of cells: two distinct cell bases at index distance `1` (all coordinates differ
by `0` or `±a`). -/
def cellGraph (d n a : ℕ) : SimpleGraph (Torus d n) where
  Adj u v := u ≠ v ∧ Near 1 a u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem cellGraph_adj {a : ℕ} {u v : Torus d n} :
    (cellGraph d n a).Adj u v ↔ u ≠ v ∧ Near 1 a u v := Iff.rfl

noncomputable instance [NeZero n] (a : ℕ) : (cellGraph d n a).LocallyFinite := fun _ => Fintype.ofFinite _

theorem degree_cellGraph_le [NeZero n] (a : ℕ) (v : Torus d n) :
    (cellGraph d n a).degree v ≤ 3 ^ d := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine le_trans (Finset.card_le_card ?_) (by simpa using card_near_le 1 a v)
  intro u hu
  rw [SimpleGraph.mem_neighborFinset, cellGraph_adj] at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hu.2

/-- **The cells met by a connected structure form a connected set of cells.** -/
theorem connected_image_cbase [NeZero n] {a : ℕ} (ha : a ∣ n) (ha0 : 0 < a)
    {W : Finset (Torus d n)} {E : Finset (Torus d n × Torus d n)} (hc : ConnStruct W E) :
    ((cellGraph d n a).induce ((W.image (cbase a) : Finset (Torus d n)) : Set (Torus d n))).Connected := by
  classical
  obtain ⟨hne, hE, hconn⟩ := hc
  have hmem : ∀ x ∈ W, cbase a x ∈ ((W.image (cbase a) : Finset (Torus d n)) : Set (Torus d n)) :=
    fun x hx => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx)
  have key : ∀ x0 (hx0 : x0 ∈ W), ∀ y, Relation.ReflTransGen (fun a b => (a, b) ∈ E ∨ (b, a) ∈ E) x0 y →
      ∃ hy : y ∈ W, ((cellGraph d n a).induce
        ((W.image (cbase a) : Finset (Torus d n)) : Set (Torus d n))).Reachable
        ⟨cbase a x0, hmem x0 hx0⟩ ⟨cbase a y, hmem y hy⟩ := by
    intro x0 hx0 y h
    induction h with
    | refl => exact ⟨hx0, SimpleGraph.Reachable.refl _⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hr⟩ := ih
      have hbc' : b ∈ W ∧ c ∈ W ∧ Nbr b c := by
        rcases hbc with h | h
        · exact hE _ h
        · obtain ⟨h1, h2, h3⟩ := hE _ h
          exact ⟨h2, h1, h3.symm⟩
      refine ⟨hbc'.2.1, hr.trans ?_⟩
      by_cases heq : cbase a b = cbase a c
      · have : (⟨cbase a b, hmem b hb⟩ : ((W.image (cbase a) : Finset (Torus d n)) :
            Set (Torus d n))) = ⟨cbase a c, hmem c hbc'.2.1⟩ := Subtype.ext heq
        rw [this]
      · exact SimpleGraph.Adj.reachable
          (cellGraph_adj.2 ⟨heq, near_cbase_of_nbr ha ha0 hbc'.2.2⟩)
  obtain ⟨x₀, hx₀⟩ := hne
  have : Nonempty ((W.image (cbase a) : Finset (Torus d n)) : Set (Torus d n)) :=
    ⟨⟨cbase a x₀, hmem x₀ hx₀⟩⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hu)
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
  obtain ⟨hy', hr⟩ := key x hx y (hconn x hx y hy)
  exact hr

end Graph

end Balaban.Fluctuation
