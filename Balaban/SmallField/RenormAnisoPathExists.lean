/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormAnisoPath
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Short lattice paths inside a connected finite set

`exists_latPath_of_reflTransGen`: in a finite set `S ⊆ ℤ^d` connected by nearest-neighbour steps
inside `S`, any two sites are joined by a nearest-neighbour path inside `S` of at most `|S| - 1`
steps (a shortest walk of the nearest-neighbour graph induced on `S` is a path, and a path visits
each site at most once).  This bounds the path lengths of `DataHypAnisoOn.of_paths` by the number
of sites of the polymer.
-/

@[expose] public section

namespace Balaban.SmallField

variable {d : ℕ}

/-- Nearest neighbours of `ℤ^d`. -/
def LatAdj (x y : Site d) : Prop := ∃ μ : Fin d, y = x + eU μ ∨ x = y + eU μ

theorem latAdj_symm {x y : Site d} (h : LatAdj x y) : LatAdj y x := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

theorem latAdj_ne {x y : Site d} (h : LatAdj x y) : x ≠ y := by
  rintro rfl
  obtain ⟨μ, h | h⟩ := h <;>
  · have h3 := congrFun h μ
    simp [eU] at h3

/-- **Short paths inside a connected finite set**: two sites of a finite set `S` connected by
nearest-neighbour steps inside `S` are joined by a nearest-neighbour path inside `S` with at most
`|S| - 1` steps. -/
theorem exists_latPath_of_reflTransGen {S : Finset (Site d)} {a b : Site d} (ha : a ∈ S)
    (hab : Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ LatAdj u v) a b) :
    ∃ (p : ℕ → Site d) (n : ℕ), p 0 = a ∧ p n = b ∧ n + 1 ≤ S.card ∧ IsLatPath p n ∧
      ∀ i ≤ n, p i ∈ S := by
  classical
  let G : SimpleGraph (S : Set (Site d)) :=
    (SimpleGraph.fromRel (fun x y : Site d => LatAdj x y)).induce (S : Set (Site d))
  have hwalk : ∀ b, Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ LatAdj u v) a b →
      ∀ hb : b ∈ S, Nonempty (G.Walk ⟨a, ha⟩ ⟨b, hb⟩) := by
    intro b h
    induction h with
    | refl => exact fun _ => ⟨SimpleGraph.Walk.nil⟩
    | tail _ hcb ih =>
      intro hb
      obtain ⟨w⟩ := ih hcb.1
      exact ⟨w.concat (show G.Adj ⟨_, hcb.1⟩ ⟨_, hb⟩ from
        ⟨latAdj_ne hcb.2.2, Or.inl hcb.2.2⟩)⟩
  have hb : b ∈ S := by
    rcases Relation.ReflTransGen.cases_tail hab with h | ⟨c, -, h⟩
    · exact h ▸ ha
    · exact h.2.1
  obtain ⟨w⟩ := hwalk b hab hb
  let q := w.toPath
  have hq : q.1.IsPath := q.2
  have hlen : q.1.length < S.card := by
    have h1 : q.1.length < Fintype.card (S : Set (Site d)) := hq.length_lt
    have h2 : Fintype.card (S : Set (Site d)) = S.card := by
      simp
    omega
  refine ⟨fun i => (q.1.getVert i).1, q.1.length, by simp [SimpleGraph.Walk.getVert_zero],
    by simp [SimpleGraph.Walk.getVert_length], by omega, fun i hi => ?_,
    fun i _ => (q.1.getVert i).2⟩
  have hadj : G.Adj (q.1.getVert i) (q.1.getVert (i + 1)) := q.1.adj_getVert_succ hi
  obtain ⟨μ, h | h⟩ := hadj.2.elim id latAdj_symm
  · exact ⟨μ, Or.inl h⟩
  · exact ⟨μ, Or.inr h⟩

end Balaban.SmallField
