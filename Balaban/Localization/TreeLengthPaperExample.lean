/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.TreeLengthPaper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The two sizes differ: a one-dimensional circle

`d = 1`, `L = 2`, a circle of `4` sites, `j = m₀ = m₁ = K = 0` (cell side `1`, cover cubes
`{i, i+1}`), `X` the whole circle (a domain).  A chosen family `{{0,1},{2,3}}` is met by the
bond `{1,2}` (cost `1`), so `treeLenCovOne X ≤ 1`; but a connected structure meeting all four
cubes `{i, i+1}` needs two bonds (a vertex cover of the 4-cycle has two non-adjacent vertices, and
two non-adjacent sites are not joined by a bond), so `treeLenAll X ≥ 2`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Fluctuation

namespace PaperExample

/-- The circle of four sites. -/
abbrev T : Type := CTorus 1 2 4 0 0

/-- The site `k`. -/
def pt (k : ℕ) : T := fun _ => ((k : ℕ) : ZMod _)

/-- The unit step. -/
def e1 : T := fun _ => 1

theorem mem_box_two (b x : T) : x ∈ box b 2 ↔ x = b ∨ x = b + e1 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h := hw 0
    have : w 0 = 0 ∨ w 0 = 1 := by omega
    rcases this with h0 | h0
    · left; funext μ; simp [h0, Subsingleton.elim μ 0]
    · right; funext μ; simp [h0, e1, Subsingleton.elim μ 0]
  · rintro (rfl | rfl)
    · exact ⟨fun _ => 0, fun _ => by norm_num, by funext μ; simp⟩
    · exact ⟨fun _ => 1, fun _ => by norm_num, by funext μ; simp [e1]⟩

theorem nbr_iff (x y : T) : Nbr x y ↔ y = x + e1 ∨ x = y + e1 := by
  constructor
  · rintro ⟨μ, h | h⟩
    · left; rw [h]; congr 1; funext ν; simp [e1, Subsingleton.elim ν μ]
    · right; rw [h]; congr 1; funext ν; simp [e1, Subsingleton.elim ν μ]
  · rintro (h | h)
    · exact ⟨0, Or.inl (by rw [h]; congr 1; funext ν; simp [e1, Subsingleton.elim ν 0])⟩
    · exact ⟨0, Or.inr (by rw [h]; congr 1; funext ν; simp [e1, Subsingleton.elim ν 0])⟩

/-- Two sites cannot meet all four cubes `{i, i+1}` unless they are non-adjacent. -/
theorem core : ∀ x y : T, (y = x + e1 ∨ x = y + e1) →
    ¬ ((∀ i : Fin 4, ∃ u ∈ ({x, y} : Finset T), u = pt i ∨ u = pt i + e1)) := by
  decide +kernel

theorem core1 : ∀ x : T, ¬ ((∀ i : Fin 4, ∃ u ∈ ({x} : Finset T), u = pt i ∨ u = pt i + e1)) := by
  decide +kernel

theorem cellSide_eq : cellSide 2 0 0 0 = 1 := by simp [cellSide]

theorem aligned_one (b : T) : Aligned (cellSide 2 0 0 0) b := by
  intro μ; rw [cellSide_eq]; exact Nat.mod_one _

theorem scaleW_eq (x y : T) : scaleW 2 0 0 0 x y = 1 := by simp [scaleW]

theorem cost_eq (E : Finset (T × T)) : bondCost (scaleW 2 0 0 0) E = E.card := by
  simp [bondCost, scaleW_eq]

theorem box_mem_iff (b x : T) : x ∈ box b (2 * cellSide 2 0 0 0) ↔ x = b ∨ x = b + e1 := by
  rw [cellSide_eq]; exact mem_box_two b x

theorem pt_val (z : T) : pt (z 0).val = z := by
  funext μ; rw [Subsingleton.elim μ 0]; simp [pt]

theorem step_pt (k : ℕ) : Nbr (pt k) (pt (k + 1)) := by
  rw [nbr_iff]; left; funext μ; simp [pt, e1]

theorem fwd (a n : ℕ) :
    Relation.ReflTransGen (fun u v : T => u ∈ (Set.univ : Set T) ∧ v ∈ (Set.univ : Set T) ∧ Nbr u v)
      (pt a) (pt (a + n)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih => exact ih.tail ⟨trivial, trivial, step_pt (a + n)⟩

theorem wrap : ∀ a b : Fin 4, ∃ n : Fin 4, pt (b : ℕ) = pt ((a : ℕ) + n) := by decide +kernel

theorem isDj : IsDj 0 0 (Set.univ : Set T) := by
  refine ⟨⟨0, trivial⟩, fun z _ => ⟨z, aligned_one z, mem_box_self z (by rw [cellSide_eq]; norm_num),
    Set.subset_univ _⟩, fun x _ y _ => ?_⟩
  rw [← pt_val x, ← pt_val y]
  obtain ⟨n, hn⟩ := wrap ⟨(x 0).val % 4, Nat.mod_lt _ (by norm_num)⟩ ⟨(y 0).val % 4, Nat.mod_lt _ (by norm_num)⟩
  have hx : ∀ z : T, pt (z 0).val = pt ((z 0).val % 4) := by
    intro z; funext μ; simp [pt]
  rw [hx x, hx y]
  simpa [hn] using fwd ((x 0).val % 4) n

/-- The covering size is at most `1`. -/
theorem cov_le_one : treeLenCovOne 0 0 (Set.univ : Set T) ≤ 1 := by
  have hbdd : BddBelow {x | ∃ 𝒦 W E, ChosenOne 0 0 (Set.univ : Set T) 𝒦 ∧ ConnStruct W E ∧
      (↑W ⊆ (Set.univ : Set T)) ∧ MeetsOne 0 0 𝒦 W ∧ x = bondCost (scaleW 2 0 0 0) E} := by
    refine ⟨0, ?_⟩
    rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    exact bondCost_scaleW_nonneg E
  have hch : ChosenOne 0 0 (Set.univ : Set T) {b | b = pt 0 ∨ b = pt 2} := by
    refine ⟨fun b _ => ⟨aligned_one b, Set.subset_univ _⟩, fun z _ => ?_⟩
    have : ∀ z : T, z = pt 0 ∨ z = pt 0 + e1 ∨ z = pt 2 ∨ z = pt 2 + e1 := by decide +kernel
    rcases this z with h | h | h | h
    · exact ⟨pt 0, Or.inl rfl, (box_mem_iff _ _).2 (Or.inl h)⟩
    · exact ⟨pt 0, Or.inl rfl, (box_mem_iff _ _).2 (Or.inr h)⟩
    · exact ⟨pt 2, Or.inr rfl, (box_mem_iff _ _).2 (Or.inl h)⟩
    · exact ⟨pt 2, Or.inr rfl, (box_mem_iff _ _).2 (Or.inr h)⟩
  have hm : MeetsOne 0 0 {b : T | b = pt 0 ∨ b = pt 2} ({pt 1, pt 2} : Finset T) := by
    rintro b (rfl | rfl)
    · refine ⟨pt 1, by simp, (box_mem_iff _ _).2 (Or.inr ?_)⟩
      funext μ; simp [pt, e1]
    · exact ⟨pt 2, by simp, (box_mem_iff _ _).2 (Or.inl rfl)⟩
  have := csInf_le hbdd ⟨_, {pt 1, pt 2}, {(pt 1, pt 2)}, hch, connStruct_edge (step_pt 1),
    Set.subset_univ _, hm, rfl⟩
  refine this.trans (le_of_eq ?_)
  rw [cost_eq]; simp

/-- Every connected structure meeting all cubes `{i, i+1}` has at least two bonds. -/
theorem all_ge_two : (2 : ℝ) ≤ treeLenAll 0 0 (Set.univ : Set T) := by
  obtain ⟨W₁, E₁, h1, h2, h3⟩ := exists_tree_all isDj
  refine le_csInf ⟨_, W₁, E₁, h1, h2, h3, rfl⟩ ?_
  rintro x ⟨W, E, hW, -, hmeet, rfl⟩
  rw [cost_eq]
  by_contra hlt
  have hcard : E.card ≤ 1 := by
    have : (E.card : ℝ) < 2 := not_le.1 hlt
    have : E.card < 2 := by exact_mod_cast this
    omega
  have hfull : ∀ i : Fin 4, ∃ u ∈ W, u = pt i ∨ u = pt i + e1 := by
    intro i
    obtain ⟨u, huW, hu⟩ := hmeet (pt i) ⟨aligned_one _, Set.subset_univ _⟩
    exact ⟨u, huW, (box_mem_iff _ _).1 hu⟩
  obtain ⟨hne, hE, hconn⟩ := hW
  obtain ⟨w₀, hw₀⟩ := hne
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1'
  · rw [Finset.card_eq_zero] at h0
    subst h0
    have hsub : ∀ u ∈ W, u = w₀ := by
      intro u hu
      have := hconn w₀ hw₀ u hu
      induction this with
      | refl => rfl
      | tail _ hab _ => simp at hab
    refine core1 w₀ fun i => ?_
    obtain ⟨u, huW, hu⟩ := hfull i
    exact ⟨u, by simp [hsub u huW], hu⟩
  · obtain ⟨⟨x, y⟩, rfl⟩ := Finset.card_eq_one.1 h1'
    obtain ⟨hxW, hyW, hxy⟩ := hE (x, y) (by simp)
    have hsub : ∀ u ∈ W, u = x ∨ u = y := by
      intro u hu
      have := hconn x hxW u hu
      induction this with
      | refl => exact Or.inl rfl
      | tail _ hab ih =>
        simp only [Finset.mem_singleton, Prod.mk.injEq] at hab
        rcases hab with ⟨h, h'⟩ | ⟨h, h'⟩
        · rw [← h']; exact Or.inr rfl
        · rw [← h]; exact Or.inl rfl
    refine core x y ((nbr_iff x y).1 hxy) fun i => ?_
    obtain ⟨u, huW, hu⟩ := hfull i
    refine ⟨u, ?_, hu⟩
    rcases hsub u huW with rfl | rfl <;> simp

/-- **The two sizes differ** (T4): on the circle of four sites with `L = 2`, the domain `X` = the
whole circle has `treeLenCovOne X ≤ 1 < 2 ≤ treeLenAll X`. -/
theorem treeLenAll_ne_treeLenCovOne_example :
    IsDj 0 0 (Set.univ : Set T) ∧
      treeLenCovOne 0 0 (Set.univ : Set T) ≤ 1 ∧ 2 ≤ treeLenAll 0 0 (Set.univ : Set T) :=
  ⟨isDj, cov_le_one, all_ge_two⟩

theorem treeLenAll_ne_treeLenCovOne :
    treeLenAll 0 0 (Set.univ : Set T) ≠ treeLenCovOne 0 0 (Set.univ : Set T) := by
  have h1 := cov_le_one
  have h2 := all_ge_two
  intro h
  linarith

end PaperExample

end Balaban.Localization
