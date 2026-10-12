module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Paths on the boundary of a grid box

`ReachIn adj P u v n`: a path of `n` steps from `u` to `v` inside `P` for the adjacency `adj`.
For the integer grid `G s = ∏_i {0, …, s_i + 1}`, the boundary `Bd s` (points with some coordinate `0` or
`s_i + 1`) is connected in at most `2 ∑_i (s_i + 1)` steps for `d ≥ 2` (`boundary_reach`); this is the
path used for the reference vector (Lemma III.3.5, P7 (2.20)).
-/

@[expose] public section

namespace Balaban.LargeField

open Finset

/-- A path of `n` steps inside `P`. -/
inductive ReachIn {α : Type*} (adj : α → α → Prop) (P : Set α) : α → α → ℕ → Prop
  | refl (u : α) : u ∈ P → ReachIn adj P u u 0
  | step {u v w : α} {n : ℕ} : ReachIn adj P u v n → w ∈ P → adj v w → ReachIn adj P u w (n + 1)

namespace ReachIn

variable {α β : Type*} {adj : α → α → Prop} {P : Set α}

theorem trans {u v w : α} {n k : ℕ} (h1 : ReachIn adj P u v n) (h2 : ReachIn adj P v w k) :
    ReachIn adj P u w (n + k) := by
  induction h2 with
  | refl => exact h1
  | step _ hw ha ih => exact ReachIn.step ih hw ha

theorem mono {P' : Set α} (hP : P ⊆ P') {u v : α} {n : ℕ} (h : ReachIn adj P u v n) :
    ReachIn adj P' u v n := by
  induction h with
  | refl hu => exact ReachIn.refl _ (hP hu)
  | step _ hw ha ih => exact ReachIn.step ih (hP hw) ha

theorem map {adj' : β → β → Prop} {P' : Set β} (f : α → β) (hf : ∀ x y, adj x y → adj' (f x) (f y))
    (hP : ∀ x ∈ P, f x ∈ P') {u v : α} {n : ℕ} (h : ReachIn adj P u v n) :
    ReachIn adj' P' (f u) (f v) n := by
  induction h with
  | refl hu => exact ReachIn.refl _ (hP _ hu)
  | step _ hw ha ih => exact ReachIn.step ih (hP _ hw) (hf _ _ ha)

theorem mem_left {u v : α} {n : ℕ} (h : ReachIn adj P u v n) : u ∈ P := by
  induction h with
  | refl hu => exact hu
  | step _ _ _ ih => exact ih

theorem mem_right {u v : α} {n : ℕ} (h : ReachIn adj P u v n) : v ∈ P := by
  cases h with
  | refl hu => exact hu
  | step _ hw _ => exact hw

end ReachIn

section Grid

variable {d : ℕ}

/-- Adjacency on `ℤ^d`: differ by `±1` in one coordinate. -/
def gridAdj (v w : Fin d → ℤ) : Prop :=
  ∃ (i : Fin d) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ w = Function.update v i (v i + ε)

/-- The box `∏_i {0, …, s_i + 1}`. -/
def gridBox (s : Fin d → ℕ) : Set (Fin d → ℤ) := {u | ∀ i, 0 ≤ u i ∧ u i ≤ (s i : ℤ) + 1}

/-- Its boundary: some coordinate is `0` or `s_i + 1`. -/
def gridBd (s : Fin d → ℕ) : Set (Fin d → ℤ) :=
  {u | u ∈ gridBox s ∧ ∃ i, u i = 0 ∨ u i = (s i : ℤ) + 1}

/-- A move along the coordinate `i` to the value `t`, through points `update u i t'` all lying in `P`. -/
theorem reach_line {P : Set (Fin d → ℤ)} (i : Fin d) (t : ℤ) :
    ∀ (n : ℕ) (u : Fin d → ℤ), (u i - t).natAbs = n →
      (∀ t' : ℤ, min (u i) t ≤ t' → t' ≤ max (u i) t → Function.update u i t' ∈ P) →
      ReachIn gridAdj P u (Function.update u i t) n := by
  intro n
  induction n with
  | zero =>
    intro u hu hP
    have : u i = t := by omega
    have hu' : Function.update u i t = u := by rw [← this]; simp
    rw [hu']
    have h0 := hP (u i) (by simp [this]) (by simp [this])
    rw [Function.update_eq_self] at h0
    exact ReachIn.refl u h0
  | succ n ih =>
    intro u hu hP
    -- first step towards `t`
    set ε : ℤ := if u i < t then 1 else -1 with hε
    have hne : u i ≠ t := by intro h; rw [h] at hu; simp at hu
    set u1 := Function.update u i (u i + ε) with hu1
    have hu1i : u1 i = u i + ε := by simp [hu1]
    have h1 : (u1 i - t).natAbs = n := by
      rw [hu1i, hε]; split_ifs with h
      · omega
      · omega
    have hmem : ∀ t' : ℤ, min (u1 i) t ≤ t' → t' ≤ max (u1 i) t → Function.update u1 i t' ∈ P := by
      intro t' ha hb
      have : Function.update u1 i t' = Function.update u i t' := by simp [hu1]
      rw [this]
      refine hP t' ?_ ?_
      · rw [hu1i, hε] at ha; split_ifs at ha with h <;> omega
      · rw [hu1i, hε] at hb; split_ifs at hb with h <;> omega
    have := ih u1 h1 hmem
    have hstep : ReachIn gridAdj P u u1 1 := by
      have hu0 : u ∈ P := by
        have := hP (u i) (by simp) (by simp)
        rwa [Function.update_eq_self] at this
      refine ReachIn.step (ReachIn.refl u hu0) ?_ ?_
      · have : u1 = Function.update u i (u i + ε) := rfl
        rw [this]
        refine hP _ ?_ ?_ <;> (rw [hε]; split_ifs with h <;> omega)
      · exact ⟨i, ε, by rw [hε]; split_ifs <;> simp, rfl⟩
    have e : Function.update u1 i t = Function.update u i t := by simp [hu1]
    rw [e] at this
    simpa [Nat.add_comm] using hstep.trans this

theorem update_mem_gridBox {s : Fin d → ℕ} {u : Fin d → ℤ} (hu : u ∈ gridBox s) (i : Fin d) {t : ℤ}
    (h0 : 0 ≤ t) (h1 : t ≤ (s i : ℤ) + 1) : Function.update u i t ∈ gridBox s := by
  intro j
  by_cases h : j = i
  · subst h; simp [h0, h1]
  · simp [h, hu j]

/-- Moving the coordinates in `I` of a point to those of a target, inside the box and a set `Q` that is
closed under changing the coordinates in `I`. -/
theorem reach_coords {s : Fin d → ℕ} {Q : Set (Fin d → ℤ)} (I : Finset (Fin d))
    (hQ : ∀ w ∈ Q, ∀ i ∈ I, ∀ t : ℤ, Function.update w i t ∈ Q) :
    ∀ (w w' : Fin d → ℤ), w ∈ gridBox s → w ∈ Q → w' ∈ gridBox s → (∀ i, i ∉ I → w' i = w i) →
      ReachIn gridAdj (gridBox s ∩ Q) w w' (∑ i ∈ I, (w i - w' i).natAbs) := by
  induction I using Finset.induction_on with
  | empty =>
    intro w w' hw hQw hw' hag
    have : w' = w := funext fun i => hag i (by simp)
    subst this
    exact (by simpa using ReachIn.refl _ (show _ ∈ gridBox s ∩ Q from ⟨hw, hQw⟩))
  | insert i I' hi ih =>
    intro w w' hw hQw hw' hag
    have hQ' : ∀ w ∈ Q, ∀ j ∈ I', ∀ t : ℤ, Function.update w j t ∈ Q :=
      fun w hw j hj t => hQ w hw j (Finset.mem_insert_of_mem hj) t
    set w1 := Function.update w i (w' i) with hw1
    have hw1box : w1 ∈ gridBox s := update_mem_gridBox hw i (hw' i).1 (hw' i).2
    have hw1Q : w1 ∈ Q := hQ w hQw i (Finset.mem_insert_self _ _) _
    have hline : ReachIn gridAdj (gridBox s ∩ Q) w w1 (w i - w' i).natAbs := by
      refine reach_line i (w' i) _ w rfl ?_
      intro t' ha hb
      refine ⟨?_, hQ w hQw i (Finset.mem_insert_self _ _) _⟩
      refine update_mem_gridBox hw i ?_ ?_
      · have := (hw i).1; have := (hw' i).1; omega
      · have := (hw i).2; have := (hw' i).2; omega
    have hag' : ∀ j, j ∉ I' → w' j = w1 j := by
      intro j hj
      by_cases hji : j = i
      · subst hji; simp [hw1]
      · simp only [hw1, Function.update_of_ne hji]
        exact hag j (by simp [hji, hj])
    have hrest := ih hQ' w1 w' hw1box hw1Q hw' hag'
    rw [Finset.sum_insert hi]
    have hsum : ∑ j ∈ I', (w1 j - w' j).natAbs = ∑ j ∈ I', (w j - w' j).natAbs := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [hw1, Function.update_of_ne hji]
    rw [hsum] at hrest
    exact hline.trans hrest

theorem gridBd_subset_gridBox (s : Fin d → ℕ) : gridBd s ⊆ gridBox s := fun _ h => h.1

/-- Two boundary points on the same face are joined inside the face by at most `∑ (s_i + 1)` steps. -/
theorem face_reach {s : Fin d → ℕ} {i0 : Fin d} {σ : ℤ} (hσ : σ = 0 ∨ σ = (s i0 : ℤ) + 1)
    {w w' : Fin d → ℤ} (hw : w ∈ gridBox s) (hw' : w' ∈ gridBox s) (h1 : w i0 = σ) (h2 : w' i0 = σ) :
    ∃ n ≤ ∑ i, (s i + 1), ReachIn gridAdj (gridBd s) w w' n := by
  classical
  have hQ : ∀ x ∈ {x : Fin d → ℤ | x i0 = σ}, ∀ i ∈ Finset.univ.erase i0, ∀ t : ℤ,
      Function.update x i t ∈ {x : Fin d → ℤ | x i0 = σ} := by
    intro x hx i hi t
    have : i0 ≠ i := fun h => (Finset.mem_erase.mp hi).1 h.symm
    simpa [Function.update_of_ne this] using hx
  have := reach_coords (s := s) (Q := {x : Fin d → ℤ | x i0 = σ}) (Finset.univ.erase i0) hQ w w' hw h1 hw'
    (fun i hi => by
      have : i = i0 := by simpa using hi
      subst this; rw [h1, h2])
  refine ⟨_, ?_, this.mono ?_⟩
  · calc ∑ i ∈ Finset.univ.erase i0, (w i - w' i).natAbs ≤ ∑ i ∈ Finset.univ.erase i0, (s i + 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hw i; have := hw' i; omega
      _ ≤ ∑ i, (s i + 1) := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  · intro x hx
    exact ⟨hx.1, i0, by rcases hσ with h | h <;> [left; right] <;> (rw [← h]; exact hx.2)⟩

/-- **The boundary of a grid box is connected** (`d ≥ 2`): any two boundary points are joined inside the boundary
by at most `2 ∑_i (s_i + 1)` steps. -/
theorem boundary_reach (hd : 2 ≤ d) {s : Fin d → ℕ} {u v : Fin d → ℤ} (hu : u ∈ gridBd s)
    (hv : v ∈ gridBd s) : ∃ n ≤ 2 * ∑ i, (s i + 1), ReachIn gridAdj (gridBd s) u v n := by
  classical
  obtain ⟨hub, i0, hi0⟩ := hu
  obtain ⟨hvb, j0, hj0⟩ := hv
  set Stot := ∑ i, (s i + 1) with hStot
  have hle : ∀ i, s i + 1 ≤ Stot := fun i =>
    Finset.single_le_sum (f := fun i => s i + 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  by_cases hij : j0 = i0
  · subst hij
    by_cases hsame : u j0 = v j0
    · obtain ⟨n, hn, h⟩ := face_reach (σ := u j0) hi0 hub hvb rfl hsame.symm
      exact ⟨n, by omega, h⟩
    · -- opposite faces
      obtain ⟨i1, hi1⟩ : ∃ i1 : Fin d, i1 ≠ j0 := by
        by_contra hcon
        push Not at hcon
        have : Fintype.card (Fin d) ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by
          rw [hcon a, hcon b]
        simp at this; omega
      -- u → u1 (coordinate i1 set to 0), inside the face of `u`
      set u1 := Function.update u i1 0 with hu1
      have hu1box : u1 ∈ gridBox s := update_mem_gridBox hub i1 le_rfl (by positivity)
      have hu1i0 : u1 j0 = u j0 := by simp [hu1, Function.update_of_ne hi1.symm]
      have h1 : ReachIn gridAdj (gridBd s) u u1 (u i1 - 0).natAbs := by
        refine reach_line i1 0 _ u rfl ?_
        intro t' ha hb
        refine ⟨update_mem_gridBox hub i1 ?_ ?_, j0, ?_⟩
        · have := (hub i1).1; omega
        · have := (hub i1).2; omega
        · simpa [Function.update_of_ne hi1.symm] using hi0
      have hn1 : (u i1 - 0).natAbs ≤ s i1 + 1 := by
        have := (hub i1).1; have := (hub i1).2; omega
      -- u1 → u2 (coordinate j0 moved to v j0), inside the face `i1 = 0`
      set u2 := Function.update u1 j0 (v j0) with hu2
      have hu2box : u2 ∈ gridBox s := update_mem_gridBox hu1box j0 (hvb j0).1 (hvb j0).2
      have hline : ReachIn gridAdj (gridBd s) u1 u2 (u1 j0 - v j0).natAbs := by
        refine reach_line j0 (v j0) _ u1 rfl ?_
        intro t' ha hb
        refine ⟨update_mem_gridBox hu1box j0 ?_ ?_, i1, Or.inl ?_⟩
        · have := (hub j0).1; have := (hvb j0).1; omega
        · have := (hub j0).2; have := (hvb j0).2; omega
        · simp [Function.update_of_ne hi1]; simp [hu1]
      have hn2 : (u1 j0 - v j0).natAbs ≤ s j0 + 1 := by
        have := (hub j0).1; have := (hub j0).2; have := (hvb j0).1; have := (hvb j0).2
        rw [hu1i0]; omega
      -- u2 → v inside the face of `v`
      have hu2j : u2 j0 = v j0 := by simp [hu2]
      obtain ⟨n3, hn3, h3⟩ := face_reach (σ := v j0) hj0 hu2box hvb hu2j rfl
      have hpair : (s i1 + 1) + (s j0 + 1) ≤ Stot := by
        have := Finset.sum_le_sum_of_subset (f := fun k => s k + 1) (Finset.subset_univ {i1, j0})
        rwa [Finset.sum_pair hi1] at this
      exact ⟨(u i1 - 0).natAbs + (u1 j0 - v j0).natAbs + n3, by omega,
        (h1.trans hline).trans h3⟩
  · -- different faces
    set u1 := Function.update u j0 (v j0) with hu1
    have hu1box : u1 ∈ gridBox s := update_mem_gridBox hub j0 (hvb j0).1 (hvb j0).2
    have hu1i0 : u1 i0 = u i0 := by simp [hu1, Function.update_of_ne (Ne.symm hij)]
    have hline : ReachIn gridAdj (gridBd s) u u1 (u j0 - v j0).natAbs := by
      have := reach_line (P := gridBd s) j0 (v j0) _ u rfl (by
        intro t' ha hb
        refine ⟨update_mem_gridBox hub j0 ?_ ?_, i0, ?_⟩
        · have := (hub j0).1; have := (hvb j0).1; omega
        · have := (hub j0).2; have := (hvb j0).2; omega
        · simpa [Function.update_of_ne (Ne.symm hij)] using hi0)
      exact this
    have hn1 : (u j0 - v j0).natAbs ≤ s j0 + 1 := by
      have := (hub j0).1; have := (hub j0).2; have := (hvb j0).1; have := (hvb j0).2; omega
    have hu1j : u1 j0 = v j0 := by simp [hu1]
    obtain ⟨n3, hn3, h3⟩ := face_reach (σ := v j0) hj0 hu1box hvb hu1j rfl
    exact ⟨_, by have := hle j0; omega, hline.trans h3⟩

end Grid

end Balaban.LargeField
