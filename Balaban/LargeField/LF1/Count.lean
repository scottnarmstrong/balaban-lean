/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.Struct
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Counting lemmas for LF-1

* `sum_adj_le`: a sum over ordered nearest-neighbour pairs is at most the two directed sums;
* `pairSumT_le`: the unordered pair sum is at most the directed sum `∑_μ ∑_y 1_{y,y+e_μ∈T}‖f y - f (y+e_μ)‖²`;
* `sum_bondEdir_union_le`: `∑_y bondEdir μ (B_y ∪ B_{y+v}) ≤ 2 bondEdir μ S`: a bond lies in at
  most two such unions.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Generic

variable {E : Type*} [NormedAddCommGroup E]

theorem sq_norm_add3_le (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (by linarith [norm_add_le a b])
  have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

end Generic

section Adj

variable {d m : ℕ} [NeZero m]

open Classical in
/-- A sum over ordered nearest-neighbour pairs satisfying `K` is at most the two directed sums. -/
theorem sum_adj_le (K : Torus d m → Torus d m → Prop) [∀ y y', Decidable (K y y')] (F : Torus d m → Torus d m → ℝ)
    (hF : ∀ y y', 0 ≤ F y y') :
    ∑ y, ∑ y', (if AdjT y y' ∧ K y y' then F y y' else 0) ≤
      ∑ μ : Fin d, ∑ y, (if K y (y + Pi.single μ 1) then F y (y + Pi.single μ 1) else 0) +
      ∑ μ : Fin d, ∑ y, (if K y (y + -Pi.single μ 1) then F y (y + -Pi.single μ 1) else 0) := by
  set gp : Torus d m → Torus d m → Fin d → ℝ := fun y y' μ =>
    if y' = y + Pi.single μ 1 ∧ K y y' then F y y' else 0 with hgp
  set gm : Torus d m → Torus d m → Fin d → ℝ := fun y y' μ =>
    if y' = y + -Pi.single μ 1 ∧ K y y' then F y y' else 0 with hgm
  have hgp0 : ∀ y y' μ, 0 ≤ gp y y' μ := fun y y' μ => by
    rw [hgp]; simp only; split_ifs
    exacts [hF _ _, le_rfl]
  have hgm0 : ∀ y y' μ, 0 ≤ gm y y' μ := fun y y' μ => by
    rw [hgm]; simp only; split_ifs
    exacts [hF _ _, le_rfl]
  have hpt : ∀ y y', (if AdjT y y' ∧ K y y' then F y y' else 0) ≤
      ∑ μ : Fin d, (gp y y' μ + gm y y' μ) := by
    intro y y'
    by_cases h : AdjT y y' ∧ K y y'
    · rw [ite_eq_left h]
      obtain ⟨⟨hne, μ, hμ⟩, hK⟩ := h
      have hsingle := Finset.single_le_sum (f := fun μ => gp y y' μ + gm y y' μ)
        (fun μ _ => add_nonneg (hgp0 y y' μ) (hgm0 y y' μ)) (Finset.mem_univ μ)
      refine le_trans ?_ hsingle
      rcases hμ with h1 | h1
      · have : gp y y' μ = F y y' := by rw [hgp]; simp only; rw [ite_eq_left ⟨h1, hK⟩]
        simp only [this]; linarith [hgm0 y y' μ]
      · have h2 : y' = y + -Pi.single μ 1 := by rw [h1]; abel
        have : gm y y' μ = F y y' := by rw [hgm]; simp only; rw [ite_eq_left ⟨h2, hK⟩]
        simp only [this]; linarith [hgp0 y y' μ]
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun μ _ => add_nonneg (hgp0 y y' μ) (hgm0 y y' μ)
  have e1 : ∀ (y : Torus d m) (c : Torus d m), ∑ y', (if y' = c ∧ K y y' then F y y' else 0) =
      if K y c then F y c else 0 := by
    intro y c
    rw [Finset.sum_eq_single c]
    · by_cases hK : K y c <;> simp [hK]
    · intro b _ hb; simp [hb]
    · simp
  calc ∑ y, ∑ y', (if AdjT y y' ∧ K y y' then F y y' else 0)
      ≤ ∑ y, ∑ y', ∑ μ : Fin d, (gp y y' μ + gm y y' μ) :=
        Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun y' _ => hpt y y'
    _ = ∑ y, ∑ μ : Fin d, ∑ y', (gp y y' μ + gm y y' μ) :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ y, ∑ y', (gp y y' μ + gm y y' μ) := Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ y, ((∑ y', gp y y' μ) + ∑ y', gm y y' μ) := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by
        rw [Finset.sum_congr rfl fun μ _ => Finset.sum_add_distrib]
        rw [Finset.sum_add_distrib]
        congr 1
        · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun y _ => ?_
          rw [hgp]; exact e1 y _
        · refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun y _ => ?_
          rw [hgm]; exact e1 y _

theorem sum_mem_eq {α : Type*} [Fintype α] [DecidableEq α] (T : Finset α) (g : α → ℝ) :
    ∑ y ∈ T, g y = ∑ y, if y ∈ T then g y else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext y; simp

/-- Reindexing a sum over the torus by a translation. -/
theorem sum_shift {d m : ℕ} [NeZero m] (v : Torus d m) (g : Torus d m → ℝ) :
    ∑ y, g (y + v) = ∑ y, g y :=
  Fintype.sum_equiv (Equiv.addRight v) _ _ fun _ => rfl

open Classical in
/-- The unordered pair sum is at most the directed sum. -/
theorem pairSumT_le {E : Type*} [NormedAddCommGroup E] (T : Finset (Torus d m))
    (f : Torus d m → E) :
    pairSumT T f ≤ ∑ μ : Fin d, ∑ y,
      (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then ‖f y - f (y + Pi.single μ 1)‖ ^ 2 else 0) := by
  unfold pairSumT
  have h0 : ∀ y y' : Torus d m, 0 ≤ ‖f y - f y'‖ ^ 2 := fun _ _ => by positivity
  have hrew : ∑ y ∈ T, ∑ y' ∈ T, (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) =
      ∑ y, ∑ y', (if AdjT y y' ∧ (y ∈ T ∧ y' ∈ T) then ‖f y - f y'‖ ^ 2 else 0) := by
    rw [sum_mem_eq]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ T
    · simp only [hy, ↓reduceIte]
      rw [sum_mem_eq]
      refine Finset.sum_congr rfl fun y' _ => ?_
      by_cases hy' : y' ∈ T <;> simp [hy']
    · simp [hy]
  rw [hrew]
  have key := sum_adj_le (fun y y' => y ∈ T ∧ y' ∈ T) (fun y y' => ‖f y - f y'‖ ^ 2) h0
  have hsym : ∑ μ : Fin d, ∑ y, (if y ∈ T ∧ y + -Pi.single μ 1 ∈ T then
        ‖f y - f (y + -Pi.single μ 1)‖ ^ 2 else 0) =
      ∑ μ : Fin d, ∑ y, (if y ∈ T ∧ y + Pi.single μ 1 ∈ T then
        ‖f y - f (y + Pi.single μ 1)‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← sum_shift (Pi.single μ 1 : Torus d m)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e : y + Pi.single μ 1 + -Pi.single μ 1 = y := by abel
    simp only [e]
    by_cases h : y + Pi.single μ 1 ∈ T ∧ y ∈ T
    · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩, norm_sub_rev]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]
  rw [hsym] at key
  linarith

open Classical in
theorem sum_shift_le_self {d m : ℕ} [NeZero m] (T : Finset (Torus d m)) (v : Torus d m)
    (g : Torus d m → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ y, (if y ∈ T ∧ y + v ∈ T then g (y + v) else 0) ≤ ∑ y ∈ T, g y := by
  rw [sum_mem_eq T g]
  calc ∑ y, (if y ∈ T ∧ y + v ∈ T then g (y + v) else 0)
      ≤ ∑ y, (if y + v ∈ T then g (y + v) else 0) :=
        Finset.sum_le_sum fun y _ => by
          by_cases h : y ∈ T ∧ y + v ∈ T
          · rw [ite_eq_left h, ite_eq_left h.2]
          · by_cases h2 : y + v ∈ T
            · rw [ite_eq_right h, ite_eq_left h2]; exact hg _
            · rw [ite_eq_right h, ite_eq_right h2]
    _ = ∑ y, (if y ∈ T then g y else 0) := sum_shift v (fun y => if y ∈ T then g y else 0)

open Classical in
theorem sum_ite_le_self {d m : ℕ} [NeZero m] (T : Finset (Torus d m)) (P : Torus d m → Prop)
    [DecidablePred P] (g : Torus d m → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ y, (if y ∈ T ∧ P y then g y else 0) ≤ ∑ y ∈ T, g y := by
  rw [sum_mem_eq T g]
  refine Finset.sum_le_sum fun y _ => ?_
  by_cases h : y ∈ T ∧ P y
  · rw [ite_eq_left h, ite_eq_left h.1]
  · by_cases h2 : y ∈ T
    · rw [ite_eq_right h, ite_eq_left h2]; exact hg _
    · rw [ite_eq_right h, ite_eq_right h2]

end Adj

section Bonds

variable {E : Type*} [NormedAddCommGroup E] {d L N₀ q : ℕ} [NeZero N₀] [NeZero L]

open Classical in
/-- A bond lies in at most two of the sets `B_y ∪ B_{y+v}`:
`∑_y bondEdir μ (B_y ∪ B_{y+v}) ≤ 2 bondEdir μ S`. -/
theorem sum_bondEdir_union_le {n : ℕ} (μ : Fin d) (v : Blk d L N₀ q n)
    (P : Finset (Blk d L N₀ q n)) (S : Finset (Site d L N₀ q))
    (hP : ∀ y ∈ P, fib d L N₀ q n y ∪ fib d L N₀ q n (y + v) ⊆ S) (φ : Site d L N₀ q → E) :
    ∑ y ∈ P, bondEdir μ (fib d L N₀ q n y ∪ fib d L N₀ q n (y + v)) φ ≤
      2 * bondEdir μ S φ := by
  unfold bondEdir
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  set t := bondTerm φ μ x with ht
  have ht0 : 0 ≤ t := bondTerm_nonneg φ μ x
  by_cases hS : x ∈ S ∧ x + Pi.single μ 1 ∈ S
  · rw [ite_eq_left hS]
    have hsub : P.filter (fun y => x ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v) ∧
        x + Pi.single μ 1 ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v)) ⊆
        {blkMap d L N₀ q n x, blkMap d L N₀ q n x - v} := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨-, hx, -⟩ := hy
      rcases Finset.mem_union.1 hx with h | h
      · rw [mem_fib] at h
        simp [h]
      · rw [mem_fib] at h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        exact eq_sub_of_add_eq h.symm
    calc ∑ y ∈ P, (if x ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v) ∧
          x + Pi.single μ 1 ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v) then t else 0)
        = ((P.filter (fun y => x ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v) ∧
            x + Pi.single μ 1 ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v))).card : ℝ) * t := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * t := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two) ht0
  · rw [ite_eq_right hS, mul_zero]
    refine Finset.sum_nonpos fun y hy => ?_
    by_cases h : x ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v) ∧
        x + Pi.single μ 1 ∈ fib d L N₀ q n y ∪ fib d L N₀ q n (y + v)
    · exact absurd ⟨hP y hy h.1, hP y hy h.2⟩ hS
    · rw [ite_eq_right h]

end Bonds

end Balaban.LargeField
