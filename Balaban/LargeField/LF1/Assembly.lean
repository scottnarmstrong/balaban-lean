/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.LF1.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Summation over the scales for LF-1

The multiplicities of bonds over the layers (`sum_bondE_lam_le`, `sum_bondE_cross_le`), the sums over
`n` and the comparison with the action.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Mult

variable {E : Type*} [NormedAddCommGroup E] {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

open Classical in
/-- If every site lies in at most `c` of the sets `S i ⊆ X`, then
`∑_i bondEdir μ (S i) ≤ c · bondEdir μ X`. -/
theorem sum_bondEdir_family_le {ι : Type*} (I : Finset ι) (S : ι → Finset (Site d L N₀ q))
    (X : Finset (Site d L N₀ q)) (hSX : ∀ i ∈ I, S i ⊆ X) (c : ℕ)
    (hc : ∀ x, (I.filter fun i => x ∈ S i).card ≤ c) (φ : Site d L N₀ q → E) (μ : Fin d) :
    ∑ i ∈ I, bondEdir μ (S i) φ ≤ c * bondEdir μ X φ := by
  unfold bondEdir
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have ht0 : 0 ≤ bondTerm φ μ x := bondTerm_nonneg φ μ x
  by_cases hX : x ∈ X ∧ x + Pi.single μ 1 ∈ X
  · rw [ite_eq_left hX]
    calc ∑ i ∈ I, (if x ∈ S i ∧ x + Pi.single μ 1 ∈ S i then bondTerm φ μ x else 0)
        = ((I.filter fun i => x ∈ S i ∧ x + Pi.single μ 1 ∈ S i).card : ℝ) * bondTerm φ μ x := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ c * bondTerm φ μ x := by
          refine mul_le_mul_of_nonneg_right ?_ ht0
          exact_mod_cast (Finset.card_le_card (fun i hi => by
            simp only [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hi.2.1⟩)).trans (hc x)
  · rw [ite_eq_right hX, mul_zero]
    refine Finset.sum_nonpos fun i hi => ?_
    by_cases h : x ∈ S i ∧ x + Pi.single μ 1 ∈ S i
    · exact absurd ⟨hSX i hi h.1, hSX i hi h.2⟩ hX
    · rw [ite_eq_right h]

theorem sum_bondE_family_le {ι : Type*} (I : Finset ι) (S : ι → Finset (Site d L N₀ q))
    (X : Finset (Site d L N₀ q)) (hSX : ∀ i ∈ I, S i ⊆ X) (c : ℕ)
    (hc : ∀ x, (I.filter fun i => x ∈ S i).card ≤ c) (φ : Site d L N₀ q → E) :
    ∑ i ∈ I, bondE (S i) φ ≤ c * bondE X φ := by
  unfold bondE
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun μ _ => sum_bondEdir_family_le I S X hSX c hc φ μ

/-- Each bond lies in one layer: `∑_{n ≤ q} E(Λ_n ∩ X) ≤ E(X)`. -/
theorem sum_bondE_lam_le (G : GeneratingSet d L N₀ q ϱ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → E) :
    ∑ n ∈ Finset.range (q + 1), bondE (lam G n ∩ X) φ ≤ bondE X φ := by
  classical
  have := sum_bondE_family_le (Finset.range (q + 1)) (fun n => lam G n ∩ X) X
    (fun n _ => Finset.inter_subset_right) 1 (fun x => ?_) φ
  · simpa using this
  · have : (Finset.range (q + 1)).filter (fun n => x ∈ lam G n ∩ X) ⊆ {G.layerIndex x} := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      rw [Finset.mem_singleton]
      exact ((mem_lam_iff G (by omega) x).1 (Finset.mem_inter.1 hn.2).1).symm
    exact (Finset.card_le_card this).trans (by simp)

/-- Each bond lies in at most two of the sets `(Λ_n ∪ Λ_{n+1}) ∩ X`. -/
theorem sum_bondE_cross_le (G : GeneratingSet d L N₀ q ϱ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → E) :
    ∑ n ∈ Finset.range q, bondE ((lam G n ∪ lam G (n + 1)) ∩ X) φ ≤ 2 * bondE X φ := by
  classical
  have := sum_bondE_family_le (Finset.range q) (fun n => (lam G n ∪ lam G (n + 1)) ∩ X) X
    (fun n _ => Finset.inter_subset_right) 2 (fun x => ?_) φ
  · simpa using this
  · have : (Finset.range q).filter (fun n => x ∈ (lam G n ∪ lam G (n + 1)) ∩ X) ⊆
        {G.layerIndex x, G.layerIndex x - 1} := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      have h1 := (Finset.mem_inter.1 hn.2).1
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases Finset.mem_union.1 h1 with h | h
      · left; exact ((mem_lam_iff G (by omega) x).1 h).symm
      · right
        have := (mem_lam_iff G (by omega) x).1 h
        omega
    exact (Finset.card_le_card this).trans Finset.card_le_two

/-- Counting form of a partition: `∑_i ∑_{x ∈ S i} F x ≤ c ∑_{x ∈ X} F x`. -/
theorem sum_sum_family_le {ι α : Type*} [DecidableEq α] (I : Finset ι) (S : ι → Finset α) (X : Finset α)
    (hSX : ∀ i ∈ I, S i ⊆ X) (c : ℕ) (hc : ∀ x, (I.filter fun i => x ∈ S i).card ≤ c)
    (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) :
    ∑ i ∈ I, ∑ x ∈ S i, F x ≤ c * ∑ x ∈ X, F x := by
  have h1 : ∀ i ∈ I, ∑ x ∈ S i, F x = ∑ x ∈ X, if x ∈ S i then F x else 0 := by
    intro i hi
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hSX i hi h, h⟩, fun h => h.2⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  calc ∑ i ∈ I, (if x ∈ S i then F x else 0)
      = ((I.filter fun i => x ∈ S i).card : ℝ) * F x := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ c * F x := mul_le_mul_of_nonneg_right (by exact_mod_cast hc x) (hF x)

end Mult

section Sums

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (q : ℕ) :
    ∑ n ∈ Finset.Icc 1 q, f n = ∑ n ∈ Finset.range q, f (n + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

end Sums

section Total

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ} [NeZero N₀]
  [NeZero L] {ϱ : ℝ}

/-- The weighted block variance `Bk_n = L^{n(d-2)} ∑_{y ∈ T_n(Λ_n ∩ X)} ‖ψ_n(y) - Q_n φ(y)‖²`. -/
noncomputable def bk (G : GeneratingSet d L N₀ q ϱ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → E) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (n : ℕ) : ℝ :=
  (L : ℝ) ^ (n * (d - 2)) * ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
    ‖psiFull φ ψ n y - bavgL d L N₀ q n φ y‖ ^ 2

theorem bk_nonneg (G : GeneratingSet d L N₀ q ϱ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → E) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (n : ℕ) : 0 ≤ bk G X φ ψ n :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

theorem bk_zero (G : GeneratingSet d L N₀ q ϱ) (X : Finset (Site d L N₀ q))
    (φ : Site d L N₀ q → E) (ψ : (m : ℕ) → Blk d L N₀ q m → E) : bk G X φ ψ 0 = 0 := by
  unfold bk
  rw [Finset.sum_eq_zero, mul_zero]
  intro y _
  rw [psiFull_zero, sub_self, norm_zero]; norm_num

/-- **Total bound of Theorem II.4.1 (a)**. -/
theorem total_bound (G : GeneratingSet d L N₀ q ϱ) (hd : 2 ≤ d) (hL : 2 ≤ L)
    (hϱ : 2 * (d : ℝ) * L ≤ ϱ) (X : Finset (Site d L N₀ q))
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n)) (φ : Site d L N₀ q → E)
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) :
    ∑ n ∈ Finset.range (q + 1), ((L : ℝ) ^ (n * (d - 2)) / 2) *
        pairSumT (tBlocks d L N₀ q n (lam G n ∩ X)) (psiFull φ ψ n) +
      ∑ n ∈ Finset.range q, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) * crossSumP G n X (psiFull φ ψ) ≤
    7 * d * ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n + 15 * bondE X φ := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hE0 := bondE_nonneg X φ
  have hI : ∀ n ∈ Finset.range (q + 1), ((L : ℝ) ^ (n * (d - 2)) / 2) *
        pairSumT (tBlocks d L N₀ q n (lam G n ∩ X)) (psiFull φ ψ n) ≤
      3 * d * bk G X φ ψ n + 3 * bondE (lam G n ∩ X) φ := fun n hn =>
    intra_bound (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) hd _
      (isBlockUnion_lam G hX (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))) φ _
  have hC : ∀ n ∈ Finset.range q, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
        crossSumP G n X (psiFull φ ψ) ≤
      3 * d * bk G X φ ψ (n + 1) + (3 * d / 4) * bk G X φ ψ n +
        6 * bondE ((lam G n ∪ lam G (n + 1)) ∩ X) φ := fun n hn =>
    cross_bound G (Finset.mem_range.1 hn) hd hL hϱ X φ (psiFull φ ψ)
      (fun y => psiFull_zero φ ψ y)
  have hBf : ∑ n ∈ Finset.range (q + 1), bk G X φ ψ n = ∑ n ∈ Finset.Icc 1 q, bk G X φ ψ n := by
    rw [sum_Icc_one_eq_sum_range (bk G X φ ψ) q, Finset.sum_range_succ', bk_zero, add_zero]
  have hsh : ∑ n ∈ Finset.range q, bk G X φ ψ (n + 1) = ∑ n ∈ Finset.range (q + 1), bk G X φ ψ n := by
    rw [Finset.sum_range_succ', bk_zero, add_zero]
  have hle : ∑ n ∈ Finset.range q, bk G X φ ψ n ≤ ∑ n ∈ Finset.range (q + 1), bk G X φ ψ n := by
    rw [Finset.sum_range_succ]; linarith [bk_nonneg G X φ ψ q]
  have hS1 := sum_bondE_lam_le G X φ
  have hS2 := sum_bondE_cross_le G X φ
  have e1 : ∑ n ∈ Finset.range (q + 1), ((L : ℝ) ^ (n * (d - 2)) / 2) *
        pairSumT (tBlocks d L N₀ q n (lam G n ∩ X)) (psiFull φ ψ n) ≤
      3 * d * ∑ n ∈ Finset.range (q + 1), bk G X φ ψ n +
        3 * ∑ n ∈ Finset.range (q + 1), bondE (lam G n ∩ X) φ := by
    refine (Finset.sum_le_sum hI).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have e2 : ∑ n ∈ Finset.range q, ((L : ℝ) ^ ((n + 1) * (d - 2)) / 2) *
        crossSumP G n X (psiFull φ ψ) ≤
      3 * d * ∑ n ∈ Finset.range q, bk G X φ ψ (n + 1) +
        (3 * d / 4) * ∑ n ∈ Finset.range q, bk G X φ ψ n +
        6 * ∑ n ∈ Finset.range q, bondE ((lam G n ∪ lam G (n + 1)) ∩ X) φ := by
    refine (Finset.sum_le_sum hC).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
  rw [← hBf]
  rw [hsh] at e2
  have f1 := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 3 * (d : ℝ) / 4)
  have f2 : 0 ≤ (d : ℝ) * ∑ n ∈ Finset.range (q + 1), bk G X φ ψ n :=
    mul_nonneg hd0 (Finset.sum_nonneg fun n _ => bk_nonneg G X φ ψ n)
  linarith [e1, e2, f1, f2, hS1, hS2]

end Total

end Balaban.LargeField
