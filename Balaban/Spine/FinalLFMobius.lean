/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Algebra.Module.BigOperators

/-!
# Möbius inversion on the subsets of a finite set (A6-4, the decorated couplings)

A boundary term `ℬ(X, Δ)` decorated by the set `Δ` of records near `X` becomes a sum of couplings
activated by the records they require: with `μf(T) = ∑_{T' ⊆ T} (-1)^{|T ∖ T'|} f(T')`
(`powMobius`), `f(S) = ∑_{T ⊆ S} μf(T)` (`sum_powMobius`), and `‖μf(T)‖ ≤ ∑_{T' ⊆ T} ‖f(T')‖`
(`norm_powMobius_le`).
-/

@[expose] public section

open Finset

namespace Balaban.RootFSpine

variable {α M : Type*} [DecidableEq α]

section Group

variable [AddCommGroup M]

/-- **The Möbius transform on the subsets**: `μf(T) = ∑_{T' ⊆ T} (-1)^{|T ∖ T'|} f(T')`. -/
def powMobius (f : Finset α → M) (T : Finset α) : M :=
  ∑ T' ∈ T.powerset, ((-1 : ℤ) ^ (T \ T').card) • f T'

/-- The alternating sum over the sets between `T'` and `S` vanishes unless `T' = S`. -/
theorem sum_neg_one_pow_card_sdiff {T' S : Finset α} (h : T' ⊆ S) :
    ∑ T ∈ S.powerset.filter (fun T => T' ⊆ T), (-1 : ℤ) ^ (T \ T').card =
      if T' = S then 1 else 0 := by
  have e : ∑ T ∈ S.powerset.filter (fun T => T' ⊆ T), (-1 : ℤ) ^ (T \ T').card =
      ∑ U ∈ (S \ T').powerset, (-1 : ℤ) ^ U.card := by
    refine Finset.sum_nbij' (fun T => T \ T') (fun U => U ∪ T') ?_ ?_ ?_ ?_ ?_
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      exact Finset.sdiff_subset_sdiff hT.1 le_rfl
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
      exact ⟨Finset.union_subset (hU.trans Finset.sdiff_subset) h, Finset.subset_union_right⟩
    · intro T hT
      simp only [Finset.mem_filter] at hT
      exact Finset.sdiff_union_of_subset hT.2
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      rw [Finset.union_sdiff_right]
      exact Finset.sdiff_eq_self_of_disjoint
        (Finset.disjoint_of_subset_left hU Finset.sdiff_disjoint)
    · intro T _
      rfl
  rw [e, Finset.sum_powerset_neg_one_pow_card]
  have hiff : S \ T' = ∅ ↔ T' = S :=
    ⟨fun h' => Finset.Subset.antisymm h (Finset.sdiff_eq_empty_iff_subset.1 h'),
      fun h' => by subst h'; exact Finset.sdiff_self _⟩
  by_cases hS : T' = S
  · rw [ite_eq_left (hiff.2 hS), ite_eq_left hS]
  · rw [ite_eq_right (fun h' => hS (hiff.1 h')), ite_eq_right hS]

/-- **Möbius inversion on the subsets**: `∑_{T ⊆ S} μf(T) = f(S)`. -/
theorem sum_powMobius (f : Finset α → M) (S : Finset α) :
    ∑ T ∈ S.powerset, powMobius f T = f S := by
  unfold powMobius
  rw [Finset.sum_comm' (t' := S.powerset) (s' := fun T' => S.powerset.filter (fun T => T' ⊆ T))]
  · have h : ∀ T' ∈ S.powerset, ∑ T ∈ S.powerset.filter (fun T => T' ⊆ T),
        ((-1 : ℤ) ^ (T \ T').card) • f T' = (if T' = S then f S else 0) := by
      intro T' hT'
      rw [← Finset.sum_smul, sum_neg_one_pow_card_sdiff (Finset.mem_powerset.1 hT')]
      by_cases h : T' = S
      · subst h; simp
      · simp [h]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' S.powerset S (fun _ => f S)]
    simp
  · intro T T'
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, h2.trans h1⟩
    · rintro ⟨⟨h1, h2⟩, -⟩
      exact ⟨h1, h2⟩

end Group

/-- The Möbius transform is bounded by the sum of the norms. -/
theorem norm_powMobius_le [SeminormedAddCommGroup M] (f : Finset α → M) (T : Finset α) :
    ‖powMobius f T‖ ≤ ∑ T' ∈ T.powerset, ‖f T'‖ := by
  unfold powMobius
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun T' _ => ?_)
  refine (norm_zsmul_le _ _).trans ?_
  have h1 : ‖((-1 : ℤ) ^ (T \ T').card)‖ = 1 := by
    rw [Int.norm_eq_abs]
    simp
  rw [h1, one_mul]

end Balaban.RootFSpine
