/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModExtend
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the hypotheses of the region-growth inequality

For every choice of parameters with `L^{m₀} ∣ N₁` and `j ≤ K`, the whole fine torus
`X = univ` is in `𝒟_j`, `Ω₋ = ∅` and `Ω₊ = univ` are unions of cells with `Ω₋ ⊆ Ω₊`, the
component hypothesis `hsplit` of `modAdmissible_extend` holds, and `X ∩ (Ω₊ ∖ Ω₋)` has at least
one cell (`exists_region_grow_instance`).  `dcovMod_univ_le` is the resulting inequality, and
`instance_d2_L2` the instance `d = L = 2`, `N₁ = 1`, `m₀ = m₁ = 0`, `K = 2`, `j = 1`.

The component hypothesis is also satisfied by every pair with `Ω₊ = Ω₋` (`hsplit_of_eq`), since
the components of `X ∩ Ω₋ᶜ` miss `Ω₋`.  It is not automatic for `Ω₊ ⊊ univ` with a non-empty
`Ω₋`: that case needs a component analysis of the complement and is not exercised here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

theorem isPiUnion_univ :
    IsPiUnion m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) := fun z _ =>
  ⟨_, aligned_cbase z, mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z, Set.subset_univ _⟩

omit [NeZero N₁] [NeZero L] in
theorem isPiUnion_empty : IsPiUnion m₀ j (∅ : Set (CTorus d L N₁ m₁ K)) :=
  fun _ hz => hz.elim

/-- The whole fine torus is in `𝒟_j`. -/
theorem isDj_univ : IsDj m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) := by
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine ⟨⟨0, trivial⟩, fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z,
    box_mono _ (Nat.le_mul_of_pos_left _ hL1) (mem_box_cbase ha0 z), Set.subset_univ _⟩, ?_⟩
  have toZero : ∀ x : CTorus d L N₁ m₁ K, Relation.ReflTransGen
      (fun u v => u ∈ (Set.univ : Set (CTorus d L N₁ m₁ K)) ∧ v ∈ Set.univ ∧ Nbr u v) 0 x := by
    intro x
    have := reach_box (0 : CTorus d L N₁ m₁ K) (fun μ => (x μ).val) Set.univ (fun _ _ => trivial)
    have e : (0 : CTorus d L N₁ m₁ K) + natT (fun μ => (x μ).val) = x := by
      funext μ; simp [natT]
    rw [e] at this
    exact Relation.ReflTransGen.mono (fun u v h => ⟨h.2.1, h.2.2, h.1.2⟩) _ _ this
  intro x _ y _
  exact (rtg_symm (fun u v h => ⟨h.2.1, h.1, h.2.2.symm⟩) (toZero x)).trans (toZero y)

/-- The component hypothesis holds when the regions coincide. -/
theorem hsplit_of_eq {X Ω : Set (CTorus d L N₁ m₁ K)} :
    ∀ Q ∈ cellComps m₀ j (X ∩ Ωᶜ), Q ⊆ Ω ∨ Disjoint Q Ω := by
  rintro Q ⟨b, hb, rfl⟩
  right
  rw [Set.disjoint_left]
  intro x hx hxΩ
  simp only [cellComp, Set.mem_iUnion, Finset.mem_coe] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ((mem_cellsIn.1 (mem_cellCompBases.1 ht).1).2 hxt).2 hxΩ

/-- **Non-vacuity**: the hypotheses of `dcovMod_le_add_of_region_grow` are satisfiable with a
newly active cell, for all parameters. -/
theorem exists_region_grow_instance :
    ∃ X Ωm Ωp : Set (CTorus d L N₁ m₁ K), IsDj m₀ j X ∧ Ωm ⊆ Ωp ∧ Ωm ≠ Ωp ∧
      IsPiUnion m₀ j Ωm ∧ IsPiUnion m₀ j Ωp ∧
      (∀ Q ∈ cellComps m₀ j (X ∩ Ωmᶜ), Q ⊆ Ωp ∨ Disjoint Q Ωp) ∧
      1 ≤ (cellsIn m₀ j (X ∩ (Ωp \ Ωm))).card := by
  refine ⟨Set.univ, ∅, Set.univ, isDj_univ, Set.empty_subset _, ?_, isPiUnion_empty,
    isPiUnion_univ, fun _ _ => Or.inl (Set.subset_univ _), ?_⟩
  · exact fun h => (Set.univ_nonempty (α := CTorus d L N₁ m₁ K)).ne_empty h.symm
  · apply Finset.card_pos.2
    exact ⟨0, mem_cellsIn.2 ⟨fun μ => by simp, fun x _ => ⟨trivial, trivial, Set.notMem_empty x⟩⟩⟩

/-- The inequality of `dcovMod_le_add_of_region_grow` for `X = univ`, `Ω₋ = ∅`, `Ω₊ = univ`. -/
theorem dcovMod_univ_le (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) :
    dcovMod m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) Set.univ ≤
      dcovMod m₀ j (∅ : Set (CTorus d L N₁ m₁ K)) Set.univ +
        ((d : ℝ) * L + d + 3) *
          ((cellsIn m₀ j ((Set.univ : Set (CTorus d L N₁ m₁ K)) ∩ (Set.univ \ ∅))).card : ℝ) :=
  dcovMod_le_add_of_region_grow hN hj isDj_univ isPiUnion_empty isPiUnion_univ
    (fun _ _ => Or.inl (Set.subset_univ _))

/-- The instance `d = L = 2`, `N₁ = 1`, `m₀ = m₁ = 0`, `K = 2`, `j = 1` (fine torus
`(ℤ/4)^2`, cells of side `2`). -/
theorem instance_d2_L2 :
    haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
    haveI : NeZero (1 : ℕ) := ⟨by norm_num⟩
    ∃ X Ωm Ωp : Set (CTorus 2 2 1 0 2), IsDj 0 1 X ∧ Ωm ⊆ Ωp ∧ Ωm ≠ Ωp ∧
      IsPiUnion 0 1 Ωm ∧ IsPiUnion 0 1 Ωp ∧
      (∀ Q ∈ cellComps 0 1 (X ∩ Ωmᶜ), Q ⊆ Ωp ∨ Disjoint Q Ωp) ∧
      1 ≤ (cellsIn 0 1 (X ∩ (Ωp \ Ωm))).card :=
  exists_region_grow_instance

end Balaban.Fluctuation
