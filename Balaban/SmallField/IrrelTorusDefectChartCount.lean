/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectChartPartition
public import Balaban.SmallField.IrrelTorusDefectCount

/-!
# Weighted counts restricted to shape tails

The geometric count is uniform in the torus and in the scale. Each finite tail is a subset of
`liftPolys`, and each infinite tail is a finite collection of rooted `InfPoly` shapes.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.Fluctuation Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

open Classical in
/-- The finite class count bounds the weight on any finite subfamily of torus shapes. -/
theorem liftPolys_wt_count_subset {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hN : L ^ P.m₀ ∣ N₁) (hκ : aEnt d L + 3 ≤ P.κ)
    (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, X' ∈ liftPolys (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) :
    ∑ X' ∈ S, wt P.κ X'
      (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) ≤
      (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2) := by
  let F := (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := k) P j).toFinset
  have hsub : S ⊆ F := by
    intro X' hX'
    simpa only [F, Set.Finite.mem_toFinset] using hS X' hX'
  have hmono : (∑ X' ∈ S, wt P.κ X'
      (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X'))) ≤
      ∑ X' ∈ F, wt P.κ X'
        (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun X' _ _ => by
      unfold wt
      have ht : 0 ≤ sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') :=
        treeLenCovOne_nonneg _ _ _
      positivity)
  have hsum : (∑ X' ∈ F, wt P.κ X'
      (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X'))) =
      ∑' X : ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j),
        liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j X := by
    have hfinite : Finite ↥(liftPolys (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (k := k) P j) :=
      (liftPolys_finite P j).to_subtype
    let : Fintype ↥(liftPolys (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (k := k) P j) := @Fintype.ofFinite _ hfinite
    let e : ↥F ≃ ↥(liftPolys (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (k := k) P j) :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun X' => by simp [F])
    calc
      _ = ∑ X' : ↥F, wt P.κ X'.1
          (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X'.1)) :=
        (Finset.sum_coe_sort F _).symm
      _ = ∑ X' : ↥(liftPolys (d := d) (L := L) (N₁ := N₁)
          (m₁ := m₁) (k := k) P j), liftWt P j X' := by
        apply Fintype.sum_equiv e
        intro X'
        rfl
      _ = ∑' X' : ↥(liftPolys (d := d) (L := L) (N₁ := N₁)
          (m₁ := m₁) (k := k) P j), liftWt P j X' := by rw [tsum_fintype]
  exact hmono.trans (hsum.le.trans (liftPolys_count_le hjk hN hκ))

omit [NeZero N₁] in
/-- The infinite class count bounds any finite rooted subfamily of infinite shapes. -/
theorem infPoly_wt_count_subset {P : Consts} {j : ℕ} (hjk : j ≤ k)
    (hκ : aEnt d L + 3 ≤ P.κ) (y : Site d)
    (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    ∑ X' ∈ S, wt P.κ X' (dInf L m₁ k P.m₀ j X') ≤
      (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 *
        (Nat.factorial 8 * Real.exp 1) * K0 d L (P.κ - 2) :=
  sum_wt_dInf_le_at hjk hκ y S hS

end Balaban.SmallField.Def6
