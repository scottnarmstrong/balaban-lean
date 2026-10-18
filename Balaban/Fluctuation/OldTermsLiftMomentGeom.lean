/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftPaving

/-!
# Geometry of the inherited second-moment sum

The summation lattice, squared distance, reference fields and block directions
have identical physical meanings in the two scale descriptions.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

omit [NeZero L] [NeZero N₁] in
/-- Alignment at any inherited scale is unchanged by the torus equivalence. -/
theorem oldTorusEquiv_aligned_iff (j : ℕ)
    (x : CTorus d L (L * N₁) m₁ k) :
    Aligned (L ^ j) (oldTorusEquiv x) ↔ Aligned (L ^ j) x := by
  simp only [Aligned, oldTorusEquiv_val]

private theorem castT_valMinAbs {n n' : ℕ} (h : n = n')
    (x : Torus d n) (μ : Fin d) :
    ZMod.valMinAbs ((castT h x) μ) = ZMod.valMinAbs (x μ) := by
  cases h
  rfl

private theorem castT_zero {n n' : ℕ} (h : n = n') :
    castT h (0 : Torus d n) = (0 : Torus d n') := by
  cases h
  rfl

omit [NeZero L] [NeZero N₁] in
/-- The physical torus equivalence fixes the origin. -/
theorem oldTorusEquiv_zero :
    oldTorusEquiv (0 : CTorus d L (L * N₁) m₁ k) =
      (0 : CTorus d L N₁ m₁ (k + 1)) := by
  rw [oldTorusEquiv_apply]
  exact castT_zero _

omit [NeZero L] [NeZero N₁] in
/-- The weight in the second-moment condition is the same physical weight. -/
theorem oldTorusEquiv_liftSq (j : ℕ)
    (x : CTorus d L (L * N₁) m₁ k) :
    liftSq L j (oldTorusEquiv x) = liftSq L j x := by
  unfold liftSq
  apply Finset.sum_congr rfl
  intro μ _
  rw [oldTorusEquiv_apply, castT_valMinAbs]

omit [NeZero L] [NeZero N₁] in
/-- Constant fields pull back without change. -/
theorem lowerNewField_constFld (v : Fin N → ℂ) :
    lowerNewField (constFld (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k + 1) v) =
      constFld (d := d) (L := L) (N₁ := L * N₁)
        (m₁ := m₁) (k := k) v := by
  rfl

omit [NeZero L] [NeZero N₁] in
/-- A block perturbation pulls back to the corresponding old block perturbation. -/
theorem lowerNewField_blockDir (j : ℕ)
    (x : CTorus d L (L * N₁) m₁ k) (i : Fin N) :
    lowerNewField (blockDir L j (oldTorusEquiv x) i) =
      blockDir L j x i := by
  funext z i'
  have hb : blockBase L j (oldTorusEquiv z) = oldTorusEquiv x ↔
      blockBase L j z = x := by
    rw [← oldTorusEquiv_blockBase]
    simp
  change (if blockBase L j (oldTorusEquiv z) = oldTorusEquiv x ∧ i' = i
      then (1 : ℂ) else 0) =
    (if blockBase L j z = x ∧ i' = i then (1 : ℂ) else 0)
  simp only [hb]

/-- The full inherited finite-torus energy is unchanged after field pullback. -/
theorem liftOldTerms_Edens (m₀ j : ℕ)
    (Tm : Terms d L (L * N₁) m₁ k N ϱ)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N) :
    Edens m₀ (liftOldTerms Tm) j Ψ h =
      Edens m₀ Tm j (lowerNewField Ψ) (lowerNewField h) := by
  classical
  have hsum :
      (∑ y ∈ (Finset.univ : Finset (CTorus d L (L * N₁) m₁ k)).filter
          (Aligned (L ^ j)),
        Eloc m₀ Tm j y (lowerNewField Ψ) (lowerNewField h)) =
      (∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
          (Aligned (L ^ j)),
        Eloc m₀ (liftOldTerms Tm) j y Ψ h) := by
    refine Finset.sum_equiv oldTorusEquiv (fun y => ?_) fun y _ => ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (oldTorusEquiv_aligned_iff j y).symm
    · exact (liftOldTerms_Eloc m₀ j Tm y Ψ h).symm
  exact hsum.symm

end Balaban.Fluctuation
