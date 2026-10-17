/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftClause

/-!
# Infinite-lattice data under the physical torus identification

The old and successor descriptions have the same block modulus at every inherited
level. Their non-winding tests and pullbacks of integer-lattice fields agree there.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

/- The coarse torus has the same side in the two descriptions at an inherited level. -/
omit [NeZero L] [NeZero N₁] in
theorem oldBlockSide_eq_newBlockSide {j : ℕ} (hjk : j ≤ k) :
    ((L * N₁) * L ^ m₁) * L ^ (k - j) =
      (N₁ * L ^ m₁) * L ^ (k + 1 - j) := by
  have hsub : k + 1 - j = (k - j) + 1 := by omega
  rw [hsub, pow_succ]
  ring

/- The non-winding test is literally the same at inherited levels. -/
omit [NeZero L] [NeZero N₁] in
theorem oldNonWind_iff_newNonWind {j : ℕ} (hjk : j ≤ k)
    (X' : Finset (Fin d → ℤ)) :
    NonWind L (L * N₁) m₁ k j X' ↔ NonWind L N₁ m₁ (k + 1) j X' := by
  unfold NonWind
  rw [← oldBlockSide_eq_newBlockSide (N₁ := N₁) (m₁ := m₁) hjk]

/- The centred integer block coordinate is unchanged by the torus equivalence. -/
omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_unlift {j : ℕ} (hjk : j ≤ k)
    (x : CTorus d L (L * N₁) m₁ k) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j (oldTorusEquiv x) =
      unlift (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j x := by
  funext μ
  simp only [unlift, jBlock, blockMap_apply, blockCoord]
  rw [← oldBlockSide_eq_newBlockSide (N₁ := N₁) (m₁ := m₁) hjk]
  rw [oldTorusEquiv_val]

/- The integer fine-site representative is unchanged at inherited levels. -/
omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_fineLift {j : ℕ} (hjk : j ≤ k)
    (x : CTorus d L (L * N₁) m₁ k) :
    fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j (oldTorusEquiv x) =
      fineLift (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j x := by
  funext μ
  simp only [fineLift, oldTorusEquiv_unlift hjk x, oldTorusEquiv_val]

/- Pullback of an infinite-lattice field commutes with the old-to-new relabeling. -/
omit [NeZero L] [NeZero N₁] in
theorem lowerNewField_pullFld {j : ℕ} (hjk : j ≤ k) (ψ : InfFld d N) :
    lowerNewField
        (pullFld (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j ψ) =
      pullFld (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j ψ := by
  funext x i
  exact congrArg (fun z => ψ z i) (oldTorusEquiv_fineLift hjk x)

/- The whole fine-site lift of an integer-block polymer commutes with relabeling. -/
omit [NeZero L] [NeZero N₁] in
theorem liftOldPoly_Ypoly {j : ℕ} (hjk : j ≤ k)
    (X' : Finset (Fin d → ℤ)) :
    liftOldPoly
        (Ypoly (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j X') =
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j X' := by
  ext x
  rw [mem_liftOldPoly]
  change unlift (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j
      (oldTorusEquiv.symm x) ∈ X' ↔
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j x ∈ X'
  rw [← oldTorusEquiv_unlift hjk (oldTorusEquiv.symm x)]
  simp

/- The representative of an integer-lattice block is transported pointwise. -/
omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_blockPt (j : ℕ) (y : Fin d → ℤ) :
    oldTorusEquiv
        (blockPt (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j y) =
      blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j y := by
  rw [oldTorusEquiv_apply]
  exact castT_intTorus (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
    (fun μ => y μ * ((L ^ j : ℕ) : ℤ))

/- The inverse image of a lifted integer-block polymer is its old realization. -/
omit [NeZero L] [NeZero N₁] in
theorem oldTorusEquiv_symm_image_Ypoly {j : ℕ} (hjk : j ≤ k)
    (X' : Finset (Fin d → ℤ)) :
    oldTorusEquiv.symm ''
        Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j X' =
      Ypoly (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j X' := by
  have h := congrArg (Set.image oldTorusEquiv.symm)
    (liftOldPoly_Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) hjk X')
  simpa [liftOldPoly, Set.image_image] using h.symm

/-- Every inherited infinite-lattice term equals the old term on the corresponding torus. -/
theorem liftOldTermsFam_E_on_inf {ϱ : ℝ} {j : ℕ} (hjk : j ≤ k)
    (Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ)
    (y : Fin d → ℤ) (X' : Finset (Fin d → ℤ)) (ψ h : InfFld d N) :
    (liftOldTermsFam Tm N₁).E j
        (blockPt (N₁ := N₁) (m₁ := m₁) (k := k + 1) j y)
        (Ypoly (N₁ := N₁) (m₁ := m₁) (k := k + 1) j X')
        (pullFld (N₁ := N₁) (m₁ := m₁) (k := k + 1) j ψ)
        (pullFld (N₁ := N₁) (m₁ := m₁) (k := k + 1) j h) =
      (Tm (L * N₁)).E j
        (blockPt (N₁ := L * N₁) (m₁ := m₁) (k := k) j y)
        (Ypoly (N₁ := L * N₁) (m₁ := m₁) (k := k) j X')
        (pullFld (N₁ := L * N₁) (m₁ := m₁) (k := k) j ψ)
        (pullFld (N₁ := L * N₁) (m₁ := m₁) (k := k) j h) := by
  have hpoly := oldTorusEquiv_symm_image_Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) hjk X'
  have hpt : oldTorusEquiv.symm
      (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) j y) =
      blockPt (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k) j y := by
    exact oldTorusEquiv.symm_apply_eq.mpr
      (oldTorusEquiv_blockPt (L := L) (N₁ := N₁) (m₁ := m₁) j y).symm
  rw [liftOldTermsFam_apply, liftOldTerms_E, hpt, hpoly,
    lowerNewField_pullFld hjk, lowerNewField_pullFld hjk]

/-- Torus independence passes to every inherited level of the lifted family. -/
theorem liftOldTermsFam_E_eq_of_torusIndep {ϱ : ℝ} {m₀ : ℕ}
    {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
    (hT : TorusIndep m₀ Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : Fin d → ℤ) (X' : Finset (Fin d → ℤ)) (hy : y ∈ X')
    (ψ h : InfFld d N) (N₂ N₃ : ℕ) [NeZero N₂] [NeZero N₃]
    (hnw₂ : NonWind L N₂ m₁ (k + 1) j X')
    (hnw₃ : NonWind L N₃ m₁ (k + 1) j X')
    (hp₂ : IsPolyDom (L := L) (N₁ := N₂) (m₁ := m₁) (k := k + 1)
      m₀ j (Ypoly (L := L) (N₁ := N₂) (m₁ := m₁) (k := k + 1) j X'))
    (hp₃ : IsPolyDom (L := L) (N₁ := N₃) (m₁ := m₁) (k := k + 1)
      m₀ j (Ypoly (L := L) (N₁ := N₃) (m₁ := m₁) (k := k + 1) j X')) :
    (liftOldTermsFam Tm N₂).E j (blockPt j y) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) =
      (liftOldTermsFam Tm N₃).E j (blockPt j y) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) := by
  have hnwo₂ : NonWind L (L * N₂) m₁ k j X' :=
    (oldNonWind_iff_newNonWind hjk X').2 hnw₂
  have hnwo₃ : NonWind L (L * N₃) m₁ k j X' :=
    (oldNonWind_iff_newNonWind hjk X').2 hnw₃
  have hpo₂ : IsPolyDom (L := L) (N₁ := L * N₂) (m₁ := m₁) (k := k)
      m₀ j (Ypoly (L := L) (N₁ := L * N₂) (m₁ := m₁) (k := k) j X') := by
    rw [← oldTorusEquiv_symm_image_Ypoly (N₁ := N₂) (m₁ := m₁) hjk X']
    exact oldPoly_of_newPoly hp₂
  have hpo₃ : IsPolyDom (L := L) (N₁ := L * N₃) (m₁ := m₁) (k := k)
      m₀ j (Ypoly (L := L) (N₁ := L * N₃) (m₁ := m₁) (k := k) j X') := by
    rw [← oldTorusEquiv_symm_image_Ypoly (N₁ := N₃) (m₁ := m₁) hjk X']
    exact oldPoly_of_newPoly hp₃
  calc
    (liftOldTermsFam Tm N₂).E j (blockPt j y) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) =
      (Tm (L * N₂)).E j (blockPt j y) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) :=
      liftOldTermsFam_E_on_inf hjk Tm y X' ψ h
    _ = (Tm (L * N₃)).E j (blockPt j y) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) :=
      hT.E_eq j hj1 hjk y X' hy ψ h (L * N₂) (L * N₃)
        hnwo₂ hnwo₃ hpo₂ hpo₃
    _ = (liftOldTermsFam Tm N₃).E j (blockPt j y) (Ypoly j X')
        (pullFld j ψ) (pullFld j h) :=
      (liftOldTermsFam_E_on_inf hjk Tm y X' ψ h).symm

end Balaban.Fluctuation
