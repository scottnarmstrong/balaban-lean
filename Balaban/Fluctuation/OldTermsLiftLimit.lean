/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftInf

/-!
# Infinite-volume energy of inherited terms

On each inherited level, old torus independence identifies the new torus-sequence
term with the old one after multiplying its side by `L`. This gives equality of
the eventual values and then of the localized infinite-volume energy.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
  {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}

/-- The stabilizing sequences agree eventually at each inherited level. -/
theorem liftOldTermsFam_Eseq_eventually_eq (hT : TorusIndep m₀ Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : Fin d → ℤ) (X' : Finset (Fin d → ℤ)) (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X')
    (ψ h : InfFld d N) :
    ∀ᶠ n in atTop,
      Eseq m₀ (liftOldTermsFam Tm) j y X' ψ h n = Eseq m₀ Tm j y X' ψ h n := by
  have hnew := (oldInfPoly_iff_newInfPoly (L := L) (m₁ := m₁) hjk X').1 hX
  filter_upwards [hX, hnew] with n hOld hNew
  have hno : NonWind L (L * torusSeq L m₀ n) m₁ k j X' :=
    (oldNonWind_iff_newNonWind hjk X').2 hNew.1
  have hpo : IsPolyDom (L := L) (N₁ := L * torusSeq L m₀ n) (m₁ := m₁) (k := k)
      m₀ j (Ypoly (L := L) (N₁ := L * torusSeq L m₀ n) (m₁ := m₁) (k := k) j X') := by
    rw [← oldTorusEquiv_symm_image_Ypoly (L := L) (N₁ := torusSeq L m₀ n)
      (m₁ := m₁) hjk X']
    exact oldPoly_of_newPoly hNew.2
  have heq := hT.E_eq j hj1 hjk y X' hy ψ h
    (L * torusSeq L m₀ n) (torusSeq L m₀ n) hno hOld.1 hpo hOld.2
  unfold Eseq
  rw [liftOldTermsFam_E_on_inf hjk Tm y X' ψ h]
  exact heq

/-- The eventual energy term is identical for the old and lifted families. -/
theorem liftOldTermsFam_Einf_eq (hT : TorusIndep m₀ Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : Fin d → ℤ) (X' : Finset (Fin d → ℤ)) (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X')
    (ψ h : InfFld d N) :
    Einf m₀ (liftOldTermsFam Tm) j y X' ψ h = Einf m₀ Tm j y X' ψ h := by
  have hseq := liftOldTermsFam_Eseq_eventually_eq hT hj1 hjk y X' hy hX ψ h
  have hold := Einf_eventually_eq hT hj1 hjk hy hX ψ h
  unfold Einf
  apply stabVal_eq
  filter_upwards [hseq, hold] with n heq hevent
  exact heq.trans hevent.symm

/-- The infinite-volume local energy agrees at each inherited level. -/
theorem liftOldTermsFam_ElocInf_eq (hT : TorusIndep m₀ Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : Fin d → ℤ) (ψ h : InfFld d N) :
    ElocInf m₀ (liftOldTermsFam Tm) j y ψ h = ElocInf m₀ Tm j y ψ h := by
  unfold ElocInf
  apply tsum_congr
  intro X'
  by_cases hX : InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X'
  · have hX' := (oldInfPoly_iff_newInfPoly (L := L) (m₁ := m₁) hjk X').1 hX
    by_cases hy : y ∈ X'
    · simp only [hX, hX', hy, and_self, ↓reduceIte]
      exact liftOldTermsFam_Einf_eq hT hj1 hjk y X' hy hX ψ h
    · simp [hy]
  · have hX' : ¬ InfPoly (L := L) (m₁ := m₁) (k := k + 1) m₀ j X' :=
      fun hn => hX ((oldInfPoly_iff_newInfPoly (L := L) (m₁ := m₁) hjk X').2 hn)
    simp [hX, hX']

end Balaban.Fluctuation
