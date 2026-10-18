/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftCov

/-!
# Paving covariance of inherited generating sets

At an inherited level, the new top region is empty.  Each lower region is
the image of the corresponding old region under the physical torus equivalence.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

omit [NeZero L] [NeZero N₁] in
private theorem liftOldSites_coe (S : Finset (CTorus d L (L * N₁) m₁ k)) :
    ((liftOldSites S : Finset (CTorus d L N₁ m₁ (k + 1))) :
      Set (CTorus d L N₁ m₁ (k + 1))) =
      oldTorusEquiv '' (S : Set (CTorus d L (L * N₁) m₁ k)) := by
  ext x
  simp only [Finset.mem_coe, mem_liftOldSites]
  simp

/-- The regions of an inherited generating set are images of the old regions. -/
theorem liftOldTerms_gsΩ (Tm : Terms d L (L * N₁) m₁ k N ϱ)
    (j i : ℕ) (hi : i ≤ k) (X : Set (CTorus d L (L * N₁) m₁ k)) :
    (((liftOldTerms Tm).gs j (liftOldPoly X)).Ω i :
      Finset (CTorus d L N₁ m₁ (k + 1))) =
      liftOldSites ((Tm.gs j X).Ω i) := by
  change (liftOldGS (Tm.gs j (oldTorusEquiv.symm '' liftOldPoly X))).Ω i = _
  simpa [liftOldPoly, Set.image_image] using
    (liftOldGS_Ω (Tm.gs j X) hi)

/-- The added top region and all higher regions of an inherited set are empty. -/
theorem liftOldTerms_gsΩ_above (Tm : Terms d L (L * N₁) m₁ k N ϱ)
    (j i : ℕ) (hi : ¬ i ≤ k) (X : Set (CTorus d L (L * N₁) m₁ k)) :
    ((liftOldTerms Tm).gs j (liftOldPoly X)).Ω i = ∅ := by
  change (liftOldGS (Tm.gs j (oldTorusEquiv.symm '' liftOldPoly X))).Ω i = ∅
  simp [liftOldGS, hi]

/-- Paving covariance of every inherited generating-set region. -/
theorem liftOldTerms_pavingGS {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L (L * N₁) m₁ k)}
    (hX : IsPolyDom P.m₀ j X)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j)
    (i : ℕ) :
    ((((liftOldTerms Tm).gs j
      ((oldTorusEquiv.permCongrHom r) '' liftOldPoly X)).Ω i :
      Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) =
    (oldTorusEquiv.permCongrHom r) ''
      ((((liftOldTerms Tm).gs j (liftOldPoly X)).Ω i :
        Finset (CTorus d L N₁ m₁ (k + 1))) : Set (CTorus d L N₁ m₁ (k + 1))) := by
  rw [← liftOldPoly_act]
  by_cases hi : i ≤ k
  · rw [liftOldTerms_gsΩ Tm j i hi (r '' X), liftOldTerms_gsΩ Tm j i hi X]
    have hOld := hcl.pavingGS j hj1 hjk X hX r hr i
    have hImage := congrArg
      (Set.image (oldTorusEquiv (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))) hOld
    rw [liftOldSites_coe, liftOldSites_coe]
    exact hImage.trans (by simpa only [liftOldPoly] using (liftOldPoly_act r
      (((Tm.gs j X).Ω i : Finset (CTorus d L (L * N₁) m₁ k)) :
        Set (CTorus d L (L * N₁) m₁ k))))
  · rw [liftOldTerms_gsΩ_above Tm j i hi (r '' X),
      liftOldTerms_gsΩ_above Tm j i hi X]
    simp

end Balaban.Fluctuation
