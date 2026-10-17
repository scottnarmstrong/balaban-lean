/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftBasic
public import Balaban.Localization.P6ActiveSeed

/-!
# Euclidean actions under the physical torus equivalence

The equivalence conjugates permutations and their actions on sites, polymers, and
fields. These identities are independent of membership in a symmetry subgroup.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]

omit [NeZero L] [NeZero N₁] in
/-- The equivalence commutes with taking the base of a `j`-block. -/
theorem oldTorusEquiv_blockBase (j : ℕ) (x : CTorus d L (L * N₁) m₁ k) :
    oldTorusEquiv (blockBase L j x) = blockBase L j (oldTorusEquiv x) := by
  simpa only [oldTorusEquiv_apply, blockBase] using
    (Balaban.LargeField.castT_cbase
      (oldSide_eq_newSide (L := L) (N₁ := N₁) (m₁ := m₁) (k := k))
      (L ^ j) x)

omit [NeZero L] [NeZero N₁] in
/-- Conjugation of a permutation commutes with transporting a polymer. -/
theorem liftOldPoly_act (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (X : Set (CTorus d L (L * N₁) m₁ k)) :
    liftOldPoly (r '' X) = (oldTorusEquiv.permCongrHom r) '' (liftOldPoly X) := by
  simp only [liftOldPoly, Set.image_image]
  congr 1
  funext x
  change oldTorusEquiv (r x) = oldTorusEquiv.permCongr r (oldTorusEquiv x)
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]

omit [NeZero L] [NeZero N₁] in
/-- Pullback of a field intertwines the conjugate permutation actions. -/
theorem lowerNewField_actField (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (Ψ : Fld d L N₁ m₁ (k + 1) N) :
    lowerNewField (actField (oldTorusEquiv.permCongrHom r) Ψ) =
      actField r (lowerNewField Ψ) := by
  funext x i
  simp [lowerNewField, actField, Equiv.permCongr_def, Equiv.trans_apply]

end Balaban.Fluctuation
