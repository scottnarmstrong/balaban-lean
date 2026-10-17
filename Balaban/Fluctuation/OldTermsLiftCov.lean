/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftSym

/-!
# Euclidean covariance of inherited terms

The statements use the exact pullback of the old field domain. They therefore
apply to both current-mass and birth-mass instances of the class domain.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- Covariance of an inherited energy term under a conjugated old paving symmetry. -/
theorem liftOldTerms_eucE_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L (L * N₁) m₁ k}
    {X : Set (CTorus d L (L * N₁) m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N)
    (hdom : Dom.dom j (Tm.gs j X) (lowerNewField Ψ) (lowerNewField h))
    (hdom' : Dom.dom j (Tm.gs j (r '' X))
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) Ψ))
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) h))) :
    (liftOldTerms Tm).E j
      (blockBase L j ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv y)))
      ((oldTorusEquiv.permCongrHom r) '' liftOldPoly X)
      (actField (oldTorusEquiv.permCongrHom r) Ψ)
      (actField (oldTorusEquiv.permCongrHom r) h) =
    (liftOldTerms Tm).E j (oldTorusEquiv y) (liftOldPoly X) Ψ h := by
  have hact : (oldTorusEquiv.permCongrHom r) (oldTorusEquiv y) =
      oldTorusEquiv (r y) := by
    change oldTorusEquiv.permCongr r (oldTorusEquiv y) = oldTorusEquiv (r y)
    simp
  rw [hact, ← oldTorusEquiv_blockBase, ← liftOldPoly_act]
  rw [liftOldTerms_E, liftOldTerms_E]
  rw [lowerNewField_actField r Ψ, lowerNewField_actField r h]
  simpa [liftOldPoly, Set.image_image] using
    (hcl.eucE j hj1 hjk y X hX hy r hr
      (lowerNewField Ψ) (lowerNewField h) hdom
      (by simpa only [lowerNewField_actField] using hdom'))

/-- Covariance of an inherited observable under a conjugated old paving symmetry. -/
theorem liftOldTerms_eucM_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : CTorus d L (L * N₁) m₁ k}
    {X : Set (CTorus d L (L * N₁) m₁ k)}
    (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ pavingSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L P.m₀ j)
    (Ψ h g : Fld d L N₁ m₁ (k + 1) N)
    (hdom : Dom.dom j (Tm.gs j X) (lowerNewField Ψ) (lowerNewField h))
    (hdom' : Dom.dom j (Tm.gs j (r '' X))
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) Ψ))
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) h))) :
    (liftOldTerms Tm).M j
      ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv x))
      ((oldTorusEquiv.permCongrHom r) '' liftOldPoly X)
      (actField (oldTorusEquiv.permCongrHom r) Ψ)
      (actField (oldTorusEquiv.permCongrHom r) h)
      (actField (oldTorusEquiv.permCongrHom r) g) =
    (liftOldTerms Tm).M j (oldTorusEquiv x) (liftOldPoly X) Ψ h g := by
  have hact : (oldTorusEquiv.permCongrHom r) (oldTorusEquiv x) =
      oldTorusEquiv (r x) := by
    change oldTorusEquiv.permCongr r (oldTorusEquiv x) = oldTorusEquiv (r x)
    simp
  rw [hact, ← liftOldPoly_act]
  rw [liftOldTerms_M, liftOldTerms_M]
  rw [lowerNewField_actField r Ψ, lowerNewField_actField r h,
    lowerNewField_actField r g]
  simpa [liftOldPoly, Set.image_image] using
    (hcl.eucM j hj1 hjk x X hX hx r hr
      (lowerNewField Ψ) (lowerNewField h) (lowerNewField g) hdom
      (by simpa only [lowerNewField_actField] using hdom'))

/-- Full lattice covariance of the inherited local energy sum. -/
theorem liftOldTerms_eucEloc_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : CTorus d L (L * N₁) m₁ k)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ fullJSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L j)
    (Ψ h : Fld d L N₁ m₁ (k + 1) N)
    (hdom : Dom.dom j (levelGS (ϱ := ϱ) (N₁ := L * N₁) (m₁ := m₁) j hjk)
      (lowerNewField Ψ) (lowerNewField h))
    (hdom' : Dom.dom j (levelGS (ϱ := ϱ) (N₁ := L * N₁) (m₁ := m₁) j hjk)
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) Ψ))
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) h))) :
    Eloc P.m₀ (liftOldTerms Tm) j
      (blockBase L j ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv y)))
      (actField (oldTorusEquiv.permCongrHom r) Ψ)
      (actField (oldTorusEquiv.permCongrHom r) h) =
    Eloc P.m₀ (liftOldTerms Tm) j (oldTorusEquiv y) Ψ h := by
  have hact : (oldTorusEquiv.permCongrHom r) (oldTorusEquiv y) =
      oldTorusEquiv (r y) := by
    change oldTorusEquiv.permCongr r (oldTorusEquiv y) = oldTorusEquiv (r y)
    simp
  rw [hact, ← oldTorusEquiv_blockBase]
  rw [liftOldTerms_Eloc, liftOldTerms_Eloc]
  simpa only [lowerNewField_actField] using
    (hcl.eucEloc j hj1 hjk y r hr (lowerNewField Ψ) (lowerNewField h) hdom
      (by simpa only [lowerNewField_actField] using hdom'))

/-- Full lattice covariance of the inherited local observable sum. -/
theorem liftOldTerms_eucMloc_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : CTorus d L (L * N₁) m₁ k)
    (r : Equiv.Perm (CTorus d L (L * N₁) m₁ k))
    (hr : r ∈ fullJSymGroup (N₁ := L * N₁) (m₁ := m₁) (k := k) (d := d) L j)
    (Ψ h g : Fld d L N₁ m₁ (k + 1) N)
    (hdom : Dom.dom j (levelGS (ϱ := ϱ) (N₁ := L * N₁) (m₁ := m₁) j hjk)
      (lowerNewField Ψ) (lowerNewField h))
    (hdom' : Dom.dom j (levelGS (ϱ := ϱ) (N₁ := L * N₁) (m₁ := m₁) j hjk)
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) Ψ))
      (lowerNewField (actField (oldTorusEquiv.permCongrHom r) h))) :
    Mloc P.m₀ (liftOldTerms Tm) j
      ((oldTorusEquiv.permCongrHom r) (oldTorusEquiv x))
      (actField (oldTorusEquiv.permCongrHom r) Ψ)
      (actField (oldTorusEquiv.permCongrHom r) h)
      (actField (oldTorusEquiv.permCongrHom r) g) =
    Mloc P.m₀ (liftOldTerms Tm) j (oldTorusEquiv x) Ψ h g := by
  have hact : (oldTorusEquiv.permCongrHom r) (oldTorusEquiv x) =
      oldTorusEquiv (r x) := by
    change oldTorusEquiv.permCongr r (oldTorusEquiv x) = oldTorusEquiv (r x)
    simp
  rw [hact]
  rw [liftOldTerms_Mloc, liftOldTerms_Mloc]
  simpa only [lowerNewField_actField] using
    (hcl.eucMloc j hj1 hjk x r hr (lowerNewField Ψ) (lowerNewField h)
      (lowerNewField g) hdom
      (by simpa only [lowerNewField_actField] using hdom'))

end Balaban.Fluctuation
