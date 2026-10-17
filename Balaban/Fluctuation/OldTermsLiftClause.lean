/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftBasic

/-!
# Inherited term clauses on the transported old domain

These statements use the old field domain at the exactly corresponding old generating
set. The mass and radius of the old class therefore remain attached to the inherited terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A successor polymer pulls back to an old polymer at the same level. -/
theorem oldPoly_of_newPoly {m₀ j : ℕ}
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : IsPolyDom m₀ j X) :
    IsPolyDom (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
      m₀ j (oldTorusEquiv.symm '' X) := by
  apply (oldTorusEquiv_isPolyDom_iff (N₁ := N₁) (m₁ := m₁) (k := k)).2
  simpa [liftOldPoly, Set.image_image] using hX

/-- The field sum norm is unchanged by relabeling the fine torus. -/
theorem lowerNewField_l1 (g : Fld d L N₁ m₁ (k + 1) N) :
    Balaban.SmallField.Def6.l1 (lowerNewField g) = Balaban.SmallField.Def6.l1 g := by
  unfold Balaban.SmallField.Def6.l1 lowerNewField
  exact Equiv.sum_comp oldTorusEquiv (fun x => vn (g x))

/- A pointwise rotation commutes with pulling a field back. -/
omit [NeZero L] [NeZero N₁] in
theorem lowerNewField_rotField (R : Matrix (Fin N) (Fin N) ℂ)
    (Ψ : Fld d L N₁ m₁ (k + 1) N) :
    lowerNewField (rotField R Ψ) = rotField R (lowerNewField Ψ) := by
  rfl

/-- The inherited energy bound on the transported old field domain. -/
theorem liftOldTerms_boundE_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hDom : Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
      (lowerNewField Ψ) (lowerNewField h)) :
    ‖(liftOldTerms Tm).E j y X Ψ h‖ ≤
      P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hbound := hcl.boundE j hj1 hjk (oldTorusEquiv.symm y)
    (oldTorusEquiv.symm '' X) (oldPoly_of_newPoly hX)
    (by exact ⟨y, hy, rfl⟩) (lowerNewField Ψ) (lowerNewField h) hDom
  rw [liftOldTerms_E]
  have himage : liftOldPoly (oldTorusEquiv.symm '' X) = X := by
    simp [liftOldPoly, Set.image_image]
  have hsize := liftOldPoly_sizeJ (N₁ := N₁) P.m₀ j (oldTorusEquiv.symm '' X)
  rw [himage] at hsize
  rw [hsize]
  exact hbound

/-- The inherited energy rotation law on the transported old field domain. -/
theorem liftOldTerms_rotE_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    {Ψ h : Fld d L N₁ m₁ (k + 1) N}
    (hDom : Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
      (lowerNewField Ψ) (lowerNewField h))
    (hRotDom : Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
      (lowerNewField (rotField R Ψ)) (lowerNewField (rotField R h))) :
    (liftOldTerms Tm).E j y X (rotField R Ψ) (rotField R h) =
      (liftOldTerms Tm).E j y X Ψ h := by
  simp only [liftOldTerms_E, lowerNewField_rotField]
  exact hcl.rotE j hj1 hjk (oldTorusEquiv.symm y)
    (oldTorusEquiv.symm '' X) (oldPoly_of_newPoly hX)
    ⟨y, hy, rfl⟩ R hR (lowerNewField Ψ) (lowerNewField h) hDom
    (by simpa only [lowerNewField_rotField] using hRotDom)

/-- The inherited observable bound on the transported old field domain. -/
theorem liftOldTerms_boundM_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    {Ψ h g : Fld d L N₁ m₁ (k + 1) N}
    (hDom : Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
      (lowerNewField Ψ) (lowerNewField h))
    (hg : Balaban.SmallField.Def6.l1 g < 1) :
    vn ((liftOldTerms Tm).M j x X Ψ h g) <
      P.c₉ * ((L : ℝ) ^ j)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
        Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hbound := hcl.boundM j hj1 hjk (oldTorusEquiv.symm x)
    (oldTorusEquiv.symm '' X) (oldPoly_of_newPoly hX)
    (by exact ⟨x, hx, rfl⟩) (lowerNewField Ψ) (lowerNewField h)
    (lowerNewField g) hDom (by rwa [lowerNewField_l1])
  rw [liftOldTerms_M]
  have himage : liftOldPoly (oldTorusEquiv.symm '' X) = X := by
    simp [liftOldPoly, Set.image_image]
  have hsize := liftOldPoly_sizeJ (N₁ := N₁) P.m₀ j (oldTorusEquiv.symm '' X)
  rw [himage] at hsize
  rw [hsize]
  exact hbound

/-- The inherited observable rotation law on the transported old field domain. -/
theorem liftOldTerms_rotM_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X)
    {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRot R)
    {Ψ h g : Fld d L N₁ m₁ (k + 1) N}
    (hg : Balaban.SmallField.Def6.l1 g < 1)
    (hRg : Balaban.SmallField.Def6.l1 (rotField R g) < 1)
    (hDom : Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
      (lowerNewField Ψ) (lowerNewField h))
    (hRotDom : Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
      (lowerNewField (rotField R Ψ)) (lowerNewField (rotField R h))) :
    (liftOldTerms Tm).M j x X (rotField R Ψ) (rotField R h) (rotField R g) =
      R.mulVec ((liftOldTerms Tm).M j x X Ψ h g) := by
  simp only [liftOldTerms_M, lowerNewField_rotField]
  exact hcl.rotM j hj1 hjk (oldTorusEquiv.symm x)
    (oldTorusEquiv.symm '' X) (oldPoly_of_newPoly hX)
    ⟨x, hx, rfl⟩ R hR (lowerNewField Ψ) (lowerNewField h) (lowerNewField g)
    (by rwa [lowerNewField_l1]) (by rw [← lowerNewField_rotField, lowerNewField_l1]; exact hRg)
    hDom (by simpa only [lowerNewField_rotField] using hRotDom)

end Balaban.Fluctuation
