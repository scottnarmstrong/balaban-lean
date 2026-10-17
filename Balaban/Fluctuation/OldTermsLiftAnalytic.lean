/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftClause

/-!
# Analyticity of inherited terms on the transported old domain

Reindexing a finite torus field is analytic because each output coordinate is a
continuous linear projection. Composition transports the old analytic term clauses.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- Pullback of a field by the site equivalence is analytic. -/
theorem lowerNewField_analyticAt (Ψ : Fld d L N₁ m₁ (k + 1) N) :
    AnalyticAt ℂ lowerNewField Ψ := by
  apply analyticAt_pi_iff.mpr
  intro x
  exact (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : CTorus d L N₁ m₁ (k + 1) => Fin N → ℂ)
    (oldTorusEquiv x)).analyticAt Ψ

/-- Analyticity of the inherited energy on the exact pullback of the old domain. -/
theorem liftOldTerms_analyticE_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {y : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) (hy : y ∈ X) :
    AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (liftOldTerms Tm).E j y X p.1 p.2)
      {p | Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
        (lowerNewField p.1) (lowerNewField p.2)} := by
  have hOld := hcl.analyticE j hj1 hjk (oldTorusEquiv.symm y)
    (oldTorusEquiv.symm '' X) (oldPoly_of_newPoly hX) ⟨y, hy, rfl⟩
  have hMap : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        (lowerNewField p.1, lowerNewField p.2))
      {p | Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
        (lowerNewField p.1) (lowerNewField p.2)} := by
    intro p _
    exact ((lowerNewField_analyticAt p.1).comp analyticAt_fst).prod
      ((lowerNewField_analyticAt p.2).comp analyticAt_snd)
  have hComp := hOld.comp hMap (by intro p hp; exact hp)
  simpa only [Function.comp_def, liftOldTerms_E] using hComp

/-- Analyticity of the inherited observable on the exact pullback of the old domain. -/
theorem liftOldTerms_analyticM_on_old_domain {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {x : CTorus d L N₁ m₁ (k + 1)}
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX : IsPolyDom P.m₀ j X) (hx : x ∈ X) :
    AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N =>
        (liftOldTerms Tm).M j x X p.1 p.2.1 p.2.2)
      {p | Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
        (lowerNewField p.1) (lowerNewField p.2.1) ∧
        Balaban.SmallField.Def6.l1 p.2.2 < 1} := by
  have hOld := hcl.analyticM j hj1 hjk (oldTorusEquiv.symm x)
    (oldTorusEquiv.symm '' X) (oldPoly_of_newPoly hX) ⟨x, hx, rfl⟩
  have hMap : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N =>
        (lowerNewField p.1, lowerNewField p.2.1, lowerNewField p.2.2))
      {p | Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
        (lowerNewField p.1) (lowerNewField p.2.1) ∧
        Balaban.SmallField.Def6.l1 p.2.2 < 1} := by
    intro p _
    have hfst : AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N ×
        Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => q.1) p :=
      analyticAt_fst
    have hpair : AnalyticAt ℂ (fun q : Fld d L N₁ m₁ (k + 1) N ×
        Fld d L N₁ m₁ (k + 1) N => (lowerNewField q.1, lowerNewField q.2)) p.2 := by
      exact ((lowerNewField_analyticAt p.2.1).comp analyticAt_fst).prod
        ((lowerNewField_analyticAt p.2.2).comp analyticAt_snd)
    exact ((lowerNewField_analyticAt p.1).comp hfst).prod
      (hpair.comp analyticAt_snd)
  have hMaps : Set.MapsTo
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N ×
          Fld d L N₁ m₁ (k + 1) N =>
        (lowerNewField p.1, lowerNewField p.2.1, lowerNewField p.2.2))
      {p | Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X))
        (lowerNewField p.1) (lowerNewField p.2.1) ∧
        Balaban.SmallField.Def6.l1 p.2.2 < 1}
      {p | Dom.dom j (Tm.gs j (oldTorusEquiv.symm '' X)) p.1 p.2.1 ∧
        Balaban.SmallField.Def6.l1 p.2.2 < 1} := by
    intro p hp
    exact ⟨hp.1, by simpa only [lowerNewField_l1] using hp.2⟩
  have hComp := hOld.comp hMap hMaps
  simpa only [Function.comp_def, liftOldTerms_M] using hComp

end Balaban.Fluctuation
