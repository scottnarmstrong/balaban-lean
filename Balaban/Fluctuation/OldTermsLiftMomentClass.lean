/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftRenormMoment
public import Balaban.Fluctuation.OldTermsLiftAnalytic
public import Balaban.Green.FinalInteractionClass

/-!
# Reference-field analyticity for inherited moments

The class's term analyticity and membership of the reference pair in every
old polymer domain imply analyticity of the full finite-torus energy.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The exact finite-torus moment equality from old class clauses and
reference-field membership in the old domain. -/
theorem liftOldTerms_momentSum_of_clauses {P : Consts}
    {Dom : FieldDom d L (L * N₁) m₁ k N ϱ}
    {Tm : Terms d L (L * N₁) m₁ k N ϱ}
    (hcl : SFTermClauses P Dom Tm)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (i₀ i₁ : Fin N)
    (href : ∀ X, IsPolyDom P.m₀ j X →
      Dom.dom j (Tm.gs j X)
        (constFld (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
          (Pi.single i₀ 1))
        (constFld (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
          (Pi.single i₀ 1))) :
    momentSum P.m₀ (liftOldTerms Tm) j i₀ i₁ =
      momentSum P.m₀ Tm j i₀ i₁ := by
  let cOld : Fld d L (L * N₁) m₁ k N := constFld (Pi.single i₀ 1)
  let cNew : Fld d L N₁ m₁ (k + 1) N := constFld (Pi.single i₀ 1)
  have hU : ∀ r ∈ ({(cOld, cOld)} : Set (Fld d L (L * N₁) m₁ k N ×
      Fld d L (L * N₁) m₁ k N)), ∀ X, IsPolyDom P.m₀ j X →
      Dom.dom j (Tm.gs j X) r.1 r.2 := by
    intro r hr X hX
    have hr' : r = (cOld, cOld) := by simpa using hr
    subst r
    exact href X hX
  have hPair : AnalyticAt ℂ
      (fun r : Fld d L (L * N₁) m₁ k N × Fld d L (L * N₁) m₁ k N =>
        Edens P.m₀ Tm j r.1 r.2) (cOld, cOld) :=
    (Balaban.Green.edens_analyticOnNhd_of_dom (U := {(cOld, cOld)})
      hcl hj1 hjk hU) _ (by simp)
  have hMap : AnalyticAt ℂ
      (fun ψ : Fld d L (L * N₁) m₁ k N => (ψ, cOld)) cOld :=
    analyticAt_id.prod analyticAt_const
  have hAnOld : AnalyticAt ℂ
      (fun ψ : Fld d L (L * N₁) m₁ k N => Edens P.m₀ Tm j ψ cOld) cOld := by
    simpa only [Function.comp_def] using hPair.comp_of_eq hMap rfl
  have hc : lowerNewField cNew = cOld := lowerNewField_constFld _
  have hAnNew : AnalyticAt ℂ
      (fun ψ : Fld d L N₁ m₁ (k + 1) N =>
        Edens P.m₀ (liftOldTerms Tm) j ψ cNew) cNew := by
    have heq : (fun ψ : Fld d L N₁ m₁ (k + 1) N =>
        Edens P.m₀ (liftOldTerms Tm) j ψ cNew) =
        (fun ψ => Edens P.m₀ Tm j (lowerNewField ψ) cOld) := by
      funext ψ
      simpa only [hc] using liftOldTerms_Edens P.m₀ j Tm ψ cNew
    rw [heq]
    have hAnOld' : AnalyticAt ℂ
        (fun ψ : Fld d L (L * N₁) m₁ k N =>
          Edens P.m₀ Tm j ψ cOld) (lowerNewField cNew) := by
      simpa only [hc] using hAnOld
    simpa only [Function.comp_def] using
      hAnOld'.comp (lowerNewField_analyticAt cNew)
  exact liftOldTerms_momentSum P.m₀ j Tm i₀ i₁
    (by simpa only [cNew] using hAnNew)
    (by simpa only [cOld] using hAnOld)

/-- The complete inherited renormalization record follows from the old family class clauses and
membership of each reference pair in its birth domain, at the old sides of the selected new tori
`SelN` (the new tori `idx' n` of the limit are selected). -/
theorem liftOldTermsFam_renormCond_of_clauses {P : Consts}
    {DomFam : ∀ (N₂ : ℕ) [NeZero N₂], FieldDom d L N₂ m₁ k N ϱ}
    {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
    {νk : ℝ} {j : ℕ} {idx idx' φ : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}
    (hidx' : ∀ n, idx' n ≠ 0) (hφ : Filter.Tendsto φ Filter.atTop Filter.atTop)
    (hrel : ∀ n, L * idx' n = idx (φ n)) (SelN : ℕ → Prop) (hSel : ∀ n, SelN (idx' n))
    (hCl : ∀ (N₂ : ℕ) [NeZero N₂], SelN N₂ → SFTermClauses P (DomFam (L * N₂)) (Tm (L * N₂)))
    (hRef : ∀ (N₂ : ℕ) [NeZero N₂], SelN N₂ → ∀ (i₀ : Fin N)
      (X : Set (CTorus d L (L * N₂) m₁ k)),
      IsPolyDom P.m₀ j X →
      (DomFam (L * N₂)).dom j ((Tm (L * N₂)).gs j X)
        (constFld (d := d) (L := L) (N₁ := L * N₂) (m₁ := m₁) (k := k)
          (Pi.single i₀ 1))
        (constFld (d := d) (L := L) (N₁ := L * N₂) (m₁ := m₁) (k := k)
          (Pi.single i₀ 1)))
    (hT : TorusIndep P.m₀ Tm)
    (hR : RenormCondAlong P.m₀ k νk Tm j idx hidx) (hν : 0 < νk)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (νK : ℝ) :
    RenormCondAlong P.m₀ (k + 1) νK (liftOldTermsFam Tm) j idx' hidx' := by
  apply liftOldTermsFam_renormCond hidx' hφ hrel hT hR hν hj1 hjk νK
  intro i₀ i₁ _ n
  have : NeZero (idx' n) := ⟨hidx' n⟩
  exact liftOldTerms_momentSum_of_clauses (hCl (idx' n) (hSel n)) hj1 hjk i₀ i₁
    (hRef (idx' n) (hSel n) i₀)

end Balaban.Fluctuation
