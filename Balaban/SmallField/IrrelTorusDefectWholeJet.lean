/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectInverse
public import Balaban.SmallField.Def6v2Renorm
public import Balaban.SmallField.Def6AvgDens

/-!
# Reference jets at every centre and finite small-shape sums

Torus independence gives equality of the complete configuration functions at each centre whose
shape is an infinite polymer and a nonwinding torus polymer. The equalities of the value, first
jet, and every second derivative entry follow without analyticity assumptions.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- The entire centred configuration function agrees with its torus realization at an arbitrary
centre, hence the reference value, every first jet, and the full second derivative matrix agree.
The local `let` names contain no cut-off and make the comparison independent of a chart radius. -/
theorem referenceJets_allCentre_eq_of_nonWind
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N) (νj : ℝ)
    {y : Site d} {X' : Finset (Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    (let fInf : Cfg d N X' → ℂ := fun c =>
       Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf νj X' c);
     let fT : Cfg d N X' → ℂ := EauxC (Tm N₁) j i₀ νj y X';
     fInf (refPt i₀ νj X') = fT (refPt i₀ νj X') ∧
       (∀ p : Idx d N X', fderiv ℂ fInf (refPt i₀ νj X') (Pi.single p 1) =
         fderiv ℂ fT (refPt i₀ νj X') (Pi.single p 1)) ∧
       (∀ p q : Idx d N X', D2 fInf (refPt i₀ νj X') (Pi.single p 1) (Pi.single q 1) =
         D2 fT (refPt i₀ νj X') (Pi.single p 1) (Pi.single q 1))) := by
  have heq : (fun c : Cfg d N X' =>
      Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf νj X' c)) =
      EauxC (Tm N₁) j i₀ νj y X' := by
    funext c
    unfold EauxC
    rw [Einf_eq_torus hF.torusIndep hj1 hjk hy hX _ _ N₁ hnw hpd,
      pullFld_fieldInfOf, pullFld_hInfOf]
  simp only [heq]
  exact ⟨congrFun heq _, fun _ => trivial, fun _ _ => trivial⟩

/-- The reference jets agree for every infinite shape below the explicit side threshold at
any centre contained in the shape. -/
theorem referenceJets_allCentre_eq_of_small
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ : Fin N) (νj : ℝ) {y : Site d} {X' : Finset (Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : 4 * (diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ))
    (h0 : (0 : Site d) ∈ X') :
    (let fInf : Cfg d N X' → ℂ := fun c =>
       Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf νj X' c);
     let fT : Cfg d N X' → ℂ := EauxC (Tm N₁) j i₀ νj y X';
     fInf (refPt i₀ νj X') = fT (refPt i₀ νj X') ∧
       (∀ p : Idx d N X', fderiv ℂ fInf (refPt i₀ νj X') (Pi.single p 1) =
         fderiv ℂ fT (refPt i₀ νj X') (Pi.single p 1)) ∧
       (∀ p q : Idx d N X', D2 fInf (refPt i₀ νj X') (Pi.single p 1) (Pi.single q 1) =
         D2 fT (refPt i₀ νj X') (Pi.single p 1) (Pi.single q 1))) := by
  have hfin := liftPolys_of_infPoly_small hjk hN h0 hX hs
  exact referenceJets_allCentre_eq_of_nonWind hF hj1 hjk i₀ νj hy hX hfin.2.1 hfin.2.2

/-- Quantitative comparison at an arbitrary centre. The centre-coordinate term in the side
threshold is necessary because `Ypoly` uses absolute representatives of the fixed torus. -/
theorem referenceJets_allCentre_eq_of_small_at
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ : Fin N) (νj : ℝ) {y : Site d} {X' : Finset (Site d)} (hy : y ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hs : 4 * ((∑ μ, (((|y μ| : ℤ) : ℝ))) +
        diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    (let fInf : Cfg d N X' → ℂ := fun c =>
       Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf νj X' c);
     let fT : Cfg d N X' → ℂ := EauxC (Tm N₁) j i₀ νj y X';
     fInf (refPt i₀ νj X') = fT (refPt i₀ νj X') ∧
       (∀ p : Idx d N X', fderiv ℂ fInf (refPt i₀ νj X') (Pi.single p 1) =
         fderiv ℂ fT (refPt i₀ νj X') (Pi.single p 1)) ∧
       (∀ p q : Idx d N X', D2 fInf (refPt i₀ νj X') (Pi.single p 1) (Pi.single q 1) =
         D2 fT (refPt i₀ νj X') (Pi.single p 1) (Pi.single q 1))) := by
  obtain ⟨hnw, hpd⟩ := fixedPoly_of_infPoly_small_at hjk hN hy hX hs
  exact referenceJets_allCentre_eq_of_nonWind hF hj1 hjk i₀ νj hy hX hnw hpd

end Balaban.SmallField.Def6v2
