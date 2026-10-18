/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.Def6v2Renorm
public import Balaban.SmallField.IrrelTorusDefectGeom

/-!
# Reference jets on a nonwinding shape

The torus-independence clause identifies the centred analytic term on each nonwinding shape
with its infinite-volume term as a function. Consequently the full first and second jets agree,
including every entry of the second derivative tensor. The anisotropic class bound supplies the
quantitative Cauchy estimates for these common jets. The comparison concerns one shape; a bound
for the sum of winding shapes needs a separate tail estimate.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- The quantitative smallness threshold makes a finite shape a nonwinding shape of `T∞`.
On that shape the two anisotropic terms agree as functions, hence all their reference jets,
including the second tensor, agree exactly. -/
theorem termLInfA_eq_of_liftPolys_small
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ : Fin N) (νj r : ℝ) {X' : Finset (Site d)}
    (hX : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (hs : 4 * (diamA d L P.m₀ m₁ *
        (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ)) :
    termLInfA Tm P.m₀ j i₀ νj r X' = termLA (Tm N₁) j i₀ νj r X' := by
  have hInf := infPoly_of_liftPolys_small hjk hN hX hs
  funext c
  exact termLInfA_eq hF.torusIndep hj1 hjk i₀ νj r hX.1 hInf N₁ hX.2.1 hX.2.2 c

/-- Torus independence identifies the full reference jet, not just the value: the second
derivative equality applies to all coordinate pairs, including the entries of the moment tensor.
The shape must already be an infinite polymer and a nonwinding polymer of this torus. -/
theorem referenceJet_eq_of_nonWind
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N) (νj r : ℝ)
    {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    (termLInfA Tm P.m₀ j i₀ νj r X' (refPt i₀ νj X') =
      termLA (Tm N₁) j i₀ νj r X' (refPt i₀ νj X')) ∧
    (∀ p : Idx d N X',
      fderiv ℂ (termLInfA Tm P.m₀ j i₀ νj r X') (refPt i₀ νj X') (Pi.single p 1) =
        fderiv ℂ (termLA (Tm N₁) j i₀ νj r X') (refPt i₀ νj X') (Pi.single p 1)) ∧
    (∀ p q : Idx d N X',
      D2 (termLInfA Tm P.m₀ j i₀ νj r X') (refPt i₀ νj X')
          (Pi.single p 1) (Pi.single q 1) =
        D2 (termLA (Tm N₁) j i₀ νj r X') (refPt i₀ νj X')
          (Pi.single p 1) (Pi.single q 1)) := by
  have heq : termLInfA Tm P.m₀ j i₀ νj r X' = termLA (Tm N₁) j i₀ νj r X' :=
    funext fun c => termLInfA_eq hF.torusIndep hj1 hjk i₀ νj r h0 hX N₁ hnw hpd c
  rw [heq]
  exact ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩

/-- The same comparison with the Cauchy sizes of all coordinate jets. The second inequality
retains the longitudinal radius `r²` through `anisoWt`; replacing it by `r` would be false. -/
theorem referenceJet_bound_of_nonWind
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {X' : Finset (Site d)} (h0 : (0 : Site d) ∈ X')
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X')
    (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    (‖termLA (Tm N₁) j i₀ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) X'
        (refPt i₀ (nuIdeal L k (Rg.ν k) j) X')‖ ≤
      P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X')) ∧
    (∀ p : Idx d N X',
      ‖fderiv ℂ
        (termLA (Tm N₁) j i₀ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) X')
        (refPt i₀ (nuIdeal L k (Rg.ν k) j) X') (Pi.single p 1)‖ ≤
      (P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X')) /
        anisoWt i₀ (anisoRadius d L N P j) X' p) ∧
    (∀ p q : Idx d N X',
      ‖D2 (termLA (Tm N₁) j i₀ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) X')
        (refPt i₀ (nuIdeal L k (Rg.ν k) j) X') (Pi.single p 1) (Pi.single q 1)‖ ≤
      4 * (P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X')) /
        (anisoWt i₀ (anisoRadius d L N P j) X' p *
          anisoWt i₀ (anisoRadius d L N P j) X' q)) := by
  have hp := hF.premisesTermAnisoInf hn.hd hn.hL hn.hϱ hn.hj1 hn.hjk hn.hsmall hn.hκ hne
  have hXp : X' ∈ (liftInfA P Tm j i₀ (nuIdeal L k (Rg.ν k) j)
      (anisoRadius d L N P j)).polys := ⟨h0, hX⟩
  have hr : 0 < anisoRadius d L N P j := (hF.anisoRadiusOK hn.hsmall i₀).1
  have han : AnalyticOnNhd ℂ
      (termLInfA Tm P.m₀ j i₀ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) X')
      (polyAniso i₀ (nuIdeal L k (Rg.ν k) j) (anisoRadius d L N P j) X') :=
    (hp.analytic X' hXp).mono polyAniso_subset_tubeAniso
  have hM : ∀ c ∈ polyAniso i₀ (nuIdeal L k (Rg.ν k) j)
      (anisoRadius d L N P j) X',
      ‖termLInfA Tm P.m₀ j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j) X' c‖ ≤
        P.E₀ * Real.exp (-P.κ * dInf L m₁ k P.m₀ j X') :=
    fun c hc => hp.bdd_tube X' hXp c (polyAniso_subset_tubeAniso hc)
  have heq : termLInfA Tm P.m₀ j i₀ (nuIdeal L k (Rg.ν k) j)
      (anisoRadius d L N P j) X' =
      termLA (Tm N₁) j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j) X' :=
    funext fun c => termLInfA_eq hF.torusIndep hn.hj1 hn.hjk i₀ _ _ h0 hX N₁ hnw hpd c
  rw [← heq]
  exact ⟨hM _ (refPt_mem_polyAniso hr),
    fun p => aniso_norm_fderiv_basis_le hr han hM p,
    fun p q => by
      have h := aniso_norm_D2_le hr han hM (Pi.single p 1) (Pi.single q 1)
      rw [anisoGauge_single hr, anisoGauge_single hr] at h
      convert h using 1; ring⟩

end Balaban.SmallField.Def6v2
