/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonPins
public import Balaban.Polymer.IrrelTorusBox

/-!
# The inherited levels of two canonically pinned systems agree on corresponding fields

* `OldTermsCanonPinsAt`: `OldTermsCanonPins` with the reference indices `i₀`, `i₁` of the irrelevant
  terms named (`oldTermsCanonPins_iff`);
* `oldTerm_E_agree`: the old term `τ` of a system on the torus `N₁` and the old term `τ'` of a system
  on the torus `N₁'` whose label is the image under `boxMap` of that of `τ` agree on fields that agree
  on the margin `Z` under `boxMap` (the box form of the torus independence of the small-field terms,
  `irrelTorus_boxAgree`; at the distinguished cell `□(y)` the agreement is the hypothesis
  `hcellcase`: the irrelevant term there contains the sum of the relevant parts of all polymers at
  `y`, among them the polymers that wrap around the torus, which the clause `TorusIndep` does not
  compare).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Polymer
  Balaban.Polymer.TwoTorusStep


open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Polymer
  Balaban.Polymer.TwoTorusStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The inherited levels are canonically indexed and canonically covered, with the reference
indices `i₀`, `i₁` of the irrelevant terms.**  `OldTermsCanonPins` is the existence of the indices. -/
def OldTermsCanonPinsAt (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) {t : ℝ}
    (O : OldTermSystem S t) (F : CanonCover d L N₁ m₁ k ϱ O.ϱ₁) (i₀ i₁ : Fin N) : Prop :=
  O.m₀ = C.m₀ ∧ ∃ (y : O.ι → CTorus d L N₁ m₁ (k + 1))
    (X : O.ι → Set (CTorus d L N₁ m₁ (k + 1))),
    (∀ τ r, O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2) ∧
    Set.BijOn (fun τ => (O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k) ∧
    ∀ τ, O.X₁f τ = F.X₁fC (O.jL τ) (y τ) (X τ) ∧ O.𝒦X τ = F.𝒦XC (O.jL τ) (y τ) (X τ) ∧
      O.Gk τ = F.GkC (O.jL τ) (y τ) (X τ) ∧ O.Gj τ = F.GjC (O.jL τ) (y τ) (X τ) ∧ O.ρ = F.ρC

theorem oldTermsCanonPins_iff {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
    {t : ℝ} {O : OldTermSystem S t} {F : CanonCover d L N₁ m₁ k ϱ O.ϱ₁} :
    OldTermsCanonPins S C O F ↔ ∃ i₀ i₁, OldTermsCanonPinsAt S C O F i₀ i₁ := by
  constructor
  · rintro ⟨h0, i₀, i₁, y, X, hE, hB, hp⟩
    exact ⟨i₀, i₁, h0, y, X, hE, hB, hp⟩
  · rintro ⟨i₀, i₁, h0, y, X, hE, hB, hp⟩
    exact ⟨h0, i₀, i₁, y, X, hE, hB, hp⟩


section Agree

variable {N₁' : ℕ} [NeZero N₁']

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))

/-- **The localized old term `τ` of a system and the old term `τ'` of a system on the second torus
agree on fields that agree on the margin `Z`** (P4 (H.4), P1 (3.112)-(3.113)), when the labels
`(j, y, X)` and `(j, bm y, bm '' X)` of the two terms correspond: the torus irrelevant terms agree
away from the distinguished cell `□(y)` (`irrelTorus_boxAgree`), and at the distinguished cell by the
hypothesis `hcellcase`. -/
theorem oldTerm_E_agree
    {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ} {t : ℝ}
    (O : OldTermSystem S t)
    {S' : StepSetting d L N₁' m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ} {t' : ℝ}
    (O' : OldTermSystem S' t')
    {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ (k + 1) N ϱ} (hCT : C.Tm = Tm N₁)
    (hCT' : C'.Tm = Tm N₁') (hm₀ : C'.m₀ = C.m₀) (hT : TorusIndep C.m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₁').E j y X Ψ h = (Tm N₁').E j y X Ψ' h')
    (hβ : S'.β = S.β) {i₀ i₁ : Fin N} {y : O.ι → CTorus d L N₁ m₁ (k + 1)}
    {X : O.ι → Set (CTorus d L N₁ m₁ (k + 1))} {y' : O'.ι → CTorus d L N₁' m₁ (k + 1)}
    {X' : O'.ι → Set (CTorus d L N₁' m₁ (k + 1))}
    (hE : ∀ τ r, O.Eτ τ r = irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2)
    (hE' : ∀ τ r, O'.Eτ τ r = irrelTorus C'.m₀ C'.Tm i₀ i₁ (O'.jL τ) (y' τ) (X' τ) r.1 r.2)
    (τ : O.ι) (τ' : O'.ι) (hy' : y' τ' = bm (y τ)) (hX' : X' τ' = bm '' X τ)
    (hj : O'.jL τ' = O.jL τ) (hj1 : 1 ≤ O.jL τ) (hjk : O.jL τ ≤ k + 1)
    (hN₁ : L ^ C.m₀ ∣ N₁) (hN₂ : L ^ C.m₀ ∣ N₁') (hM8 : 8 ≤ L ^ (C.m₀ + m₁)) {R : ℕ}
    (hmar₁ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (O.jL τ) <
      (N₁ * L ^ m₁) * L ^ (k + 1))
    (hmar₂ : 8 * R + 3 * L ^ (k + 1) + L * cellSide L C.m₀ m₁ (O.jL τ) <
      (N₁' * L ^ m₁) * L ^ (k + 1))
    (hy : Aligned (L ^ O.jL τ) (y τ)) (hyX : y τ ∈ X τ) (hX : IsPolyDom C.m₀ (O.jL τ) (X τ))
    (hXR : ∀ x ∈ X τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hstep : ∀ μ : Fin d, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y τ + (L ^ O.jL τ) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1))))
    (hcell : ∀ z ∈ box (cbase (cellSide L C.m₀ m₁ (O.jL τ)) (y τ) -
      natT (fun _ => L / 2 * cellSide L C.m₀ m₁ (O.jL τ))) (L * cellSide L C.m₀ m₁ (O.jL τ)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z)
    {Z : Set (CTorus d L N₁ m₁ (k + 1))} (hZX : X τ ⊆ Z)
    (hZs : ∀ μ : Fin d, y τ + (L ^ O.jL τ) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈ Z)
    (hcellcase : X τ = box (cbase (cellSide L C.m₀ m₁ (O.jL τ)) (y τ) -
        natT (fun _ => L / 2 * cellSide L C.m₀ m₁ (O.jL τ))) (L * cellSide L C.m₀ m₁ (O.jL τ)) →
      ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
        (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) →
        irrelTorus C'.m₀ C'.Tm i₀ i₁ (O'.jL τ') (y' τ') (X' τ') r'.1 r'.2 =
          irrelTorus C.m₀ C.Tm i₀ i₁ (O.jL τ) (y τ) (X τ) r.1 r.2) :
    ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) →
      (S'.β : ℂ)⁻¹ * O'.Eτ τ' r' = (S.β : ℂ)⁻¹ * O.Eτ τ r := by
  intro r r' hr
  rw [hE τ r, hE' τ' r', hβ]
  congr 1
  by_cases hc : X τ = box (cbase (cellSide L C.m₀ m₁ (O.jL τ)) (y τ) -
      natT (fun _ => L / 2 * cellSide L C.m₀ m₁ (O.jL τ))) (L * cellSide L C.m₀ m₁ (O.jL τ))
  · exact hcellcase hc r r' hr
  · rw [hy', hX', hj, hm₀, hCT', hCT]
    refine irrelTorus_boxAgree (Tm := Tm) (m₀ := C.m₀) (j := O.jL τ) hj1 hjk hT hlocB hN₁ hN₂ hM8
      (R := R) hmar₁ hmar₂ hy hyX hX hXR hstep hcell hc i₀ i₁ r.1 r.2 r'.1 r'.2 ?_ ?_ ?_
    · intro x hx; exact ((hr x (hZX hx)).1).symm
    · intro μ
      have := (hr _ (hZs μ)).1
      exact this.symm
    · intro x hx; exact ((hr x (hZX hx)).2).symm
  
end Agree


end Balaban.Inhabited
