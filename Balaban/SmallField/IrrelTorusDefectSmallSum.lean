/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectWholeJet
public import Balaban.SmallField.IrrelTorusDefectTail

/-!
# Finite reindexing and reference-jet sums

The nonwinding lift is injective, so a finite collection of small shapes can be summed either
over their integer coordinates or over their torus polymers. The three jet identities below
apply to every finite collection satisfying the explicit side threshold.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- Reindex any finite collection of nonwinding shapes by its torus polymers. -/
theorem sum_image_nonWind {j : ℕ} (hjk : j ≤ k) (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, NonWind L N₁ m₁ k j X')
    (f : Set (CTorus d L N₁ m₁ k) → ℂ) :
    ∑ Y ∈ S.image (fun X' => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X'), f Y =
      ∑ X' ∈ S, f (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  rw [Finset.sum_image]
  intro X hX X' hX' heq
  exact ypoly_injOn_nonWind hjk (hS X hX) (hS X' hX') heq

omit [NeZero L] [NeZero N₁] in
/-- A shape through the block of a torus centre contributes to `polysAt` there. -/
theorem mem_polysAt_of_shape {m₀ j : ℕ} {y : CTorus d L N₁ m₁ k}
    {X' : Finset (Site d)}
    (hy : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈ X')
    (hpd : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' ∈ polysAt m₀ j y :=
  ⟨hpd, hy⟩

open Classical in
/-- Reindex the complete finite torus sum at any centre by canonical nonwinding integer shapes.
This identity applies directly to each coefficient of the expanded filed term. -/
theorem finsum_polysAt_reindex {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    (y : CTorus d L N₁ m₁ k) (f : Set (CTorus d L N₁ m₁ k) → ℂ) :
    ∑ᶠ Z ∈ polysAt m₀ j y, f Z =
      ∑ᶠ X' ∈ {X' : Finset (Site d) |
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈ X' ∧
        NonWind L N₁ m₁ k j X' ∧
        IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')},
        f (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') := by
  rw [polysAt_eq_image hjk hN y]
  rw [finsum_mem_image (g := fun X' =>
    Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')]
  intro A hA B hB h
  exact ypoly_injOn_nonWind hjk hA.2.1 hB.2.1 h

end Balaban.SmallField.Def6

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- The value and every selected first and second entry have equal sums on the common small
shapes. The selectors may choose a different coordinate in each configuration space. -/
theorem referenceJet_smallSums_eq
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ : Fin N) (νj : ℝ) (y : Site d) (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, y ∈ X' ∧
      InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X' ∧
      4 * ((∑ μ, (((|y μ| : ℤ) : ℝ))) +
        diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') +
        ((L * L ^ (P.m₀ + m₁) : ℕ) : ℝ) + 1) <
        ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ))
    (p q : (X' : Finset (Site d)) → Idx d N X') :
    (let fInf : (X' : Finset (Site d)) → Cfg d N X' → ℂ := fun X' c =>
       Einf P.m₀ Tm j y X' (fieldInfOf L j i₀ X' c) (hInfOf νj X' c);
     let fT : (X' : Finset (Site d)) → Cfg d N X' → ℂ := fun X' =>
       EauxC (Tm N₁) j i₀ νj y X';
     (∑ X' ∈ S, fInf X' (refPt i₀ νj X')) =
       (∑ X' ∈ S, fT X' (refPt i₀ νj X')) ∧
     (∑ X' ∈ S, fderiv ℂ (fInf X') (refPt i₀ νj X') (Pi.single (p X') 1)) =
       (∑ X' ∈ S, fderiv ℂ (fT X') (refPt i₀ νj X') (Pi.single (p X') 1)) ∧
     (∑ X' ∈ S, D2 (fInf X') (refPt i₀ νj X') (Pi.single (p X') 1)
        (Pi.single (q X') 1)) =
       (∑ X' ∈ S, D2 (fT X') (refPt i₀ νj X') (Pi.single (p X') 1)
        (Pi.single (q X') 1))) := by
  dsimp only
  refine ⟨Finset.sum_congr rfl (fun X' hX' => ?_),
    Finset.sum_congr rfl (fun X' hX' => ?_),
    Finset.sum_congr rfl (fun X' hX' => ?_)⟩
  · obtain ⟨hy, hInf, hs⟩ := hS X' hX'
    exact (referenceJets_allCentre_eq_of_small_at hF hj1 hjk hN i₀ νj hy hInf hs).1
  · obtain ⟨hy, hInf, hs⟩ := hS X' hX'
    exact (referenceJets_allCentre_eq_of_small_at hF hj1 hjk hN i₀ νj hy hInf hs).2.1 (p X')
  · obtain ⟨hy, hInf, hs⟩ := hS X' hX'
    exact (referenceJets_allCentre_eq_of_small_at hF hj1 hjk hN i₀ νj hy hInf hs).2.2
      (p X') (q X')

end Balaban.SmallField.Def6v2
