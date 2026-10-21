/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffPairs
public import Balaban.Inhabited.NewLevelCanonBox

/-!
# The index bijection of the old terms of canonically pinned systems as the hypothesis of the
# two-torus coefficient chain

`canon_hE`: for every label `Y` of the box an equivalence between the old terms whose domains contain
`Y` and `bm '' Y` along which the levels, the label cubes and the canonical pairs correspond
(`domEquiv_of_canon_box`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory Balaban.Polymer.TwoTorusStep

section ClassCoeff

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl

attribute [local irreducible] NewLevelSystem.Dom

/-- **The partial index bijection of the old terms of two canonically pinned systems, as the
hypothesis of the comparison chain**: for every label `Y` of the box, an equivalence between the old
terms of the domains of `Y` and of `bm '' Y` along which the levels, the label cubes and the
canonical pairs correspond. -/
theorem canon_hE
    (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    {C : StepClass d L N₁ m₁ k N ϱ} {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : (SA).JointRep t pp} {C' : StepClass d L N₁' m₁ k N ϱ} {pp' : ℝ} {Jr' : (SB).JointRep t pp'} (NS : NewLevelSystem (SA) C z Jr) (NS' : NewLevelSystem (SB) C' (bc z) Jr')
    {F : CanonCover d L N₁ m₁ k ϱ NS.O.ϱ₁} {F' : CanonCover d L N₁' m₁ k ϱ NS'.O.ϱ₁}
    {y : NS.O.ι → CTorus d L N₁ m₁ (k + 1)} {X : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    {y' : NS'.O.ι → CTorus d L N₁' m₁ (k + 1)} {X' : NS'.O.ι → Set (CTorus d L N₁' m₁ (k + 1))}
    (hB : Set.BijOn (fun τ => (NS.O.jL τ, y τ, X τ)) Set.univ (AdmPairs L N₁ m₁ k d C.m₀ k))
    (hB' : Set.BijOn (fun τ => (NS'.O.jL τ, y' τ, X' τ)) Set.univ (AdmPairs L N₁' m₁ k d C'.m₀ k))
    (hX₁ : ∀ τ, NS.O.X₁f τ = F.X₁fC (NS.O.jL τ) (y τ) (X τ))
    (hX₁' : ∀ τ, NS'.O.X₁f τ = F'.X₁fC (NS'.O.jL τ) (y' τ) (X' τ))
    (hm₀ : NS.O.m₀ = C.m₀) (hm₀' : NS'.O.m₀ = C'.m₀) (hC : C'.m₀ = C.m₀)
    (hcX : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      insert y₀ X₀ ⊆ ↑(F.X₁fC j y₀ X₀))
    (hcX' : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁' m₁ k d C'.m₀ k →
      insert y₀ X₀ ⊆ ↑(F'.X₁fC j y₀ X₀))
    {R R₂ : ℕ} (hR : R ≤ R₂)
    (hcloc : ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
      (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∀ x ∈ F.X₁fC j y₀ X₀, InBox d R₂ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hcov : ∀ j y₀ X₀, (∀ x ∈ insert y₀ X₀, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      F'.X₁fC j (bm y₀) (bm '' X₀) = (F.X₁fC j y₀ X₀).image bm)
    (hGA : (SA).G' = levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hGB : (SB).G' = levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) le_rfl)
    (hn : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * R₂ + 5 * (L * cellSide L NS.O.m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1)) :
    ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
      ∃ e : {τ // NS.Dom Y τ} ≃ {τ' // NS'.Dom (bm '' Y) τ'}, ∀ τ,
        NS'.O.jL (e τ).1 = NS.O.jL τ.1 ∧ NS'.O.X₁f (e τ).1 = (NS.O.X₁f τ.1).image bm ∧
          (y' (e τ).1 = bm (y τ.1) ∧ X' (e τ).1 = bm '' X τ.1) := by
  intro Y hY
  obtain ⟨e, he⟩ := domEquiv_of_canon_box hGA NS hGB NS' y X y' X' hB hB' hX₁ hX₁' hm₀ hm₀' hC hcX hcX' hR hcloc hcov Y hY hn hn'
  exact ⟨e, fun τ => ⟨(he τ).1, (he τ).2.1, (he τ).2.2.1, (he τ).2.2.2⟩⟩

end ClassCoeff

end Balaban.Inhabited
