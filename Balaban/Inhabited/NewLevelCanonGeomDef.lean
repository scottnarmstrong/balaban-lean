/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCanonBox
public import Balaban.Polymer.ComposeFieldTransport
public import Balaban.Polymer.BgFieldTransport

/-!
# The geometry of the canonical covers of two tori

`HGeom S C C' F F' i₀ i₁ R` is the per-pair geometry of the canonical covers of the inherited levels
on two tori that `canon_hprem` consumes: for each admissible pair `(j, y₀, X₀)` whose region `X₁` lies in
the box of radius `R`, the neighbours and the cell of `y₀` lie in the box, and there is a margin `Z`
(containing the polymer and the neighbours, inside `X₁`, with the block margin and closed under the
blocks of the generating sets) on which the generating sets `Gk`, `Gj` of the pair and of its image
correspond, together with the agreement of the irrelevant term at the distinguished cell
(`CellTermsAgree`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Polymer Balaban.SmallField.Def6 Balaban.Polymer.TwoTorusStep
  Balaban.SmallField.Def6v2

section GeomDef

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))

/-- **The agreement of the irrelevant term at the distinguished cell** (the named hypothesis
`hcellcase` of `oldTerm_E_agree`): for the term of level `j` at `y₀` whose polymer `X₀` is the cell
of `y₀` (the case that `irrelTorus_boxAgree` does not cover: there the relevant parts of all polymers
at `y₀`, among them those wrapping around the torus, enter), the irrelevant terms of the classes `C`,
`C'` at `(j, y₀, X₀)` and `(j, bm y₀, bm '' X₀)` agree on fields that agree on `Z` under `bm`. -/
def CellTermsAgree (C : StepClass d L N₁ m₁ k N ϱ) (C' : StepClass d L N₁' m₁ k N ϱ)
    (i₀ i₁ : Fin N) (j : ℕ) (y₀ : CTorus d L N₁ m₁ (k + 1)) (X₀ Z : Set (CTorus d L N₁ m₁ (k + 1))) :
    Prop :=
  X₀ = box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j))
      (L * cellSide L C.m₀ m₁ j) →
    ∀ (r : RawData d L (N₁ * L ^ m₁) (k + 1) N) (r' : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      (∀ z ∈ Z, r.1 z = r'.1 (bm z) ∧ r.2 z = r'.2 (bm z)) →
      irrelTorus C'.m₀ C'.Tm i₀ i₁ j (bm y₀) (bm '' X₀) r'.1 r'.2 =
        irrelTorus C.m₀ C.Tm i₀ i₁ j y₀ X₀ r.1 r.2

/-- The cell case holds vacuously when the polymer is not the cell of `y₀` (non-vacuity of
`CellTermsAgree`). -/
theorem CellTermsAgree.of_ne {C : StepClass d L N₁ m₁ k N ϱ} {C' : StepClass d L N₁' m₁ k N ϱ}
    {i₀ i₁ : Fin N} {j : ℕ} {y₀ : CTorus d L N₁ m₁ (k + 1)} {X₀ Z : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : X₀ ≠ box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j))
      (L * cellSide L C.m₀ m₁ j)) : CellTermsAgree C C' i₀ i₁ j y₀ X₀ Z :=
  fun hc => absurd hc h

/-- **The geometry of the canonical covers of two tori** (see the module doc-string). -/
def HGeom (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    (C' : StepClass d L N₁' m₁ k N ϱ) {ϱ₁ ϱ₁' : ℝ} (F : CanonCover d L N₁ m₁ k ϱ ϱ₁)
    (F' : CanonCover d L N₁' m₁ k ϱ ϱ₁') (i₀ i₁ : Fin N) (R : ℕ) : Prop :=
  ∀ j y₀ X₀, (j, y₀, X₀) ∈ AdmPairs L N₁ m₁ k d C.m₀ k →
    (∀ x ∈ (↑(F.X₁fC j y₀ X₀) : Set (CTorus d L N₁ m₁ (k + 1))),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) →
    (∀ μ : Fin d, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1))
      (y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)))) ∧
    (∀ z ∈ box (cbase (cellSide L C.m₀ m₁ j) y₀ - natT (fun _ => L / 2 * cellSide L C.m₀ m₁ j))
      (L * cellSide L C.m₀ m₁ j), InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) z) ∧
    ∃ Z : Set (CTorus d L N₁ m₁ (k + 1)), X₀ ⊆ Z ∧
      (∀ μ : Fin d, y₀ + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ (k + 1)) ∈ Z) ∧
      Z ⊆ ↑(F.X₁fC j y₀ X₀) ∧ BlockMargin S.G' (F.X₁fC j y₀ X₀) Z ∧
      GSCorr (F.GkC j y₀ X₀) (F'.GkC j (bm y₀) (bm '' X₀)) bm Z ∧
      GSCorr (F.GjC j y₀ X₀) (F'.GjC j (bm y₀) (bm '' X₀)) bm Z ∧
      GSIso (compWeight L S.a₁) S.ν (F.GkC j y₀ X₀) (F'.GkC j (bm y₀) (bm '' X₀)) bm Z ∧
      (∀ z ∈ Z, z ∈ (F.GkC j y₀ X₀).Ω 1 →
        (∀ y ∈ (F.GkC j y₀ X₀).blk ((F.GkC j y₀ X₀).layerIndex z) z, y ∈ Z) ∧
        (∀ y ∈ S.G'.blk (S.G'.layerIndex z) z, y ∈ Z) ∧
        (∀ y ∈ (stepG d L N₁ m₁ k ϱ).blk ((stepG d L N₁ m₁ k ϱ).layerIndex z) z, y ∈ Z)) ∧
      (∀ z ∈ Z, z ∈ (F.GjC j y₀ X₀).Ω 1 →
        (∀ y ∈ (F.GjC j y₀ X₀).blk ((F.GjC j y₀ X₀).layerIndex z) z, y ∈ Z) ∧
        (∀ y ∈ (F.GkC j y₀ X₀).blk ((F.GkC j y₀ X₀).layerIndex z) z, y ∈ Z)) ∧
      CellTermsAgree C C' i₀ i₁ j y₀ X₀ Z

end GeomDef

end Balaban.Inhabited
