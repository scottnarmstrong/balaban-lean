/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.IrrelBoxTransfer
public import Balaban.Polymer.IrrelTorusOnBox
public import Balaban.SmallField.IrrelTorusDefectExpand
public import Balaban.Fluctuation.LocalClassLabels

/-!
# The torus irrelevant term on two tori

`irrelTorus_boxAgree`: the irrelevant part `ℰ^{(j)}_{irrel}(y, X; Ψ, h)` of the label `(j, y, X)` on the
torus `N₁` (`irrelTorus`) and the one of the image label `(j, boxMap y, boxMap '' X)` on the torus
`N₂` agree, when `X` is a polymer of `𝒟_j` in the centred box, away from the distinguished cell
`□(y)`, and the fields agree under `boxMap` on `X` and on the stencil `y + L^j e_μ`.  It is the
instance `sm = ⊤` of `irrelTorusOn_boxAgree` (`IrrelTorusOnBox.lean`), which transports every
ingredient: the term itself (`E_boxAgree`, the clause `TorusIndep`), its first and second
derivatives at the constant field (`fderiv_E_boxAgree`, `D2_E_boxAgree`), the sums over the
aligned sites of `X` (`sum_blk_boxMap`), the directions `δ_{(block x)} e_i` (`blockDir_boxMap`) and
the integer positions of the blocks (`unlift_sub_of_box`).

For `X = □(y)` the term contains the sum over *all* polymers of `𝒟_j` at `y` of the relevant
parts, which on a finite torus includes the polymers that wrap around it; that sum is not controlled
by the clause `TorusIndep` and is excluded here (`image_eq_cellBox_iff` identifies the case on the two
tori).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep


open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.RootFSpine Balaban.Multiscale


section Main

variable {d L N₁ N₂ m₁ K N : ℕ} [NeZero L] [NeZero N₁] [NeZero N₂] {ϱ : ℝ}

set_option hygiene false in
local notation "n₁" => (N₁ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "n₂" => (N₂ * L ^ m₁) * L ^ K
set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₂ * L ^ m₁) * L ^ K)

open Classical in
/-- **The torus irrelevant term on two tori** (P1 (3.112)-(3.113), P4 (H.4)): away from the
distinguished cell `□(y)`, `ℰ_irrel^{(j)}(y, X; Ψ, h)` agrees with the term of the image polymer on the
second torus when the fields agree under `boxMap` on `X` and on the stencil `y + L^j e_μ`. -/
theorem irrelTorus_boxAgree {Tm : ∀ (M : ℕ) [NeZero M], Terms d L M m₁ K N ϱ} {m₀ j : ℕ}
    (hj1 : 1 ≤ j) (hjK : j ≤ K) (hT : TorusIndep m₀ Tm)
    (hlocB : ∀ j y X Ψ Ψ' h h', (∀ x ∈ X, Ψ x = Ψ' x ∧ h x = h' x) →
      (Tm N₂).E j y X Ψ h = (Tm N₂).E j y X Ψ' h')
    (hN₁ : L ^ m₀ ∣ N₁) (hN₂ : L ^ m₀ ∣ N₂) (hM8 : 8 ≤ L ^ (m₀ + m₁)) {R : ℕ}
    (hmar₁ : 8 * R + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₁)
    (hmar₂ : 8 * R + 3 * L ^ K + L * cellSide L m₀ m₁ j < n₂)
    {y : CTorus d L N₁ m₁ K} {X : Set (CTorus d L N₁ m₁ K)} (hy : Aligned (L ^ j) y) (hyX : y ∈ X)
    (hX : IsPolyDom m₀ j X) (hXR : ∀ x ∈ X, InBox d R n₁ x)
    (hstep : ∀ μ : Fin d, InBox d R n₁ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (hcell : ∀ z ∈ box (cbase (cellSide L m₀ m₁ j) y -
      natT (fun _ => L / 2 * cellSide L m₀ m₁ j)) (L * cellSide L m₀ m₁ j), InBox d R n₁ z)
    (hne : X ≠ box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j))
    (i₀ i₁ : Fin N) (Ψ h : Fld d L N₁ m₁ K N) (Ψ' h' : Fld d L N₂ m₁ K N)
    (hΨ : ∀ x ∈ X, Ψ' (bm x) = Ψ x)
    (hΨst : ∀ μ : Fin d, Ψ' (bm (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K))) =
      Ψ (y + (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ K)))
    (hh : ∀ x ∈ X, h' (bm x) = h x) :
    irrelTorus m₀ (Tm N₂) i₀ i₁ j (bm y) (bm '' X) Ψ' h' = irrelTorus m₀ (Tm N₁) i₀ i₁ j y X Ψ h := by
  rw [irrelTorus_eq_irrelTorusOn, irrelTorus_eq_irrelTorusOn]
  exact irrelTorusOn_boxAgree _ _ hj1 hjK hT hlocB hN₁ hN₂ hM8 hmar₁ hmar₂ hy hyX hX hXR hstep hcell
    hne Iff.rfl i₀ i₁ Ψ h Ψ' h' hΨ hΨst hh

end Main

end Balaban.Polymer.TwoTorusStep
