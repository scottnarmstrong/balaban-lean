/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkCluster

/-!
# Families of interactions on the cubes of a region over a parameter

The cluster expansion of the measure of the step on a region (FLUCTUATION Theorem 3.4,
`Fluctuation/MarkCluster`) runs with an interaction `LocInteraction` at fixed external fields.  The
boundary terms are functions of the external fields, and their (D7) clauses compare the interactions
at two values of the fields; these must have the same labels and constants.

* `LocIntFam`: fixed labels and constants of Theorem 3.4 with one mark, and the activities `A(p, u)`
  at every value `p` of a parameter (the external fields);
* `LocIntFam.at`: the interaction at a parameter; `LocIntFam.const`, and `LocIntFam` is inhabited
  (rule 10).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Localization Balaban.Polymer

namespace Balaban.Fluctuation

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}

/-- **A family of interactions on the cubes of a region over a parameter** (the data of Proposition
3.3 on a region as a function of the external fields): fixed labels `Lab` of the cubes of `Ω` and
constants of Theorem 3.4 with one mark, and the activities `A(p, u)` at every parameter `p`. -/
structure LocIntFam (Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*)
    [∀ b, MeasurableSpace (Ωb b)] (Prm : Type*) where
  /-- the labels -/
  Lb : Type
  [fin : Fintype Lb]
  /-- their sites and sizes -/
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω Lb
  εH : ℝ
  κH : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  /-- the activities at the parameter `p` and the interpolation parameter `u` -/
  A : Prm → ℂ → LabelAct Lab Ωb εH κH κ0 Kc
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 ≤ Kc
  hεpos : 0 < εH
  hκ' : 0 ≤ κ'
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * (Kc + 1) ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))

attribute [instance] LocIntFam.fin

/-- **The interaction of a family at a parameter.** -/
def LocIntFam.at {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] {Prm : Type*} (I : LocIntFam Ωb Prm) (p : Prm) :
    LocInteraction Ωb where
  Lb := I.Lb
  Lab := I.Lab
  εH := I.εH
  κH := I.κH
  κ0 := I.κ0
  κ' := I.κ'
  Kc := I.Kc
  A := I.A p
  hκ0 := I.hκ0
  hKc := I.hKc
  hεpos := I.hεpos
  hκ' := I.hκ'
  hκ := I.hκ
  hε := I.hε

/-- The constant family of an interaction. -/
def LocIntFam.const {Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (Prm : Type*) (I : LocInteraction Ωb) : LocIntFam Ωb Prm where
  Lb := I.Lb
  Lab := I.Lab
  εH := I.εH
  κH := I.κH
  κ0 := I.κ0
  κ' := I.κ'
  Kc := I.Kc
  A := fun _ => I.A
  hκ0 := I.hκ0
  hKc := I.hKc
  hεpos := I.hεpos
  hκ' := I.hκ'
  hκ := I.hκ
  hε := I.hε

/-- `LocIntFam` is inhabited (rule 10): the constant family of the empty interaction. -/
instance (Ωb : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*)
    [∀ b, MeasurableSpace (Ωb b)] (Prm : Type*) : Nonempty (LocIntFam Ωb Prm) := by
  obtain ⟨I⟩ := (inferInstance : Nonempty (LocInteraction Ωb))
  exact ⟨LocIntFam.const Prm I⟩

end Balaban.Fluctuation
