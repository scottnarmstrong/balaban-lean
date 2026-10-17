/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedBound

/-!
# Linked gas with mapped cores

The landed GasCore interface maps charged supports and heavy supports through a core map.
This extension also maps the activation set, while retaining a separate charged footprint.
Its estimate is a direct instance of the linked bound.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Core

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  (core : Finset B → Finset B)
  {allRequired : Yt → Bool} {activation footprint : Yt → Finset B}
  {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}

/-- The GasCore size and counting hypotheses bound a linked gas after mapping activation,
footprints, and heavy supports to cores. The trigger and footprint remain distinct. -/
theorem gasLinked_activity_bound_core {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h : ℝ}
    (hact : ∀ y, core (activation y) ⊆ core (footprint y))
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y)
    (hz : ∀ z, (core (zs z)).Nonempty)
    (hcr : ∀ z, cr z ⊆ core (zs z))
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (core (footprint y))))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (core (zs z)).card))
    (hzd : ∀ z, d (core (zs z)) ≤ c2 * (core (zs z)).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs (fun y => core (footprint y)) (fun z => core (zs z))) C →
      gasA (fun y => core (footprint y)) (fun z => core (zs z)) cr C →
      d (unionCs (gasCs (fun y => core (footprint y)) (fun z => core (zs z))) C) ≤
        ∑ t ∈ C, d (gasCs (fun y => core (footprint y)) (fun z => core (zs z)) t) +
          c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ core (footprint y)),
      Real.exp (-(κ'' - κ') * d (core (footprint y))) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z =>
        b ∈ core (zs z) ∧ (core (zs z)).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' +
      κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasLinkedK allRequired (fun y => core (activation y))
      (fun y => core (footprint y)) (fun z => core (zs z)) cr β τ X‖ ≤
        3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  gasLinked_activity_bound hact hB0 hκ' hκ'' hc hc1 hp hd hz hcr hB hτ hzd
    hG3 hK0' hent hK1 hcount hh X hG1

end Core

end Balaban.Polymer
