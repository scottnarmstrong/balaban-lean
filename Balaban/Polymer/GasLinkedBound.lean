/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedEq

/-!
# Activity estimate for a linked gas

An activated linked family is a landed admissible family when activation is contained in the
charged footprint, so the size hypothesis may be stated for landed families. The estimate is the
instance of `actGasK_activity_bound` (`GasBound.lean`) for the linked activation, with no loss in
the numerical constants.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Bound

variable {B Yt Zt : Type*} [Fintype B] [Fintype Yt] [Fintype Zt]
  {allRequired : Yt → Bool} {activation footprint : Yt → Finset B}
  {zs cr : Zt → Finset B} {β : Yt → ℂ} {τ : Zt → ℂ}

omit [Fintype B] [Fintype Yt] [Fintype Zt] in
/-- A linked family is landed-admissible when every activation set lies in its footprint. -/
theorem gasLinkedA_imp_gasA (hact : ∀ y, activation y ⊆ footprint y)
    (D : Finset (Yt ⊕ Zt))
    (h : gasLinkedA allRequired activation zs cr D) :
    gasA footprint zs cr D := by
  refine ⟨h.1, ?_⟩
  intro y hy
  have hmeet := gasLinkedActive_footprint_meets hact y D.toRight (h.2 y hy)
  rw [Finset.disjoint_biUnion_right] at hmeet
  push Not at hmeet
  exact hmeet

/-- The connected linked activity has the same bound as the landed gas when the decay and
geometry are measured on charged footprints. The geometric subadditivity premise is stated
for the landed family so that its existing absolute family majorant applies directly. -/
theorem gasLinked_activity_bound {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h : ℝ}
    (hact : ∀ y, activation y ⊆ footprint y)
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (footprint y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs footprint zs) C → gasA footprint zs cr C →
      d (unionCs (gasCs footprint zs) C) ≤
        ∑ t ∈ C, d (gasCs footprint zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint y),
      Real.exp (-(κ'' - κ') * d (footprint y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' +
      κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasLinkedK allRequired activation footprint zs cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) :=
  actGasK_activity_bound (act := fun y Γ => gasLinkedActive allRequired activation cr Γ y)
    hB0 hκ' hκ'' hc hc1 hp hd hz (gasLinkedActive_meets hact hcr) hB hzd
    (fun C hconn hA => hG3 C hconn (gasLinkedA_imp_gasA hact C hA)) hK0'
    (fun Γ _ b => sum_filter_act_le (act := fun y Γ => gasLinkedActive allRequired activation cr Γ y)
      (fun _ => (Real.exp_pos _).le) hent Γ b) hK1
    (sum_filter_le_of_count hτ hcount) hh X hG1

/-- The landed activity estimate is the intersection-mode specialization of the linked
estimate. Its numeric hypotheses and conclusion are unchanged. -/
theorem gas_activity_bound_of_gasLinked {d : Finset B → ℝ}
    {B0 κ' κ'' c c1 c2 p h : ℝ}
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ Y, 0 ≤ d Y)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (footprint y)))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Yt ⊕ Zt),
      ConnSet (gasCs footprint zs) C → gasA footprint zs cr C →
      d (unionCs (gasCs footprint zs) C) ≤
        ∑ t ∈ C, d (gasCs footprint zs t) + c * ((C.card : ℝ) - 1))
    {K0' K0'' : ℝ} (hK0' : 0 ≤ K0')
    (hent : ∀ b : B, ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint y),
      Real.exp (-(κ'' - κ') * d (footprint y)) ≤ K0')
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤ K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) * K0' +
      κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasK footprint zs cr β τ X‖ ≤
      3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  simpa only [gasLinkedK_intersection_eq] using
    (gasLinked_activity_bound (allRequired := fun _ => false)
      (activation := footprint) (footprint := footprint) (zs := zs) (cr := cr)
      (β := β) (τ := τ) (fun _ => Finset.Subset.rfl) hB0 hκ' hκ'' hc
      hc1 hp hd hz hcr hB hτ hzd hG3 hK0' hent hK1 hcount hh X hG1)

end Bound

end Balaban.Polymer
