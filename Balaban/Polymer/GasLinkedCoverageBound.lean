/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.GasLinkedCoverage
public import Balaban.Green.FinalLargeActivation
import Balaban.Green.FinalLargeLinkedMayer

/-!
# Large-boundary coverage gas

Coverage labels share a parent footprint and are counted by subsets of its marked set.
Their power-set cost is paid before the linked activity bound; the remaining, possibly
large boundary constant is paid by the heavy charge.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Finset

namespace Balaban.Polymer

section Bound

variable {B T Y Zt : Type*} [Fintype B] [Fintype T] [Fintype Y] [Fintype Zt]
  (parent : Y → T) (activation : Y → Finset B)
  (marks footprint : T → Finset B)
  {zs cr : Zt → Finset B} {β : Y → ℂ} {τ : Zt → ℂ}

omit [Fintype B] in
/-- The coverage gas has the landed large-boundary estimate after paying the
\`2^|marks|\` label count from footprint decay. No smallness of \`B0\` is required. -/
theorem gasLinked_coverage_activity_bound {d : Finset B → ℝ}
    {B0 κ' κ'' κ0 c c1 c2 p h K0 K0'' : ℝ}
    (hsub : ∀ y, activation y ⊆ marks (parent y))
    (hinj : ∀ y y', parent y = parent y' →
      activation y = activation y' → y = y')
    (hmarkfoot : ∀ t, marks t ⊆ footprint t)
    (hfootG1 : ∀ t, ((footprint t).card : ℝ) ≤
      c1 * (1 + d (footprint t)))
    (hκcount : κ0 + c1 * Real.log 2 ≤ κ'' - κ')
    (hbase : ∀ b : B,
      ∑ t ∈ Finset.univ.filter (fun t => b ∈ footprint t),
        Real.exp (-κ0 * d (footprint t)) ≤ K0)
    (hK0 : 0 ≤ K0)
    (hB0 : 0 ≤ B0) (hκ' : 0 ≤ κ') (hκ'' : κ' ≤ κ'') (hc : 0 ≤ c)
    (hc1 : 0 ≤ c1) (hp : 0 ≤ p) (hd : ∀ S, 0 ≤ d S)
    (hz : ∀ z, (zs z).Nonempty) (hcr : ∀ z, cr z ⊆ zs z)
    (hB : ∀ y, ‖β y‖ ≤ B0 * Real.exp (-κ'' * d (footprint (parent y))))
    (hτ : ∀ z, ‖τ z‖ ≤ Real.exp (-p - h * (zs z).card))
    (hzd : ∀ z, d (zs z) ≤ c2 * (zs z).card)
    (hG3 : ∀ C : Finset (Y ⊕ Zt),
      ConnSet (gasCs (fun y => footprint (parent y)) zs) C →
      gasA (fun y => footprint (parent y)) zs cr C →
      d (unionCs (gasCs (fun y => footprint (parent y)) zs) C) ≤
        ∑ t ∈ C, d (gasCs (fun y => footprint (parent y)) zs t) +
          c * ((C.card : ℝ) - 1))
    (hK1 : 1 ≤ K0'')
    (hcount : ∀ (b : B) (v : ℕ),
      ((Finset.univ.filter (fun z => b ∈ zs z ∧ (zs z).card = v)).card : ℝ) ≤
        K0'' ^ v)
    (hh : B0 * Real.exp B0 * Real.exp (κ' * c) *
        (Real.exp (c1 * Real.log 2) * K0) +
      κ' * (c2 + c) + c1 + 3 + Real.log K0'' ≤ h)
    (X : NePoly B) (hG1 : (X.1.card : ℝ) ≤ c1 * (1 + d X.1)) :
    ‖gasLinkedK (fun _ => false) activation (fun y => footprint (parent y))
      zs cr β τ X‖ ≤
        3 * c1 * Real.exp (-p) * Real.exp (-(κ' - 2) * d X.1) := by
  have hact : ∀ y, activation y ⊆ footprint (parent y) :=
    fun y => (hsub y).trans (hmarkfoot (parent y))
  have hmarks : ∀ t, ((marks t).card : ℝ) ≤
      c1 * (1 + d (footprint t)) := by
    intro t
    exact (by exact_mod_cast Finset.card_le_card (hmarkfoot t) : _ ≤
      ((footprint t).card : ℝ)).trans (hfootG1 t)
  have hent : ∀ b : B,
      ∑ y ∈ Finset.univ.filter (fun y => b ∈ footprint (parent y)),
        Real.exp (-(κ'' - κ') * d (footprint (parent y))) ≤
          Real.exp (c1 * Real.log 2) * K0 :=
    gasLinked_coverage_entropy parent activation marks footprint d hsub hinj
      hd hmarks hκcount hbase
  have hK0' : 0 ≤ Real.exp (c1 * Real.log 2) * K0 :=
    mul_nonneg (Real.exp_nonneg _) hK0
  exact gasLinked_activity_bound (allRequired := fun _ => false)
    (activation := activation) (footprint := fun y => footprint (parent y))
    (zs := zs) (cr := cr) (β := β) (τ := τ)
    hact hB0 hκ' hκ'' hc hc1 hp hd hz hcr hB hτ hzd hG3
    hK0' hent hK1 hcount hh X hG1

end Bound

end Balaban.Polymer
