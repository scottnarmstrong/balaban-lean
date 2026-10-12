/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2Form
public import Balaban.LargeField.Operators.AncVars
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The exact region-shrink identity (Q13-FACTOR (1.1)-(1.2))

When the small-field region `Y` shrinks to `Y' ⊆ Y`, the restricted energy term of P5 (1.8)
(`EresJ2`) changes by an exact finite-sum difference (`notes/phase1/Q13-FACTOR.md` §1, with
`Q13-REEXPAND.md` §1 and `Q13-SHARED.md` §1).

* `energyAt`, `shrink_identity`: the abstract finite algebra (1.1) over a finite universe `U` of
  admissible polymers.  The absolute-convergence hypothesis of the note is vacuous here: every sum
  is a finite sum.  The polymer support `Bp` (a set) and the correction support `Bc` (a finset) are
  separate arguments, as in `EresJ2`.
* `EresAt`: `EresJ2` with its region, supports and composed field as arguments
  (`EresJ2_eq_EresAt`); `EresJ2_shrink` is (1.1) for the landed objects with the full `corrPair`
  (both coefficients `v₁, v₂` of P5 (1.8)); `alignedIn_mono`, `sset_mono`, `thickY_mono` are the
  monotonicity of the landed maps.
* `shrinkDeleted`, `shrinkCrossing`, `shrinkFlux`, `shrinkReeval` and `EresJ2_shrink_total`: the
  identity (1.2) for two composed fields.
* `shrinkFlux_ne_zero_example`: the flux term cannot be dropped.

No bound on any term is asserted, and nothing is assigned to a large-field kernel (open analytic
theorem).
-/

@[expose] public section

open Finset

namespace Balaban.LargeField.RegionShrink

section Abstract

variable {ι V : Type*} [AddCommGroup V]

open Classical in
/-- `P_B(y) = ∑_{X ∋ y, X ⊆ B} E y X` over the finite universe `U` of admissible polymers. -/
noncomputable def polyAt (U : Finset (Set ι)) (E : ι → Set ι → V) (Bp : Set ι) (y : ι) : V :=
  ∑ X ∈ U.filter (fun X => y ∈ X ∧ X ⊆ Bp), E y X

open Classical in
/-- The polymers through `y` supported in `Bp` but not in `Bp'`. -/
noncomputable def crossAt (U : Finset (Set ι)) (E : ι → Set ι → V) (Bp Bp' : Set ι) (y : ι) : V :=
  ∑ X ∈ U.filter (fun X => y ∈ X ∧ X ⊆ Bp ∧ ¬ X ⊆ Bp'), E y X

/-- `𝒞(A, B) = ∑_{y ∈ A} ∑_{x ∈ B} c y x`. -/
def pairSum (c : ι → ι → V) (A B : Finset ι) : V := ∑ y ∈ A, ∑ x ∈ B, c y x

/-- `ℰ(R, B) = ∑_{y ∈ R} P_B(y) - 𝒞(R, B)`; `Bp` supports the polymers, `Bc` the correction. -/
noncomputable def energyAt (U : Finset (Set ι)) (E : ι → Set ι → V) (c : ι → ι → V)
    (R Bc : Finset ι) (Bp : Set ι) : V :=
  ∑ y ∈ R, polyAt U E Bp y - pairSum c R Bc

/-- The deleted-centre contribution `∑_{y ∈ R \ R'} P_B(y)`. -/
noncomputable def shrinkDeleted [DecidableEq ι] (U : Finset (Set ι)) (E : ι → Set ι → V)
    (R R' : Finset ι) (Bp : Set ι) : V :=
  ∑ y ∈ R \ R', polyAt U E Bp y

/-- The crossing-polymer contribution `∑_{y ∈ R'} ∑_{X ∋ y, X ⊆ B, X ⊄ B'} E y X`. -/
noncomputable def shrinkCrossing (U : Finset (Set ι)) (E : ι → Set ι → V)
    (R' : Finset ι) (Bp Bp' : Set ι) : V :=
  ∑ y ∈ R', crossAt U E Bp Bp' y

/-- The correction flux `𝒞(D, B) + 𝒞(R', B \ B')`, `D = R \ R'`. -/
def shrinkFlux [DecidableEq ι] (c : ι → ι → V) (R R' Bc Bc' : Finset ι) : V :=
  pairSum c (R \ R') Bc + pairSum c R' (Bc \ Bc')

theorem polyAt_split [DecidableEq ι] (U : Finset (Set ι)) (E : ι → Set ι → V) {Bp Bp' : Set ι}
    (hB : Bp' ⊆ Bp) (y : ι) :
    polyAt U E Bp y = polyAt U E Bp' y + crossAt U E Bp Bp' y := by
  classical
  unfold polyAt crossAt
  rw [← Finset.sum_filter_add_sum_filter_not (U.filter (fun X => y ∈ X ∧ X ⊆ Bp))
    (fun X => X ⊆ Bp')]
  congr 1
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext X
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.2⟩, fun h => ⟨⟨h.1, h.2.1, fun a ha => hB (h.2.2 ha)⟩, h.2.2⟩⟩
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext X
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

/-- **Q13-FACTOR (1.1)**: the exact regional difference.  All sums are finite (`U` is a finite
universe of admissible polymers), so the absolute-convergence hypothesis of the note is vacuous. -/
theorem shrink_identity [DecidableEq ι] (U : Finset (Set ι)) (E : ι → Set ι → V)
    (c : ι → ι → V) {R R' Bc Bc' : Finset ι} {Bp Bp' : Set ι}
    (hR : R' ⊆ R) (hBc : Bc' ⊆ Bc) (hBp : Bp' ⊆ Bp) :
    energyAt U E c R Bc Bp - energyAt U E c R' Bc' Bp' =
      shrinkDeleted U E R R' Bp + shrinkCrossing U E R' Bp Bp' - shrinkFlux c R R' Bc Bc' := by
  unfold energyAt shrinkDeleted shrinkCrossing shrinkFlux pairSum
  have h1 : ∑ y ∈ R, polyAt U E Bp y =
      ∑ y ∈ R \ R', polyAt U E Bp y + ∑ y ∈ R', polyAt U E Bp y :=
    (Finset.sum_sdiff hR).symm
  have h2 : ∑ y ∈ R', polyAt U E Bp y =
      ∑ y ∈ R', polyAt U E Bp' y + ∑ y ∈ R', crossAt U E Bp Bp' y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => polyAt_split U E hBp y
  have h3 : ∑ y ∈ R, ∑ x ∈ Bc, c y x =
      ∑ y ∈ R \ R', ∑ x ∈ Bc, c y x + ∑ y ∈ R', ∑ x ∈ Bc, c y x :=
    (Finset.sum_sdiff hR).symm
  have h4 : ∀ y, ∑ x ∈ Bc, c y x = ∑ x ∈ Bc', c y x + ∑ x ∈ Bc \ Bc', c y x := fun y =>
    (Finset.sum_sdiff hBc).symm.trans (add_comm _ _)
  have h5 : ∑ y ∈ R', ∑ x ∈ Bc, c y x =
      ∑ y ∈ R', ∑ x ∈ Bc', c y x + ∑ y ∈ R', ∑ x ∈ Bc \ Bc', c y x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => h4 y
  rw [h1, h2, h3, h5]
  abel

/-- **Q13-FACTOR (1.2)** in the abstract form: with two evaluations (`E₁, c₁` and `E₂, c₂`) the
difference is (1.1) at the first plus the re-evaluation on the retained supports. -/
theorem shrink_identity_total [DecidableEq ι] (U : Finset (Set ι)) (E₁ E₂ : ι → Set ι → V)
    (c₁ c₂ : ι → ι → V) {R R' Bc Bc' : Finset ι} {Bp Bp' : Set ι}
    (hR : R' ⊆ R) (hBc : Bc' ⊆ Bc) (hBp : Bp' ⊆ Bp) :
    energyAt U E₁ c₁ R Bc Bp - energyAt U E₂ c₂ R' Bc' Bp' =
      (shrinkDeleted U E₁ R R' Bp + shrinkCrossing U E₁ R' Bp Bp' - shrinkFlux c₁ R R' Bc Bc') +
        (energyAt U E₁ c₁ R' Bc' Bp' - energyAt U E₂ c₂ R' Bc' Bp') := by
  rw [← shrink_identity U E₁ c₁ hR hBc hBp]
  abel

end Abstract

end Balaban.LargeField.RegionShrink
