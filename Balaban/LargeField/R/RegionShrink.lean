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


section Landed

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField.Def7 Balaban.LargeField.Def7v2

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N))

/-- `y ∈ Y' ⊆ Y` gives `sset Y' ⊆ sset Y`. -/
theorem sset_mono {A A' : Set (Torus S.d (n k))} (h : A' ⊆ A) : C.sset A' ⊆ C.sset A :=
  fun _ hx => h hx

/-- Monotonicity of the aligned sites: `Y' ⊆ Y` gives `alignedIn j Y' ⊆ alignedIn j Y`. -/
theorem alignedIn_mono (j : ℕ) {A A' : Set (Torus S.d (n k))} (h : A' ⊆ A) :
    C.alignedIn j A' ⊆ C.alignedIn j A := by
  classical
  intro y hy
  simp only [SFCtx.alignedIn, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  exact ⟨hy.1, sset_mono C h hy.2⟩

/-- Monotonicity of the thickening `Y ↦ Y^≈`. -/
theorem thickY_mono {A A' : Set (Torus S.d (n k))} (h : A' ⊆ A) : thickY R A' ⊆ thickY R A :=
  thick_mono' _ h

open Classical in
/-- `EresJ2` with its region `Rr`, correction support `Bc`, polymer support `Bp` and composed
field `ψ` as arguments (P5 (1.8)). -/
noncomputable def EresAt (j : ℕ) (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N) : ℂ :=
  (∑ y ∈ Rr,
      ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ Bp},
        (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))) -
    corrSum (fun y x => vc.v1 j (unlift j (x - y))) (fun y x => vc.v2 j (unlift j (x - y)))
      (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ (hC hv)

/-- `EresJ2` is `EresAt` at the regions of `Y` and the field `psiJ`. -/
theorem EresJ2_eq_EresAt (Y : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (j : ℕ) :
    EresJ2 C vc Y ψk hv j =
      EresAt C vc hv j (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.sset (thickY R Y))
        (C.psiJ Y ψk hv j) := rfl

/-- The finite universe of admissible polymers. -/
noncomputable def polyUniv (j : ℕ) : Finset (Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :=
  (Set.toFinite {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | IsPolyDom C.m₀ j X}).toFinset

/-- The pair function of P5 (1.8): the full `corrPair` with both coefficients. -/
noncomputable def corrFn (j : ℕ) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    Localization.CTorus S.d S.L C.N₁ m₁ k → Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ :=
  fun y x => corrPair (vc.v1 j (unlift j (x - y))) (vc.v2 j (unlift j (x - y)))
    (nuIdeal S.L k (C.sf.ν k) j) ψ (hC hv) y x

/-- The polymer term at the field `ψ`. -/
noncomputable def polyTerm (j : ℕ) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    Localization.CTorus S.d S.L C.N₁ m₁ k → Set (Localization.CTorus S.d S.L C.N₁ m₁ k) → ℂ :=
  fun y X => (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))

/-- `EresAt` is the abstract `energyAt` over the finite universe of admissible polymers. -/
theorem EresAt_eq_energyAt (j : ℕ) (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j Rr Bc Bp ψ =
      energyAt (polyUniv C j) (polyTerm C hv j ψ) (corrFn C vc hv j ψ) Rr Bc Bp := by
  classical
  unfold EresAt energyAt polyAt pairSum
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext X
  simp [polyUniv]

open Classical in
/-- **Q13-FACTOR (1.1) for `EresJ2`'s index sets**: for one common composed field `ψ`, regions
`R' ⊆ R`, correction supports `B' ⊆ B` and polymer supports `Bp' ⊆ Bp`. -/
theorem EresAt_shrink (j : ℕ) {Rr Rr' Bc Bc' : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    {Bp Bp' : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)} (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (hR : Rr' ⊆ Rr) (hBc : Bc' ⊆ Bc) (hBp : Bp' ⊆ Bp) :
    EresAt C vc hv j Rr Bc Bp ψ - EresAt C vc hv j Rr' Bc' Bp' ψ =
      shrinkDeleted (polyUniv C j) (polyTerm C hv j ψ) Rr Rr' Bp +
        shrinkCrossing (polyUniv C j) (polyTerm C hv j ψ) Rr' Bp Bp' -
        shrinkFlux (corrFn C vc hv j ψ) Rr Rr' Bc Bc' := by
  rw [EresAt_eq_energyAt, EresAt_eq_energyAt]
  exact shrink_identity _ _ _ hR hBc hBp

open Classical in
/-- **Q13-FACTOR (1.1) for `EresJ2`** (regions `Y' ⊆ Y`, one common composed field `ψ`): the
difference of `EresJ2`'s index data, evaluated at `ψ`, is the deleted centres plus the crossing
polymers minus the correction flux (P5 (1.8) with both `v₁, v₂`). -/
theorem EresJ2_shrink (j : ℕ) {Y Y' : Set (Torus S.d (n k))} (hY : Y' ⊆ Y)
    (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.sset (thickY R Y)) ψ -
      EresAt C vc hv j (C.alignedIn j Y') (C.alignedIn j (thickY R Y')) (C.sset (thickY R Y')) ψ =
      shrinkDeleted (polyUniv C j) (polyTerm C hv j ψ) (C.alignedIn j Y) (C.alignedIn j Y')
          (C.sset (thickY R Y)) +
        shrinkCrossing (polyUniv C j) (polyTerm C hv j ψ) (C.alignedIn j Y')
          (C.sset (thickY R Y)) (C.sset (thickY R Y')) -
        shrinkFlux (corrFn C vc hv j ψ) (C.alignedIn j Y) (C.alignedIn j Y')
          (C.alignedIn j (thickY R Y)) (C.alignedIn j (thickY R Y')) :=
  EresAt_shrink C vc hv j ψ (alignedIn_mono C j hY) (alignedIn_mono C j (thickY_mono hY))
    (sset_mono C (thickY_mono hY))

/-- The re-evaluation term of (1.2): `ℰ(R', B'; ψ_Y) - ℰ(R', B'; ψ_{Y'})`. -/
noncomputable def shrinkReeval (j : ℕ) (Y' : Set (Torus S.d (n k)))
    (ψY ψY' : Fld S.d S.L C.N₁ m₁ k N) : ℂ :=
  EresAt C vc hv j (C.alignedIn j Y') (C.alignedIn j (thickY R Y')) (C.sset (thickY R Y')) ψY -
    EresAt C vc hv j (C.alignedIn j Y') (C.alignedIn j (thickY R Y')) (C.sset (thickY R Y')) ψY'

open Classical in
/-- **Q13-FACTOR (1.2)**: for the two composed fields `ψ_Y`, `ψ_{Y'}`,
`ℰ(R,B;ψ_Y) - ℰ(R',B';ψ_{Y'})` is deleted + crossing - flux (all at `ψ_Y`) + re-evaluation. -/
theorem EresJ2_shrink_total (j : ℕ) {Y Y' : Set (Torus S.d (n k))} (hY : Y' ⊆ Y)
    (ψY ψY' : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.sset (thickY R Y)) ψY -
      EresAt C vc hv j (C.alignedIn j Y') (C.alignedIn j (thickY R Y')) (C.sset (thickY R Y'))
        ψY' =
      shrinkDeleted (polyUniv C j) (polyTerm C hv j ψY) (C.alignedIn j Y) (C.alignedIn j Y')
          (C.sset (thickY R Y)) +
        shrinkCrossing (polyUniv C j) (polyTerm C hv j ψY) (C.alignedIn j Y')
          (C.sset (thickY R Y)) (C.sset (thickY R Y')) -
        shrinkFlux (corrFn C vc hv j ψY) (C.alignedIn j Y) (C.alignedIn j Y')
          (C.alignedIn j (thickY R Y)) (C.alignedIn j (thickY R Y')) +
        shrinkReeval C vc hv j Y' ψY ψY' := by
  rw [← EresJ2_shrink C vc hv j hY ψY]
  unfold shrinkReeval
  ring

/-- **Non-vanishing of the flux** (P5 (1.8); `corrSum_ne_zero_example`): for `v₁ ≡ 1`, `v₂ ≡ 0`
and two sites with different `ψ²`, the pair-sum over `{y} × {x}` is nonzero, so with
`R = {y}`, `R' = ∅`, `B = {x}`, `B' = ∅` the flux term of (1.1) is not zero. -/
theorem shrinkFlux_ne_zero_example {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁]
    (νj : ℝ) (y x : Localization.CTorus d L N₁ m₁ k) (ψ : Fld d L N₁ m₁ k N) (h : Fin N → ℂ)
    (hne : dot (ψ x) (ψ x) ≠ dot (ψ y) (ψ y)) :
    shrinkFlux (fun y x => corrPair ((fun _ _ => (1 : ℂ)) y x) ((fun _ _ => (0 : ℂ)) y x) νj ψ h y x)
      {y} ∅ {x} ∅ ≠ 0 := by
  classical
  have := corrSum_ne_zero_example νj y x ψ h hne
  unfold shrinkFlux pairSum
  simpa [corrSum] using this

end Landed

end Balaban.LargeField.RegionShrink
