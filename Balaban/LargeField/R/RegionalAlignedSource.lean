/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RegionalAligned
public import Balaban.LargeField.R.RadialCoefficientLimitEres
public import Balaban.LargeField.R.RadialCoefficientLimitInhab
public import Balaban.SmallField.Def6v2Renorm
import Mathlib.Tactic.Ring

/-!
# The source-facing A-term on the scale-`j` lattice

## Convention

In P5 (1.8) and P1 (3.104) the sums defining the renormalization A-term and its correction run
over the sites of the scale-`j` lattice, each site counted once, with no factor `L^{-jd}`
(`notes/phase1/Q13-ALIGN.md`).  On the fine torus of the repository the scale-`j` sites are the
`L^j`-aligned sites.  The landed correction `corrSum` inside `EresAt`/`EresJ2` follows this
convention.  The statements `EresAt_eq_aterm_aCoef_far` and `EresJ2_eq_aterm_aCoef_far`
(`RadialCoefficientLimitEres.lean`) are true finite algebra, but their A-term sums over every
fine site `x` with the block-constant kernel `w ↦ a (unlift j w)`; that is not the source A-term.
Here the A-term is taken with the **aligned kernel** `alignedKernel C j (fun w => a (unlift j w))`
(`RegionalAligned.lean`: `a (unlift j w)` for aligned `w`, `0` otherwise).

## Contents

* `AtermCentre_alignedKernel`, `AtermCentre_alignedKernel_unlift`: for an aligned centre `y` the
  A-term with the aligned kernel is exactly `½ Σ_{x aligned} a (unlift j (x - y)) (s x - s y)`.
* `EresAt_eq_aterm_far_aligned`, `EresAt_eq_aterm_aCoef_far_aligned`,
  `EresJ2_eq_aterm_aCoef_far_aligned`, `EresJ2_eq_aterm_v1_far_aligned`: the aligned mirrors of
  the landed identities, in the form consumed by `grouped_bound_power_aligned`.
* `EresJ2_sub_remainder_le_aligned_of_class`: the coefficient premise `hv1` of
  `EresJ2_sub_remainder_le_aligned_of_radialCoeff` is discharged from `aCoef_avgFamilyA_eq_v1`.
  The bundle `GroupedInputsAligned` stays a hypothesis; its open fields are listed on that theorem.
* `aCoef_avgFamilyAM_eq_v1`: the coefficient bridge for the mass family `avgFamilyAM` of the
  second-version class (`IsSFFamily2.renormalization_aniso`).
* `sum_comp_eq_card_mul_sum`, `AtermCentre_blockConstant`: the multiplicity `L^{jd}` that refutes
  the all-fine transcription; `alignedKernel_zero`: the zero-class instance.

## Not proved here

`AlignedI6Transport` (the I6 decomposition and the coefficient bounds for aligned representatives,
i.e. the fields `a_decomp`, `a_coeff`, `v2_decomp`, `v2_coeff`, `E_bound` and the data fields of
`GroupedBase`), the count `|R'| ≤ Γ_E s^{-d}` of centres, the energy identity and the common
tube.
-/

@[expose] public section

open Finset Balaban.LargeField.RegionEnergyAlgebra Balaban.LargeField.RegionalFlux

namespace Balaban.LargeField.RegionalAlignedSource

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.LargeField.RegionShrink Balaban.LargeField.RegionalAligned
  Balaban.LargeField.RegionalGroupedBound

/-! ### The aligned A-term is the scale-`j` sum -/

section Centre

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

open Classical in
/-- **T1 (general kernel).**  For an `L^j`-aligned centre `y`, the A-term with the aligned kernel
of `b` is `½ Σ_{x aligned} b (x - y) (s x - s y)`: no factor, and sites over non-aligned `x`
contribute nothing. -/
theorem AtermCentre_alignedKernel {j : ℕ} (hj : j ≤ k)
    (b : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (s : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : Aligned (S.L ^ j) y) :
    AtermCentre (alignedKernel C j b) s y =
      (1 / 2 : ℂ) * ∑ x ∈ Finset.univ.filter (fun x => Aligned (S.L ^ j) x),
        b (x - y) * (s x - s y) := by
  have : NeZero (S.L ^ j) := neZero_pow_L
  have hdvd := pow_dvd_side C hj
  unfold AtermCentre
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : Aligned (S.L ^ j) x
  · simp [alignedKernel_of_aligned C b (aligned_sub hdvd hx hy), hx]
  · have hxy : ¬ Aligned (S.L ^ j) (x - y) := fun h => hx (aligned_of_sub hdvd hy h)
    simp [alignedKernel_of_not C b hxy, hx]

open Classical in
/-- **T1.**  For a kernel `a` on the scale-`j` coordinate lattice and an aligned centre `y`,
`AtermCentre (alignedKernel (a ∘ unlift j)) s y = ½ Σ_{x aligned} a (unlift j (x - y)) (s x - s y)`
(P5 (1.8), P1 (3.104)). -/
theorem AtermCentre_alignedKernel_unlift {j : ℕ} (hj : j ≤ k) (a : SmallField.Site S.d → ℂ)
    (s : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    {y : Localization.CTorus S.d S.L C.N₁ m₁ k} (hy : Aligned (S.L ^ j) y) :
    AtermCentre (alignedKernel C j (fun w => a (unlift j w))) s y =
      (1 / 2 : ℂ) * ∑ x ∈ Finset.univ.filter (fun x => Aligned (S.L ^ j) x),
        a (unlift j (x - y)) * (s x - s y) :=
  AtermCentre_alignedKernel C hj _ s hy

/-- The coefficient premise on aligned pairs: if `f (unlift j ·)` is the coefficient of the
correction, then it is the aligned kernel on every pair of aligned sites. -/
theorem aligned_hv1 {j : ℕ} (hj : j ≤ k) (f : SmallField.Site S.d → ℂ)
    {Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k)}
    (hR : ∀ y ∈ Rr, Aligned (S.L ^ j) y) (hB : ∀ x ∈ Bc, Aligned (S.L ^ j) x) :
    ∀ y ∈ Rr, ∀ x ∈ Bc,
      f (unlift j (x - y)) = alignedKernel C j (fun w => f (unlift j w)) (x - y) := by
  have : NeZero (S.L ^ j) := neZero_pow_L
  have hdvd := pow_dvd_side C hj
  intro y hy x hx
  rw [alignedKernel_of_aligned C _ (aligned_sub hdvd (hB x hx) (hR y hy))]

end Centre

/-! ### Source-facing identities with the aligned kernel -/

section Identities

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N))

open Classical in
/-- **The landed correction energy against the regional A-term of any kernel `b`** that agrees
with the correction coefficient on the pairs `(y, x) ∈ Rr × Bc` the correction uses.  No
alignment is assumed here; the aligned versions below take `b` aligned. -/
theorem EresAt_eq_aterm_far_aligned (j : ℕ)
    (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N)
    (b : Localization.CTorus S.d S.L C.N₁ m₁ k → ℂ)
    (hv1 : ∀ y ∈ Rr, ∀ x ∈ Bc, vc.v1 j (unlift j (x - y)) = b (x - y)) :
    EresAt C vc hv j Rr Bc Bp ψ =
      (∑ y ∈ Rr,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
            IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ Bp},
          (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))) -
        AtermRegion b (fun x => dot (ψ x) (ψ x)) Rr +
        farCrossing b (fun x => dot (ψ x) (ψ x)) Rr Bc -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ
          (hC hv) := by
  have h := AtermRegion_sub_corrSum (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (N := N)
    b (fun y x => vc.v2 j (unlift j (x - y)))
    (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ (hC hv)
  have h2 : corrSum (fun y x => vc.v1 j (unlift j (x - y))) (fun y x => vc.v2 j (unlift j (x - y)))
      (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ (hC hv) =
      corrSum (fun y x => b (x - y)) (fun y x => vc.v2 j (unlift j (x - y)))
        (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ (hC hv) := by
    unfold corrSum corrPair
    refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
    beta_reduce
    rw [hv1 y hy x hx]
  unfold EresAt
  rw [h2]
  linear_combination h

open Classical Balaban.SmallField.Def6v2 in
/-- **T2 (v₁ kernel).**  `EresAt` against the regional A-term with the aligned kernel of
`vc.v1 j ∘ unlift j`, for aligned `Rr`, `Bc`. -/
theorem EresAt_eq_aterm_v1_far_aligned {j : ℕ} (hj : j ≤ k)
    (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (hR : ∀ y ∈ Rr, Aligned (S.L ^ j) y) (hB : ∀ x ∈ Bc, Aligned (S.L ^ j) x)
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j Rr Bc Bp ψ =
      (∑ y ∈ Rr,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
            IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ Bp},
          (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))) -
        AtermRegion (alignedKernel C j (fun w => vc.v1 j (unlift j w)))
          (fun x => dot (ψ x) (ψ x)) Rr +
        farCrossing (alignedKernel C j (fun w => vc.v1 j (unlift j w)))
          (fun x => dot (ψ x) (ψ x)) Rr Bc -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ
          (hC hv) :=
  EresAt_eq_aterm_far_aligned C vc hv j Rr Bc Bp ψ _
    (aligned_hv1 C hj (fun z => vc.v1 j z) hR hB)

open Classical Balaban.SmallField.Def6v2 in
/-- **T2 (v₁ kernel, `EresJ2`).** -/
theorem EresJ2_eq_aterm_v1_far_aligned {j : ℕ} (hj : j ≤ k) (Y : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    EresJ2 C vc Y ψk hv j =
      (∑ y ∈ C.alignedIn j Y,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
            IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
          (C.sf.Tm C.N₁).E j y X (C.psiJ Y ψk hv j) (constFld (hC hv))) -
        AtermRegion (alignedKernel C j (fun w => vc.v1 j (unlift j w)))
          (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) (C.alignedIn j Y) +
        farCrossing (alignedKernel C j (fun w => vc.v1 j (unlift j w)))
          (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) (C.alignedIn j Y)
          (C.alignedIn j (thickY R Y)) -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j)
          (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.psiJ Y ψk hv j) (hC hv) := by
  rw [EresJ2_eq_EresAt]
  exact EresAt_eq_aterm_v1_far_aligned C vc hv hj _ _
    (fun y hy => aligned_of_mem_alignedIn hy) (fun x hx => aligned_of_mem_alignedIn hx) _ _

open Classical Balaban.SmallField.Def6v2 in
/-- **T2.  The aligned mirror of `EresAt_eq_aterm_aCoef_far`.**  Same hypotheses (plus alignment
of the regions `Rr`, `Bc`, which the landed `EresJ2` has by construction); the A-term is taken
with the aligned kernel of `aCoef (avgFamilyA …)`, the marginal kernel of the renormalization
step. -/
theorem EresAt_eq_aterm_aCoef_far_aligned {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (hR : ∀ y ∈ Rr, Aligned (S.L ^ j) y) (hB : ∀ x ∈ Bc, Aligned (S.L ^ j) x)
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j Rr Bc Bp ψ =
      (∑ y ∈ Rr,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
            IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ Bp},
          (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))) -
        AtermRegion (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm
          j i₀ (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w))) (fun x => dot (ψ x) (ψ x)) Rr +
        farCrossing (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm
          j i₀ (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w))) (fun x => dot (ψ x) (ψ x)) Rr Bc -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ
          (hC hv) := by
  have hD' : D1Corr P.m₀ C.sf St hv vc := hP ▸ hD
  have hker : (fun w : Localization.CTorus S.d S.L C.N₁ m₁ k => vc.v1 j (unlift j w)) =
      fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
        (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
        (nuIdeal S.L k (C.sf.ν k) j) (unlift j w) :=
    funext fun w => (aCoef_avgFamilyA_eq_v1 hD' hF hn hne hhv (unlift j w)).symm
  have := EresAt_eq_aterm_v1_far_aligned C vc hv hn.hjk Rr Bc hR hB Bp ψ
  rwa [hker] at this

open Classical Balaban.SmallField.Def6v2 in
/-- **T2.  The aligned mirror of `EresJ2_eq_aterm_aCoef_far`.** -/
theorem EresJ2_eq_aterm_aCoef_far_aligned {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    EresJ2 C vc Y ψk hv j =
      (∑ y ∈ C.alignedIn j Y,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) |
            IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ C.sset (thickY R Y)},
          (C.sf.Tm C.N₁).E j y X (C.psiJ Y ψk hv j) (constFld (hC hv))) -
        AtermRegion (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm
          j i₀ (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)))
          (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) (C.alignedIn j Y) +
        farCrossing (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm
          j i₀ (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)))
          (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) (C.alignedIn j Y)
          (C.alignedIn j (thickY R Y)) -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j)
          (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.psiJ Y ψk hv j) (hC hv) := by
  rw [EresJ2_eq_EresAt]
  exact EresAt_eq_aterm_aCoef_far_aligned C vc hv hP hD hF hn hne hhv _ _
    (fun y hy => aligned_of_mem_alignedIn hy) (fun x hx => aligned_of_mem_alignedIn hx) _ _

open Classical Balaban.SmallField.Def6v2 in
/-- **T3.  The deliverable with `hv1` discharged.**  For a `D1Corr` datum of a class family, the
bound `EresJ2_sub_remainder_le_aligned_of_radialCoeff` holds with the aligned kernel
`a := alignedKernel C j (aCoef (avgFamilyA …) ∘ unlift j)`; the coefficient premise `hv1` does not
appear.  What remains in `g : GroupedInputsAligned` is open: the I6 decomposition `a_decomp`,
`v2_decomp` of the coefficients into per-polymer pieces and their row bounds `a_coeff`,
`v2_coeff` (`AlignedI6Transport`), `E_bound` (H4), and the data/geometry fields of `GroupedBase`
(small-field data, count of centres, margins).  The field `a_supp` holds for the aligned kernel by
definition (`alignedKernel_of_not`). -/
theorem EresJ2_sub_remainder_le_aligned_of_class {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (hN : S.L ^ C.m₀ ∣ C.N₁) (Y : Set (Torus S.d (n k)))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    {c cv : Set (SiteT C) → SiteT C → SiteT C → ℂ}
    {E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq : ℝ}
    (g : GroupedInputsAligned C j Y (C.alignedIn j Y) (C.alignedIn j (thickY R Y))
      (C.psiJ Y ψk hv j) (hC hv) (nuIdeal S.L k (C.sf.ν k) j)
      (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
        (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
        (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)))
      (fun y x => vc.v2 j (unlift j (x - y))) c cv (polyTerm C hv j (C.psiJ Y ψk hv j))
      E₀ κ κ₀ Rs dd α₃ α₁ α C₀ K_r K_R B εj εq) :
    ‖EresJ2 C vc Y ψk hv j -
        ∑ y ∈ C.alignedIn j Y, (Efull (polyUniv C j) (polyTerm C hv j (C.psiJ Y ψk hv j)) y -
          AtermCentre (alignedKernel C j (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a
            C.sf.Tm j i₀ (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
            (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)))
            (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) y)‖ ≤
      (C.alignedIn j Y).card * ((RegionalGroupedBound.farConst C κ κ₀ Rs dd α₃ C₀ K_r K_R +
        RegionalGroupedBound.v2Const (S := S) κ κ₀ B C₀ K_r K_R +
        RegionalGroupedBound.tailConst C κ κ₀ Rs dd α₃) * E₀ *
          scaleJ S.L k j ^ (dd + α₃)) := by
  have hD' : D1Corr P.m₀ C.sf St hv vc := hP ▸ hD
  refine EresJ2_sub_remainder_le_aligned_of_radialCoeff vc hv hN hn.hjk Y ψk ?_ g
  intro y hy x hx
  have e : vc.v1 j (unlift j (x - y)) = aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
    (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
    (nuIdeal S.L k (C.sf.ν k) j) (unlift j (x - y)) :=
    (aCoef_avgFamilyA_eq_v1 hD' hF hn hne hhv (unlift j (x - y))).symm
  have : NeZero (S.L ^ j) := neZero_pow_L
  have hdvd := pow_dvd_side C hn.hjk
  have hal := aligned_sub hdvd (aligned_of_mem_alignedIn hx) (aligned_of_mem_alignedIn hy)
  rw [alignedKernel_of_aligned C _ hal]
  exact e

end Identities

/-! ### The mass family of the second-version class -/

section Mass

open Balaban.SmallField.Def6v2 Balaban.LargeField.Def7v2 Balaban.SmallField.Def6 in
/-- **T4.  The coefficient bridge for the mass family.**  Let `h` be a member of the second-version
class (`IsSFFamily2`, complete domain) with terms `Tm`, and let `(sf, St, hv, vc)` be a `D1Corr`
datum for the same polymer exponent `P.m₀` whose terms are `Tm` and whose mass at the scale `k` is
the regime's, `sf.ν k = Rg.ν k`.  ("Matching" means exactly `sf.Tm = Tm` and `sf.ν k = Rg.ν k`:
`D1Corr` reads only `sf.Tm`, `sf.ν k` and `sf.corr`; the couplings `sf.β`, `sf.a` play no role.)
Then the marginal kernel of the family `avgFamilyAM` at the solver mass `Rg.sfBgMass k`, the one
of `IsSFFamily2.renormalization_aniso`, is the coefficient `vc.v1 j`.

Proof: `IsSFFamily2.toLanded` gives a landed class with coefficients `β', ν'`,
`ν' k = Rg.ν k`, `bgMass L k (β' k) (ν' k) = Rg.sfBgMass k`; the family `avgFamilyA` of that class
is `avgFamilyAM` at that mass by the definitional equality `avgFamilyA_eq`, and `D1Corr` transfers
to the data `sf` with `β, ν` replaced by `β', ν'` since it reads `ν` only at `k`. -/
theorem aCoef_avgFamilyAM_eq_v1 {d L N m₁ k : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts}
    {Rg : Regime L} {β a Ek : ℕ → ℝ}
    {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρ : ∀ (N₁ : ℕ) [NeZero N₁], (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    (h : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρ Ek)
    {sf : SFData d L m₁ k N ϱ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms d L N₁ m₁ k N} {hv : EuclideanSpace ℝ (Fin N)}
    {vc : CorrCoef d} (hD : D1Corr P.m₀ sf St hv vc) (hTm : sf.Tm = Tm)
    (hν : sf.ν k = Rg.ν k) {j : ℕ} (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    (hhv : ‖hv‖ = 1) (x : SmallField.Site d) :
    aCoef (avgFamilyAM P a (Rg.sfBgMass k) Tm j i₀ (nuIdeal L k (Rg.ν k) j)
        (anisoRadius d L N P j)) i₀ (nuIdeal L k (Rg.ν k) j) x = vc.v1 j x := by
  subst hTm
  obtain ⟨β', ν', hν', hμ, hF'⟩ := h.toLanded
  let sf' : SFData d L m₁ k N ϱ := { sf with β := β', ν := ν', a := a }
  have hνk : sf'.ν k = sf.ν k := by
    show ν' k = sf.ν k
    rw [hν', hν]
  have hD' : D1Corr P.noChi.m₀ sf' St hv vc :=
    { src_pos := fun N₁ _ j' h1 h2 hpos y X Ψ b => by
        rw [hνk] at hpos ⊢
        exact hD.src_pos N₁ j' h1 h2 hpos y X Ψ b
      v1_lim := fun j' h1 h2 z => by
        rw [hνk]; exact hD.v1_lim j' h1 h2 z
      v2_lim := fun j' h1 h2 e₂ he hp z => by
        rw [hνk]; exact hD.v2_lim j' h1 h2 e₂ he hp z
      corr_eq := fun N₁ _ j' h1 h2 y x' ψ hx hy => by
        rw [hνk]; exact hD.corr_eq N₁ j' h1 h2 y x' ψ hx hy }
  have key := aCoef_avgFamilyA_eq_v1 (sf := sf') hD' hF' hn.noChi hne hhv x
  rw [← key]
  have e1 : nuIdeal L k (Rg.ν k) j = nuIdeal L k (ν' k) j := by rw [hν']
  rw [e1]
  have e2 : avgFamilyAM P a (Rg.sfBgMass k) sf.Tm j i₀ (nuIdeal L k (ν' k) j)
        (anisoRadius d L N P j) =
      avgFamilyA P.noChi β' ν' a sf.Tm j i₀ (nuIdeal L k (ν' k) j)
        (anisoRadius d L N P.noChi j) := by
    rw [← hμ]; rfl
  rw [e2]

end Mass

/-! ### The multiplicity that refutes the all-fine transcription -/

section Multiplicity

/-- **T6(a), the multiplicity.**  If a function of `x` factors through a map `g` all of whose
fibres have `m` elements (for the block map `x ↦ jBlock x`, `m = L^(j d)`), then its sum over all
sites is `m` times the sum over the targets.  With `f x = a(unlift j (x-y)) (s x - s y)` for an
aligned `y` and a field `s` constant on `j`-blocks this is the factor `L^{jd}` between the
all-fine and the aligned A-term. -/
theorem sum_comp_eq_card_mul_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (g : ι → κ) (m : ℕ) (hfib : ∀ c, (Finset.univ.filter fun x => g x = c).card = m)
    (F : κ → ℂ) : ∑ x, F (g x) = (m : ℂ) * ∑ c, F c := by
  rw [← Finset.sum_fiberwise Finset.univ g (fun x => F (g x))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2] : ∀ x ∈
    Finset.univ.filter (fun x => g x = c), F (g x) = F c)]
  rw [Finset.sum_const, hfib c]
  simp

/-- The all-fine A-term of a kernel and field that factor through the block map `g` is `m` times
the sum over the blocks: `AtermCentre (A ∘ g) (S ∘ g) y = ½ m Σ_c A c (S c - s y)`.  Here the
kernel is read as a function of `x` (centre `y` fixed), as in the block-constant case of the
note. -/
theorem AtermCentre_blockConstant {ι κ : Type*} [AddCommGroup ι] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (g : ι → κ) (m : ℕ)
    (hfib : ∀ c, (Finset.univ.filter fun x => g x = c).card = m) (A Sf : κ → ℂ) (y : ι)
    (a : ι → ℂ) (hay : ∀ x, a (x - y) = A (g x)) (s : ι → ℂ)
    (hs : ∀ x, s x = Sf (g x)) :
    AtermCentre a s y = (1 / 2 : ℂ) * ((m : ℂ) * ∑ c, A c * (Sf c - s y)) := by
  unfold AtermCentre
  congr 1
  rw [← sum_comp_eq_card_mul_sum g m hfib (fun c => A c * (Sf c - s y))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hay, hs]

end Multiplicity

/-! ### Non-vacuity: the zero class -/

section Witness

/-- **T6(b).**  The zero kernel has zero aligned kernel.  The landed inhabitant of the coefficient
theorem (`nonempty_final_hypotheses`, `aCoef_avgFamilyA_eq_v1_witness` in
`RadialCoefficientLimitInhab.lean`) is the zero class: `aCoef (avgFamilyA …) = 0 = vc.v1 j`.  So
`aligned_hv1` and the hypotheses of `aCoef_avgFamilyA_eq_v1` are consistent there, with the
aligned kernel equal to `0`; this does not exercise a nonzero kernel.  A full instance of
`EresJ2_sub_remainder_le_aligned_of_class` would also need an `SFCtx` whose `sf` is that witness
data and a `GroupedInputsAligned`; neither is landed. -/
theorem alignedKernel_zero {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
    {M K : ℕ} [NeZero M] [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
    (j : ℕ) : alignedKernel C j (fun _ => 0) = 0 := by
  funext w
  unfold alignedKernel
  split_ifs <;> rfl

end Witness

end Balaban.LargeField.RegionalAlignedSource
