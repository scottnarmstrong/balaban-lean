/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RadialCoefficientLimit
public import Balaban.LargeField.R.RegionEnergyAlgebra

/-!
# The landed correction energy and the marginal kernel of the renormalization step

`RegionEnergyAlgebra.AtermRegion_sub_corrSum` is an identity for an abstract kernel `a` on a torus.
Here it is applied to the landed objects.  In `corrFn`/`EresAt`/`EresJ2` the coefficient of the
correction is `v₁(y, x) = vc.v1 j (unlift j (x - y))`, so the kernel is
`a_j(w) = vc.v1 j (unlift j w)` on the torus (`w = x - y`), which is exactly of the form `a (x - y)`
required by `AtermRegion_sub_corrSum`.

* `EresAt_eq_aterm_far`: for the landed `EresAt` (hence `EresJ2`, by `EresJ2_eq_EresAt`), the
  polymer sum minus `ℰ` is the regional A-term of the kernel `a_j` minus the far crossing sum plus
  the `v₂` part; no property of the class is used.
* `EresAt_eq_aterm_aCoef_far`: for a `D1Corr` datum of a class family, the kernel `a_j` is the
  marginal kernel `aCoef (avgFamilyA …)` of the renormalization step (`aCoef_avgFamilyA_eq_v1`), so
  the regional A-term is that of the renormalization kernel.

Evenness of the kernel `a_j` (needed to read the far crossing sum as a sum of crossing pairs,
`grouped_eq_far_crossing_even`) is not used here.
-/

@[expose] public section

namespace Balaban.LargeField.RadialLimitEres

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.LargeField.RegionShrink Balaban.LargeField.RegionEnergyAlgebra
  Balaban.LargeField.RegionalFlux

section Landed

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N))

open Classical in
/-- **The landed correction energy against the regional A-term.**  With the kernel
`a_j(w) = vc.v1 j (unlift j w)` of the landed correction,
`EresAt = ∑_{y∈R} ∑_{X ∋ y, X ⊆ Bp} ℰ(y, X) - ∑_{y∈R} A_{a_j}(y) + (far crossing sum of a_j) - (v₂ part)`. -/
theorem EresAt_eq_aterm_far (j : ℕ) (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j Rr Bc Bp ψ =
      (∑ y ∈ Rr,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | IsPolyDom C.m₀ j X ∧ y ∈ X ∧ X ⊆ Bp},
          (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))) -
        AtermRegion (fun w => vc.v1 j (unlift j w)) (fun x => dot (ψ x) (ψ x)) Rr +
        farCrossing (fun w => vc.v1 j (unlift j w)) (fun x => dot (ψ x) (ψ x)) Rr Bc -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ
          (hC hv) := by
  have h := AtermRegion_sub_corrSum (L := S.L) (N₁ := C.N₁) (m₁ := m₁) (k := k) (N := N)
    (fun w => vc.v1 j (unlift j w)) (fun y x => vc.v2 j (unlift j (x - y)))
    (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ (hC hv)
  unfold EresAt
  linear_combination h

open Classical Balaban.SmallField.Def6v2 in
/-- **The landed correction energy against the regional A-term of the renormalization kernel.**
For a `D1Corr` datum `(St, hv, vc)` of a class family `hF` (`‖hv‖ = 1`), at a scale `j` with the
numeric premises `MomNum`, the kernel `a_j(w) = vc.v1 j (unlift j w)` of the landed correction is the
marginal kernel `w ↦ aCoef (avgFamilyA …) (unlift j w)` of the renormalization step
(`aCoef_avgFamilyA_eq_v1`), so the identity `EresAt_eq_aterm_far` reads with the regional A-term of
the renormalization kernel: the localized terms minus `ℰ` is the regional A-term of the
renormalization kernel minus the far crossing sum, plus the `v₂` part. -/
theorem EresAt_eq_aterm_aCoef_far {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (Rr Bc : Finset (Localization.CTorus S.d S.L C.N₁ m₁ k))
    (Bp : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (ψ : Fld S.d S.L C.N₁ m₁ k N) :
    EresAt C vc hv j Rr Bc Bp ψ =
      (∑ y ∈ Rr,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | IsPolyDom C.m₀ j X ∧ y ∈ X ∧
            X ⊆ Bp},
          (C.sf.Tm C.N₁).E j y X ψ (constFld (hC hv))) -
        AtermRegion (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
          (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)) (fun x => dot (ψ x) (ψ x)) Rr +
        farCrossing (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
          (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w)) (fun x => dot (ψ x) (ψ x)) Rr Bc -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j) Rr Bc ψ
          (hC hv) := by
  have hD' : D1Corr P.m₀ C.sf St hv vc := hP ▸ hD
  have hker : (fun w : Localization.CTorus S.d S.L C.N₁ m₁ k => vc.v1 j (unlift j w)) =
      fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
        (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
        (nuIdeal S.L k (C.sf.ν k) j) (unlift j w) :=
    funext fun w => (aCoef_avgFamilyA_eq_v1 hD' hF hn hne hhv (unlift j w)).symm
  rw [EresAt_eq_aterm_far, hker]

open Classical Balaban.SmallField.Def6v2 in
/-- The same identity for the landed `EresJ2`, at its regions `alignedIn j Y`,
`alignedIn j (thickY R Y)`, support `sset (thickY R Y)` and field `psiJ`. -/
theorem EresJ2_eq_aterm_aCoef_far {P : Consts} {ρd : ∀ (N₁ : ℕ) [NeZero N₁],
      (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
        (Localization.CTorus S.d S.L N₁ m₁ k → Fin N → ℝ) → ℝ} {Ek : ℕ → ℝ}
    {St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ m₁ k N}
    (hP : P.m₀ = C.m₀) (hD : D1Corr C.m₀ C.sf St hv vc)
    (hF : IsSFFamily P C.sf.β C.sf.ν C.sf.a C.sf.Tm ρd Ek) {j : ℕ}
    (hn : MomNum S.d S.L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) (hhv : ‖hv‖ = 1)
    (Y : Set (Torus S.d (n k))) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    EresJ2 C vc Y ψk hv j =
      (∑ y ∈ C.alignedIn j Y,
        ∑ᶠ X ∈ {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k) | IsPolyDom C.m₀ j X ∧ y ∈ X ∧
            X ⊆ C.sset (thickY R Y)},
          (C.sf.Tm C.N₁).E j y X (C.psiJ Y ψk hv j) (constFld (hC hv))) -
        AtermRegion (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
          (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w))
          (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) (C.alignedIn j Y) +
        farCrossing (fun w => aCoef (avgFamilyA P C.sf.β C.sf.ν C.sf.a C.sf.Tm j i₀
          (nuIdeal S.L k (C.sf.ν k) j) (anisoRadius S.d S.L N P j)) i₀
          (nuIdeal S.L k (C.sf.ν k) j) (unlift j w))
          (fun x => dot (C.psiJ Y ψk hv j x) (C.psiJ Y ψk hv j x)) (C.alignedIn j Y)
          (C.alignedIn j (thickY R Y)) -
        v2Part (fun y x => vc.v2 j (unlift j (x - y))) (nuIdeal S.L k (C.sf.ν k) j)
          (C.alignedIn j Y) (C.alignedIn j (thickY R Y)) (C.psiJ Y ψk hv j) (hC hv) := by
  rw [EresJ2_eq_EresAt]
  exact EresAt_eq_aterm_aCoef_far C vc hv hP hD hF hn hne hhv _ _ _ _

end Landed

end Balaban.LargeField.RadialLimitEres
