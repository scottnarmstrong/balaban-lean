/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Euclid
public import Balaban.Spine.LFOldD7Hist
public import Balaban.LargeField.Region.SymmLevel

/-!
# The local step under a lattice symmetry of the history (clause `euclid` of (D7))

A lattice symmetry `σ` of the history (`LatTorusSym`, `RegionIso σ H H'`) acts on the cover torus of
the step by the affine isometry `coverAff σ`.  Here the layers of `p6Hold` and `p6Top` of the two
histories are shown to correspond (`stepW_map`, `minLayer_map`, `fineK1_map`), the first step of
the proof that the local steps are related by `StepAff`.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Balaban.Fluctuation

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

open Balaban.LargeField.RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- **The affine isometry of the cover torus of the step induced by a lattice symmetry.** -/
def coverAff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) :
    AffIso S.d ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1)) :=
  σ.aff.cast (coverSide g hnn hM1 hk).symm

theorem torusCast_cancel {d a b : ℕ} (h : a = b) (y : Torus d b) :
    LargeField.torusCast h (LargeField.torusCast h.symm y) = y := by
  subst h; rfl

theorem torusCast_cancel' {d a b : ℕ} (h : a = b) (y : Torus d a) :
    LargeField.torusCast h.symm (LargeField.torusCast h y) = y := by
  subst h; rfl

theorem fineOfC_coverAff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    fineOfC g hnn hM1 hk ((coverAff g hnn hM1 σ hk).toFun x) = σ.ef (fineOfC g hnn hM1 hk x) := by
  unfold coverAff fineOfC
  rw [σ.ef_aff]
  have := AffIso.cast_toFun (coverSide g hnn hM1 hk).symm σ.aff
    (LargeField.torusCast (coverSide g hnn hM1 hk) x)
  rw [torusCast_cancel'] at this
  rw [this, torusCast_cancel]

/-- The cover isometry, as an isometry of the torus of `W_k` (`M₁ (c n_{k+1}) L^{k+1}`). -/
def stepAff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) :
    AffIso S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)) :=
  (coverAff g hnn hM1 σ hk).cast (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c)
    (n1 := n (k + 1)) hM1)).symm

theorem stepAff_coarse (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) (P m : ℕ) :
    (stepAff g hnn hM1 σ hk).coarse P m = σ.aff.coarse P m := by
  unfold stepAff coverAff
  rw [AffIso.coarse_cast, AffIso.coarse_cast]

theorem stepAff_aligned (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) :
    (stepAff g hnn hM1 σ hk).Aligned (g.c * g.M1 * S.L ^ (k + 1)) := by
  unfold stepAff coverAff
  refine AffIso.cast_aligned _ _ (AffIso.cast_aligned _ _ ?_)
  refine σ.aligned_of_dvd ?_
  have h : M * S.L ^ K = g.c * g.M1 * S.L ^ K := congrArg (· * S.L ^ K) g.hM
  rw [h]
  exact Nat.mul_dvd_mul_left _ (pow_dvd_pow S.L hk)

theorem stepAff_toFun (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (stepAff g hnn hM1 σ hk).toFun ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c)
      (n1 := n (k + 1)) hM1)).symm ▸ x) =
      (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸
        (coverAff g hnn hM1 σ hk).toFun x :=
  AffIso.cast_toFun _ _ x

theorem step_Z_aff (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
    (hI : RegionIso σ H H') {k : ℕ} (hk : k + 1 ≤ K) :
    (H'.step k).Z = ((stepAff g hnn hM1 σ hk).coarse (S.L ^ k * (g.c * g.M1)) (n k)).toFun ''
      (H.step k).Z := by
  rw [stepAff_coarse, hI.hZ k (by omega)]
  have hf : ⇑(σ.ec k) = (σ.aff.coarse (S.L ^ k * M) (n k)).toFun :=
    funext (σ.ec_eq hnn (by omega : k ≤ K))
  have h : S.L ^ k * M = S.L ^ k * (g.c * g.M1) := congrArg (S.L ^ k * ·) g.hM
  rw [hf, h]

end Balaban.RootFSpine
