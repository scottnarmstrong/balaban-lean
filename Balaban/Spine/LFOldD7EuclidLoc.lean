/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldD7Euclid
public import Balaban.Spine.LFOldD7Hist
public import Balaban.Spine.LFOldD7Reads
public import Balaban.LargeField.Region.SymmLevel

/-!
# The local step under a lattice symmetry of the history (clause `euclid` of (D7))

A lattice symmetry `σ` of the history (`LatTorusSym`, `RegionIso σ H H'`) acts on the cover torus of
the step by the affine isometry `coverAff σ`.  Here the layers of `p6Hold` and `p6Top` of the two
histories are shown to correspond (`stepW_map`, `minLayer_map`, `fineK1_map`), the first step of
the proof that the local steps are related by `StepAff`.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization Balaban.Localization.DecEquiv
  Balaban.LargeField Balaban.Fluctuation

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

open Balaban.LargeField.RegionHistory Balaban.LargeField.Def7

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

theorem step_Omega_aff (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
    (hI : RegionIso σ H H') {k : ℕ} (hk : k + 1 ≤ K) :
    (H'.step k).Omega = ((stepAff g hnn hM1 σ hk).coarse (S.L ^ (k + 1) * (g.c * g.M1))
      (n (k + 1))).toFun '' (H.step k).Omega := by
  rw [stepAff_coarse, hI.omega hk]
  have hf : ⇑(σ.ec (k + 1)) = (σ.aff.coarse (S.L ^ (k + 1) * M) (n (k + 1))).toFun :=
    funext (σ.ec_eq hnn hk)
  have h : S.L ^ (k + 1) * M = S.L ^ (k + 1) * (g.c * g.M1) :=
    congrArg (S.L ^ (k + 1) * ·) g.hM
  rw [hf, h]

variable (H H' : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
  (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (ψ ψ₁ : MultiFieldC S n M K N) (z : ℝ) (h₀ : Fin N → ℝ)
  (a₁ ν β p₁ δ : ℝ)

/-- **The old set `G` of the step is carried by the lattice symmetry.** -/
theorem holeStepLF_G_aff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (j : ℕ)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈
        (holeStepLF g hnn hM1 H' hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).G.Ω j ↔
      x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G.Ω j := by
  rw [holeStepLF_G_Ω, holeStepLF_G_Ω, ← stepAff_toFun g hnn hM1 σ hk x]
  have hal := stepAff_aligned g hnn hM1 σ hk
  have hn : n k = S.L * n (k + 1) := hnn k (by omega)
  have h1 := stepW_map hal hn (⌊R (k - 1)⌋₊) (H.step k).Z
  rw [← step_Z_aff g hnn hM1 σ hI hk] at h1
  have h2 := minLayer_map (A := stepAff g hnn hM1 σ hk) (c := g.c) hal (j := k) (Nat.le_succ k)
    (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j
  rw [h1] at h2
  have key : ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
      (stepAff g hnn hM1 σ hk).toFun y ∈ minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
        (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z) j ↔
      y ∈ minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
        (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j := by
    intro y
    rw [h2, Finset.mem_map_equiv]
    have e : (stepAff g hnn hM1 σ hk).toEquiv.symm ((stepAff g hnn hM1 σ hk).toFun y) = y :=
      (stepAff g hnn hM1 σ hk).invFun_toFun y
    rw [e]
  exact key _

theorem holeStepLF_G'_Ω_top' (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω (k + 1) ↔
      ((congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm ▸ x :
        Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))) ∈
        fineK1 g.M1 g.c (n (k + 1)) S.L k (H.step k).Omega := by
  unfold holeStepLF holeStepOf
  dsimp only
  rw [p6TopC, mem_castN_Ω, p6Top_Ω_top]

/-- **The set `G'` of the step is carried by the lattice symmetry.** -/
theorem holeStepLF_G'_aff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (j : ℕ)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈
        (holeStepLF g hnn hM1 H' hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ).G'.Ω j ↔
      x ∈ (holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.Ω j := by
  by_cases hj : j = k + 1
  · subst hj
    rw [holeStepLF_G'_Ω_top', holeStepLF_G'_Ω_top', ← stepAff_toFun g hnn hM1 σ hk x]
    have hal := stepAff_aligned g hnn hM1 σ hk
    have hn : n k = S.L * n (k + 1) := hnn k (by omega)
    have h1 := fineK1_map hal hn (H.step k).Omega
    rw [← step_Omega_aff g hnn hM1 σ hI hk] at h1
    have key : ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
        (stepAff g hnn hM1 σ hk).toFun y ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (H'.step k).Omega ↔
        y ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (H.step k).Omega := by
      intro y
      rw [← h1, Finset.mem_map_equiv]
      have e : (stepAff g hnn hM1 σ hk).toEquiv.symm ((stepAff g hnn hM1 σ hk).toFun y) = y :=
        (stepAff g hnn hM1 σ hk).invFun_toFun y
      rw [e]
    exact key _
  · rw [holeStepLF_G'_Ω_of_ne g hnn hM1 H' hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ hj,
      holeStepLF_G'_Ω_of_ne g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ hj,
      ← stepAff_toFun g hnn hM1 σ hk x]
    have hal := stepAff_aligned g hnn hM1 σ hk
    have hn : n k = S.L * n (k + 1) := hnn k (by omega)
    have h1 := stepW_map hal hn (⌊R (k - 1)⌋₊) (H.step k).Z
    rw [← step_Z_aff g hnn hM1 σ hI hk] at h1
    have h2 := minLayer_map (A := stepAff g hnn hM1 σ hk) (c := g.c) hal (j := k)
      (Nat.le_succ k) (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j
    rw [h1] at h2
    have key : ∀ y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)),
        (stepAff g hnn hM1 σ hk).toFun y ∈ minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H'.step k).Z) j ↔
        y ∈ minLayer g.M1 (g.c * n (k + 1)) S.L (k + 1) k
          (stepW g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ (H.step k).Z) j := by
      intro y
      rw [h2, Finset.mem_map_equiv]
      have e : (stepAff g hnn hM1 σ hk).toEquiv.symm ((stepAff g hnn hM1 σ hk).toFun y) = y :=
        (stepAff g hnn hM1 σ hk).invFun_toFun y
      rw [e]
    exact key _

theorem coverAff_aligned (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) :
    (coverAff g hnn hM1 σ hk).Aligned (S.L ^ (k + 1 + m₁)) := by
  unfold coverAff
  refine AffIso.cast_aligned _ _ ?_
  refine σ.aligned_of_dvd ?_
  have h : M * S.L ^ K = g.c * S.L ^ m₁ * S.L ^ K := by
    have : M * S.L ^ K = g.c * g.M1 * S.L ^ K := congrArg (· * S.L ^ K) g.hM
    rw [this, hM1]
  rw [h, add_comm (k + 1) m₁, pow_add]
  exact Nat.mul_dvd_mul (dvd_mul_left _ _) (pow_dvd_pow S.L hk)

section LocB

open Balaban.SmallField.GsSpec in
theorem fineCubeIdx_eq_blockMap {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {n : ℕ}
    (x : CTorus d L N₁ m₁ k) :
    fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)) =
      blockMap (L ^ n * L ^ m₁) (N₁ * L ^ (k - n)) x := by
  funext ν
  rw [fineCubeIdx_torusCast_coord, blockMap_apply]

open Balaban.SmallField.GsSpec in
/-- An aligned affine isometry preserves the distances of the cube indices. -/
theorem localCube_aff {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]
    (A : AffIso d ((N₁ * L ^ m₁) * L ^ k)) {j : ℕ} (hj : j ≤ k) (hA : A.Aligned (L ^ (j + m₁)))
    {n : ℕ} (hn : n ≤ j) (x y : CTorus d L N₁ m₁ k) :
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (A.toEquiv x) : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n
        (torusCast (A.toEquiv y) : Torus d (L ^ m₁ * N₁ * L ^ k))) =
    supDist (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ k)))
      (fineCubeIdx (L ^ m₁) N₁ L k n (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ k))) := by
  rw [fineCubeIdx_eq_blockMap, fineCubeIdx_eq_blockMap, fineCubeIdx_eq_blockMap,
    fineCubeIdx_eq_blockMap]
  have hpos : 0 < L ^ n * L ^ m₁ := by have := NeZero.pos L; positivity
  have hℓ : N₁ * L ^ m₁ * L ^ k = (L ^ n * L ^ m₁) * (N₁ * L ^ (k - n)) :=
    side_eq_localCube (by omega)
  have hal : A.Aligned (L ^ n * L ^ m₁) := fun i =>
    dvd_trans (by rw [← pow_add]; exact pow_dvd_pow L (by omega)) (hA i)
  show supDist (blockMap _ _ (A.toFun x)) (blockMap _ _ (A.toFun y)) = _
  rw [A.blockMap_toFun hℓ hpos hal, A.blockMap_toFun hℓ hpos hal, AffIso.supDist_eq]

/-- **The layers of `𝔹_{k+1}(V)` under the lattice symmetry.** -/
theorem locB_aff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) (j : ℕ)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈
        (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V)).Ω j ↔
      x ∈ (locB g hM1 V).Ω j := by
  unfold locB
  have h := SmallField.GsSpec.mem_localB_Ω_image_iff_of_cubeIso (j := k + 1) (hj := le_rfl)
    (X := V) (hsep := minSep_le_locB g hM1)
    (r := (coverAff g hnn hM1 σ hk).toEquiv)
    (fun n hn x y => localCube_aff _ le_rfl (coverAff_aligned g hnn hM1 σ hk) hn x y) j
    ((coverAff g hnn hM1 σ hk).toFun x)
  have e : (coverAff g hnn hM1 σ hk).toEquiv.symm ((coverAff g hnn hM1 σ hk).toFun x) = x :=
    (coverAff g hnn hM1 σ hk).invFun_toFun x
  rw [e] at h
  exact h

end LocB

theorem coverBlk_aff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) (i : ℕ) (hi : i ≤ k + 1)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    coverBlk g hnn hM1 hk i hi ((coverAff g hnn hM1 σ hk).toFun x) =
      σ.eb i (coverBlk g hnn hM1 hk i hi x) := by
  rw [← jBlock_fineOfC g hnn hM1 hk i hi, ← jBlock_fineOfC g hnn hM1 hk i hi,
    fineOfC_coverAff, σ.jblock i (by omega)]

theorem blockLift_coverField_symM (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) (i : ℕ)
    (hi : i ≤ k + 1) (ψ : MultiFieldC S n M K N)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    blockLift i (coverField g hnn hM1 hk (symM σ ψ) i hi) ((coverAff g hnn hM1 σ hk).toFun x) =
      blockLift i (coverField g hnn hM1 hk ψ i hi) x := by
  show symM σ ψ i (coverBlk g hnn hM1 hk i hi ((coverAff g hnn hM1 σ hk).toFun x)) =
    ψ i (coverBlk g hnn hM1 hk i hi x)
  rw [coverBlk_aff, symM]
  simp

section LocStep

variable (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))

theorem holeStepLoc_G_aff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (j : ℕ)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈
        (holeStepLoc g hnn hM1 H' hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
          ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G.Ω j ↔
      x ∈ (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G.Ω j := by
  rw [holeStepLoc_G, holeStepLoc_G, GeneratingSet.inter_Ω, GeneratingSet.inter_Ω,
    Finset.mem_inter, Finset.mem_inter,
    holeStepLF_G_aff g hnn hM1 H H' hk hk1 hρ ψ ψ₁ z h₀ a₁ ν β p₁ δ σ hI,
    locB_aff g hnn hM1 σ hk V]

theorem holeStepLoc_G'_aff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (j : ℕ)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈
        (holeStepLoc g hnn hM1 H' hk hk1 hρ ψ₁ z h₀ a₁ ν β p₁ δ
          ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G'.Ω j ↔
      x ∈ (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'.Ω j := by
  rw [holeStepLoc_G', holeStepLoc_G', GeneratingSet.inter_Ω, GeneratingSet.inter_Ω,
    Finset.mem_inter, Finset.mem_inter,
    holeStepLF_G'_aff g hnn hM1 H H' hk hk1 hρ ψ ψ₁ z h₀ a₁ ν β p₁ δ σ hI,
    locB_aff g hnn hM1 σ hk V]

/-- **The datum of the local step is carried by the lattice symmetry.** -/
theorem holeStepLoc_D'_aff_Ψ (σ : LatTorusSym S n M K) (hI : RegionIso σ H H')
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (i : Fin N) :
    (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
      ((coverAff g hnn hM1 σ hk).toEquiv '' V)).D'.Ψ ((coverAff g hnn hM1 σ hk).toFun x) i =
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.Ψ x i := by
  classical
  have hal1 : (coverAff g hnn hM1 σ hk).Aligned (S.L ^ (k + 1)) :=
    fun i => dvd_trans (pow_dvd_pow S.L (by omega)) (coverAff_aligned g hnn hM1 σ hk i)
  set T := Balaban.Fluctuation.latSymmOfΩ (coverAff g hnn hM1 σ hk) hal1
    (holeStepLoc_G'_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI) with hT
  have hdata : (coverAff g hnn hM1 σ hk).toFun x ∈
      dataSites (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G' ↔
      x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' := by
    rw [mem_dataSites, mem_dataSites]
    exact or_congr (T.mem_Ω1 x) (T.mem_collar x)
  have hΩt : (coverAff g hnn hM1 σ hk).toFun x ∈
      ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))).Ω (k + 1) ↔
      x ∈ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 V)).Ω (k + 1) :=
    holeStepLoc_G'_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI (k + 1) x
  simp only [holeStepLoc_D'_eq, liftMixed, BgData.clip]
  by_cases hx : x ∈ dataSites ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
      (locB g hM1 V))
  · have h2 : (coverAff g hnn hM1 σ hk).toFun x ∈
        dataSites ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
          (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))) := hdata.2 hx
    simp only [hx, h2, ↓reduceIte]
    unfold mixedLift
    by_cases hΩ : x ∈ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 V)).Ω (k + 1)
    · simp only [hΩ, hΩt.2 hΩ, ↓reduceIte]
      have := blockLift_coverField_symM g hnn hM1 σ hk (k + 1) le_rfl (scaleMulti z ψ) x
      exact congrFun this i
    · have hΩn : (coverAff g hnn hM1 σ hk).toFun x ∉
          ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
            (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))).Ω (k + 1) :=
        fun h => hΩ (hΩt.1 h)
      simp only [hΩ, hΩn, ↓reduceIte]
      have := blockLift_coverField_symM g hnn hM1 σ hk k (Nat.le_succ k) ψ x
      exact congrFun this i
  · have h2 : (coverAff g hnn hM1 σ hk).toFun x ∉
        dataSites ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
          (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))) := fun h => hx (hdata.1 h)
    simp only [hx, h2, ↓reduceIte]

theorem holeStepLoc_D'_aff_h (σ : LatTorusSym S n M K) (hI : RegionIso σ H H')
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) (i : Fin N) :
    (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
      ((coverAff g hnn hM1 σ hk).toEquiv '' V)).D'.h ((coverAff g hnn hM1 σ hk).toFun x) i =
    (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'.h x i := by
  classical
  have hΩ1 : (coverAff g hnn hM1 σ hk).toFun x ∈
      ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))).Ω 1 ↔
      x ∈ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 V)).Ω 1 :=
    holeStepLoc_G'_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI 1 x
  simp only [holeStepLoc_D'_eq, liftMixed, BgData.clip]
  by_cases hx : x ∈ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
      (locB g hM1 V)).Ω 1
  · simp only [hx, hΩ1.2 hx, ↓reduceIte]
  · have hxn : (coverAff g hnn hM1 σ hk).toFun x ∉
        ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
          (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))).Ω 1 := fun h => hx (hΩ1.1 h)
    simp only [hx, hxn, ↓reduceIte]

/-- **The local steps of two histories related by a lattice symmetry are related by `StepAff`.** -/
theorem holeStepLoc_stepAff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (hm₁ : 2 ≤ m₁) :
    StepAff (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V)
      (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)) (coverAff g hnn hM1 σ hk) where
  hAl := coverAff_aligned g hnn hM1 σ hk
  hΩ := holeStepLoc_G_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI
  hΩ' := holeStepLoc_G'_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI
  hca' := holeStepLoc_cubeAligned g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _ hm₁
  hΨ := holeStepLoc_D'_aff_Ψ g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI
  hh := holeStepLoc_D'_aff_h g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI
  ha₁ := (holeStepLoc_consts g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _).2.1.trans
    (holeStepLoc_consts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).2.1.symm
  hν := (holeStepLoc_consts g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _).2.2.1.trans
    (holeStepLoc_consts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).2.2.1.symm
  hβ := (holeStepLoc_consts g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _).2.2.2.1.trans
    (holeStepLoc_consts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).2.2.2.1.symm

end LocStep

section Cubes

theorem cubeOfC_aff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    cubeOfC hM1 ((coverAff g hnn hM1 σ hk).toFun x) =
      ((stepAff g hnn hM1 σ hk).coarse (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1))).toFun
        (cubeOfC hM1 x) := by
  unfold cubeOfC
  rw [← stepAff_toFun g hnn hM1 σ hk x]
  have hpos : 0 < S.L ^ (k + 1) * (g.c * g.M1) := by
    have := NeZero.pos S.L; have := NeZero.pos g.c; have := NeZero.pos g.M1; positivity
  exact AffIso.blockMap_level (stepAff_aligned g hnn hM1 σ hk) (by ring) hpos
    ⟨1, by ring⟩ _

theorem cubeKOfC_aff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    cubeKOfC (n0 := n k) hM1 ((coverAff g hnn hM1 σ hk).toFun x) =
      ((stepAff g hnn hM1 σ hk).coarse (S.L ^ k * (g.c * g.M1)) (n k)).toFun
        (cubeKOfC (n0 := n k) hM1 x) := by
  unfold cubeKOfC
  rw [← stepAff_toFun g hnn hM1 σ hk x]
  have hpos : 0 < S.L ^ k * (g.c * g.M1) := by
    have := NeZero.pos S.L; have := NeZero.pos g.c; have := NeZero.pos g.M1; positivity
  have hn : n k = S.L * n (k + 1) := hnn k (by omega)
  exact AffIso.blockMap_level (stepAff_aligned g hnn hM1 σ hk) (by rw [hn]; ring) hpos
    ⟨S.L, by ring⟩ _

theorem stepAff_coarse_ec (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K) (i : ℕ)
    (hi : i ≤ K) :
    ((stepAff g hnn hM1 σ hk).coarse (S.L ^ i * (g.c * g.M1)) (n i)).toFun = σ.ec i := by
  rw [stepAff_coarse]
  have h : S.L ^ i * M = S.L ^ i * (g.c * g.M1) := congrArg (S.L ^ i * ·) g.hM
  funext y
  rw [σ.ec_eq hnn hi, h]

theorem mem_activeCoreC_aff (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
    (hI : RegionIso σ H H') {k : ℕ} (hk : k + 1 ≤ K) (X : Finset (Torus S.d (n k)))
    (y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun y ∈
        activeCoreC (c := g.c) (k := k) (H'.step k) hM1 (X.map (σ.ec k).toEmbedding) ↔
      y ∈ activeCoreC (c := g.c) (k := k) (H.step k) hM1 X := by
  rw [mem_activeCoreC, mem_activeCoreC, cubeOfC_aff g hnn hM1 σ hk, cubeKOfC_aff g hnn hM1 σ hk,
    step_Omega_aff g hnn hM1 σ hI hk, stepAff_coarse_ec g hnn hM1 σ hk k (by omega)]
  have hf := stepAff_coarse_ec g hnn hM1 σ hk (k + 1) hk
  rw [hf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_map_equiv] at h1
      simpa using h1
    · obtain ⟨z, hz, hz'⟩ := h2
      have := (σ.ec (k + 1)).injective hz'
      rw [← this]; exact hz
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ⟨_, h2, rfl⟩⟩
    rw [Finset.mem_map_equiv]
    simpa using h1

theorem mem_collarCoreC_aff (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
    (hI : RegionIso σ H H') {k : ℕ} (hk : k + 1 ≤ K) (r : ℕ) (X : Finset (Torus S.d (n k)))
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈
        collarCoreC (c := g.c) (k := k) (H'.step k) hM1 r (X.map (σ.ec k).toEmbedding) ↔
      x ∈ collarCoreC (c := g.c) (k := k) (H.step k) hM1 r X := by
  rw [mem_collarCoreC, mem_collarCoreC]
  constructor
  · rintro ⟨y', hy', hd⟩
    obtain ⟨y, rfl⟩ := (coverAff g hnn hM1 σ hk).toEquiv.surjective y'
    have hy : y ∈ activeCoreC (c := g.c) (k := k) (H.step k) hM1 X :=
      (mem_activeCoreC_aff g hnn hM1 σ hI hk X y).1 hy'
    refine ⟨y, hy, ?_⟩
    rw [← (coverAff g hnn hM1 σ hk).supDist_eq]
    exact hd
  · rintro ⟨y, hy, hd⟩
    refine ⟨(coverAff g hnn hM1 σ hk).toFun y, (mem_activeCoreC_aff g hnn hM1 σ hI hk X y).2 hy, ?_⟩
    rw [(coverAff g hnn hM1 σ hk).supDist_eq]
    exact hd

end Cubes

/-- **The local set `V(X, J)` under the lattice symmetry.** -/
theorem locSetXJ_aff (σ : LatTorusSym S n M K) {H H' : RegionHistory S n R k0 K}
    (hI : RegionIso σ H H') {k : ℕ} (hk : k + 1 ≤ K) (r r' : ℕ) (X : Finset (Torus S.d (n k)))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {G₀ : GeneratingSet S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) (minSep S.L g.M1)}
    (hJ : ∀ P ∈ J, P ∈ cubeIdx G₀) :
    locSetXJ g hM1 H' r r' (X.map (σ.ec k).toEmbedding) (J.map (DecEquiv.affCentres (m₁ := m₁)
        (coverAff g hnn hM1 σ hk) m₁).toEmbedding) =
      (coverAff g hnn hM1 σ hk).toEquiv '' locSetXJ g hM1 H r r' X J := by
  ext x'
  obtain ⟨x, rfl⟩ := (coverAff g hnn hM1 σ hk).toEquiv.surjective x'
  rw [Set.mem_image_equiv]
  simp only [Equiv.symm_apply_apply]
  unfold locSetXJ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y', hy' | ⟨P', hP', hyP'⟩, hd⟩
    · obtain ⟨y, rfl⟩ := (coverAff g hnn hM1 σ hk).toEquiv.surjective y'
      refine ⟨y, Or.inl ?_, ?_⟩
      · exact (mem_collarCoreC_aff g hnn hM1 σ hI hk r X y).1 hy'
      · rw [← (coverAff g hnn hM1 σ hk).supDist_eq]; exact hd
    · obtain ⟨y, rfl⟩ := (coverAff g hnn hM1 σ hk).toEquiv.surjective y'
      obtain ⟨P, hP, rfl⟩ := Finset.mem_map.1 hP'
      refine ⟨y, Or.inr ⟨P, hP, ?_⟩, ?_⟩
      · exact (cubeP_aff (coverAff g hnn hM1 σ hk) (coverAff_aligned g hnn hM1 σ hk) (hJ P hP) y).1 hyP'
      · rw [← (coverAff g hnn hM1 σ hk).supDist_eq]; exact hd
  · rintro ⟨y, hy | ⟨P, hP, hyP⟩, hd⟩
    · refine ⟨(coverAff g hnn hM1 σ hk).toFun y, Or.inl ?_, ?_⟩
      · exact (mem_collarCoreC_aff g hnn hM1 σ hI hk r X y).2 hy
      · show supDist ((coverAff g hnn hM1 σ hk).toFun x) ((coverAff g hnn hM1 σ hk).toFun y) ≤ r'
        rw [(coverAff g hnn hM1 σ hk).supDist_eq]; exact hd
    · refine ⟨(coverAff g hnn hM1 σ hk).toFun y, Or.inr ⟨_, Finset.mem_map_of_mem _ hP, ?_⟩, ?_⟩
      · exact (cubeP_aff (coverAff g hnn hM1 σ hk) (coverAff_aligned g hnn hM1 σ hk) (hJ P hP) y).2 hyP
      · show supDist ((coverAff g hnn hM1 σ hk).toFun x) ((coverAff g hnn hM1 σ hk).toFun y) ≤ r'
        rw [(coverAff g hnn hM1 σ hk).supDist_eq]; exact hd

theorem cubeOfC_eq_of_unitBlock {k : ℕ} (x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))
    (h : unitBlock x = unitBlock y) : cubeOfC hM1 x = cubeOfC hM1 y := by
  have h1 := (unitBlock_eq_iff x y).1 h
  unfold cubeOfC
  refine blockMap_eq_of_sameCell (a := S.L ^ k) ?_ ?_
  · intro μ
    have e := LargeField.torusCast_val (d := S.d) (congrArg (· * S.L ^ (k + 1))
      (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm
    change ((LargeField.torusCast _ x : Torus S.d _) μ).val / S.L ^ k =
      ((LargeField.torusCast _ y : Torus S.d _) μ).val / S.L ^ k
    rw [e x μ, e y μ]
    exact h1 μ
  · exact ⟨S.L * (g.c * g.M1), by ring⟩

theorem mem_thick_singleton_aff {d ℓ : ℕ} [NeZero ℓ] (A : AffIso d ℓ) (r : ℕ) (c y : Torus d ℓ) :
    A.toFun y ∈ thick r ({A.toFun c} : Set (Torus d ℓ)) ↔ y ∈ thick r ({c} : Set (Torus d ℓ)) := by
  have h := AffIso.image_thick A r ({c} : Set (Torus d ℓ))
  rw [Set.image_singleton] at h
  rw [← h]
  exact A.toFun_injective.mem_set_image

/-- **The localization domains of the unit points under the lattice symmetry.** -/
theorem locDomsLF_aff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    {St St' : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1)}
    (H0 : StepAff St St' (coverAff g hnn hM1 σ hk)) (ρ : ℕ) (b : St.U)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (coverAff g hnn hM1 σ hk).toFun x ∈ locDomsLF g hM1 St' ρ (H0.u b) ↔
      x ∈ locDomsLF g hM1 St ρ b := by
  unfold locDomsLF
  rw [Finset.mem_filter, Finset.mem_filter, mem_locDomC, mem_locDomC]
  have hu : cubeOfC hM1 (unitRep (H0.u b)) =
      cubeOfC hM1 ((coverAff g hnn hM1 σ hk).toFun (unitRep b)) := by
    refine cubeOfC_eq_of_unitBlock g hM1 _ _ ?_
    rw [unitBlock_unitRep]
    exact ((H0.u_spec b (unitRep b)).2 (unitBlock_unitRep b)).symm
  rw [hu, cubeOfC_aff g hnn hM1 σ hk, cubeOfC_aff g hnn hM1 σ hk]
  refine and_congr (mem_thick_singleton_aff _ ρ _ _) ?_
  constructor
  · intro h z hz
    have hz' : supDist ((coverAff g hnn hM1 σ hk).toFun x) ((coverAff g hnn hM1 σ hk).toFun z) ≤
        4 * S.L ^ (k + 1 + m₁) := by
      rw [(coverAff g hnn hM1 σ hk).supDist_eq]; exact hz
    exact (H0.hΩ' 1 z).1 (h _ hz')
  · intro h z' hz'
    obtain ⟨z, rfl⟩ := (coverAff g hnn hM1 σ hk).toEquiv.surjective z'
    have hz : supDist x z ≤ 4 * S.L ^ (k + 1 + m₁) := by
      rw [← (coverAff g hnn hM1 σ hk).supDist_eq]; exact hz'
    exact (H0.hΩ' 1 z).2 (h z hz)

theorem unitOfBlock_coverBlk {k : ℕ} (hk : k + 1 ≤ K)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    unitOfBlock g hnn hM1 hk (coverBlk g hnn hM1 hk k (Nat.le_succ k) x) = unitBlock x := by
  unfold unitOfBlock coverBlk
  rw [torusCast_cancel']
  rfl

theorem exists_coverBlk_eq {k : ℕ} (hk : k + 1 ≤ K) (z : BlockAt S n M K k) :
    ∃ x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1),
      coverBlk g hnn hM1 hk k (Nat.le_succ k) x = z := by
  obtain ⟨x, hx⟩ := unitBlock_surj (d := S.d) (L := S.L) (N₁ := g.c * n (k + 1)) (m₁ := m₁)
    (k := k) (unitOfBlock g hnn hM1 hk z)
  refine ⟨x, ?_⟩
  unfold coverBlk
  have : jBlock S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) k x = unitOfBlock g hnn hM1 hk z := hx
  rw [this]
  unfold unitOfBlock
  exact torusCast_cancel _ _

theorem mem_unitPts_iff_layer {ϱ₀ : ℝ} {k : ℕ}
    (G : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ₀)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    unitBlock x ∈ unitPts G ↔ x ∈ G.layer (k + 1) := by
  rw [mem_unitPts]
  constructor
  · rintro ⟨x', hx', h⟩
    exact layer_of_unitBlock G h hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **The composed multiscale field is carried by the lattice symmetry.** -/
theorem composedMulti_symM (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    {St St' : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1)}
    (H0 : StepAff St St' (coverAff g hnn hM1 σ hk)) (ψ : MultiFieldC S n M K N)
    (c : St.U → Fin N → ℂ) :
    composedMulti g hnn hM1 hk St'.G' (symM σ ψ) (fun b' i => c (H0.u.symm b') i) =
      symM σ (composedMulti g hnn hM1 hk St.G' ψ c) := by
  classical
  funext j y
  show composedMulti g hnn hM1 hk St'.G' (symM σ ψ) _ j y =
    composedMulti g hnn hM1 hk St.G' ψ c j ((σ.eb j).symm y)
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · simp [composedMulti, hjk, symM]
  · obtain ⟨x, hx⟩ := exists_coverBlk_eq g hnn hM1 hk ((σ.eb j).symm y)
    have hy : y = coverBlk g hnn hM1 hk j (Nat.le_succ j) ((coverAff g hnn hM1 σ hk).toFun x) := by
      rw [coverBlk_aff, hx]; simp
    have e1 : unitOfBlock g hnn hM1 hk y = unitBlock ((coverAff g hnn hM1 σ hk).toFun x) := by
      rw [hy, unitOfBlock_coverBlk]
    have e2 : unitOfBlock g hnn hM1 hk ((σ.eb j).symm y) = unitBlock x := by
      rw [← hx, unitOfBlock_coverBlk]
    have hmem : unitBlock ((coverAff g hnn hM1 σ hk).toFun x) ∈ unitPts St'.G' ↔
        unitBlock x ∈ unitPts St.G' := by
      rw [mem_unitPts_iff_layer, mem_unitPts_iff_layer]
      have hl : ∀ (G : GeneratingSet S.d S.L ((g.c * n (j + 1)) * S.L ^ m₁) (j + 1) (minSep S.L g.M1)),
          G.layer (j + 1) = G.Ω (j + 1) := fun G => by
        unfold GeneratingSet.layer; rw [G.top, Finset.sdiff_empty]
      rw [hl, hl]
      exact H0.hΩ' (j + 1) x
    unfold composedMulti
    simp only [lt_irrefl, ↓reduceIte, dite_true]
    by_cases hm : unitBlock x ∈ unitPts St.G'
    · have hm' := hmem.2 hm
      simp only [show unitOfBlock g hnn hM1 hk y ∈ unitPts St'.G' by rw [e1]; exact hm',
        show unitOfBlock g hnn hM1 hk ((σ.eb j).symm y) ∈ unitPts St.G' by rw [e2]; exact hm,
        ↓reduceDIte]
      have := H0.u_spec ⟨unitBlock x, hm⟩ x
      have hu : (H0.u ⟨unitBlock x, hm⟩ : UnitTorus S.d S.L (g.c * n (j + 1)) m₁ j) =
          unitBlock ((coverAff g hnn hM1 σ hk).toFun x) := (this.2 rfl).symm
      have hs : H0.u.symm ⟨unitOfBlock g hnn hM1 hk y, by rw [e1]; exact hm'⟩ =
          ⟨unitOfBlock g hnn hM1 hk ((σ.eb j).symm y), by rw [e2]; exact hm⟩ := by
        rw [Equiv.symm_apply_eq]
        exact Subtype.ext (by simp only [e1, e2]; exact hu.symm)
      simp only [hs]
    · have hm' : unitBlock ((coverAff g hnn hM1 σ hk).toFun x) ∉ unitPts St'.G' :=
        fun h => hm (hmem.1 h)
      simp only [show unitOfBlock g hnn hM1 hk y ∉ unitPts St'.G' by rw [e1]; exact hm',
        show unitOfBlock g hnn hM1 hk ((σ.eb j).symm y) ∉ unitPts St.G' by rw [e2]; exact hm,
        ↓reduceDIte]
      simp [symM]
  · simp [composedMulti, not_lt.2 hjk.le, hjk.ne']

/-- **The cover cubes with the labels of `J` under the lattice symmetry.** -/
theorem locCubes_aff (σ : LatTorusSym S n M K) {k : ℕ} (hk : k + 1 ≤ K)
    {St St' : HoleStep S.d S.L (g.c * n (k + 1)) m₁ k N (minSep S.L g.M1) (minSep S.L g.M1)}
    (H0 : StepAff St St' (coverAff g hnn hM1 σ hk))
    (J : Finset (ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) :
    locCubes g (coverOf St'.G') (J.map (affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁).toEmbedding) =
      (locCubes g (coverOf St.G') J).map H0.kappa.toEmbedding := by
  classical
  ext Q'
  unfold locCubes
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro h
    obtain ⟨P, hP, hPQ⟩ := h
    have hPi : P ∈ (coverOf St.G').cubeIdx := by
      refine (cover_idx_aff _ H0.hAl H0.hca' H0.hΩ' P).1 ?_
      have : affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁ P = Q'.1 := hPQ
      rw [this]; exact Q'.2
    refine ⟨⟨P, hPi⟩, hP, Subtype.ext ?_⟩
    exact hPQ
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨Q.1, hQ, rfl⟩

/-- **The coefficient `T(X, J)` of the re-expanded old term is invariant under the lattice
symmetries of the history** (the clause `euclid` of (D7), at the level of one coefficient).  `σ`
maps the history `H` to `H'` (`RegionIso`), `X` to `X' = σ X`, the local set `V` to `σ V`, the
cubes `J` to `τ J`, and the fixed values of the fluctuation field by `ψ̂ ∘ u⁻¹`; the multiscale
fields and the source are carried by `symM`, `symG`.  Inputs: the clause `euclid` of the record at `X`
(`heuc`) and the analyticity of the interpolated old terms (`hana`, `hana'`). -/
theorem oldCoefLF_aff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (hm₁ : 2 ≤ m₁)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A A' : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ρc : ℝ) (ρ r : ℕ)
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (heuc : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ₂) (symM σ ψ₃) h (symG σ g₂) =
        rep.B A X ψ₂ ψ₃ h g₂)
    (ψout : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U → Fin N → ℂ)
    {R₀ : ℝ} (hR : 1 < R₀)
    (hana : AnalyticOnNhd ℂ ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).oldInterp
      (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
      (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
      (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
      (oldTermLF g hnn hM1 rep A X hk
        (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ψ ψ' hv gx)
      (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')) fun _ => R₀))
    (hana' : AnalyticOnNhd ℂ ((holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)).oldInterp
      (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G') ρc
      (locDomsLF g hM1 (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)) ρ)
      (collarCoreC (c := g.c) (H'.step k) hM1 r (X.map (σ.ec k).toEmbedding)) ∅
      (fun b' i => ψout ((holeStepLoc_stepAff g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI hm₁).u.symm b') i)
      (oldTermLF g hnn hM1 rep A' (X.map (σ.ec k).toEmbedding) hk
        (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
          ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G' (symM σ ψ) (symM σ ψ') hv (symG σ gx))
      (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G')) fun _ => R₀))
    (J₀ : Finset (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G').cubeIdx) :
    oldCoefLF g hnn hM1 (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)) H' hk
      (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G') ρc ρ r ∅
      (fun b' i => ψout ((holeStepLoc_stepAff g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI hm₁).u.symm b') i)
      rep A' (X.map (σ.ec k).toEmbedding) (symM σ ψ) (symM σ ψ') hv (symG σ gx)
      (J₀.map (holeStepLoc_stepAff g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI hm₁).kappa.toEmbedding)
      (fun b => absurd b.2 (Finset.notMem_empty _)) =
    oldCoefLF g hnn hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) H hk
      (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc ρ r ∅ ψout
      rep A X ψ ψ' hv gx J₀ (fun b => absurd b.2 (Finset.notMem_empty _)) := by
  set H0 := holeStepLoc_stepAff g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI hm₁ with hH0
  unfold oldCoefLF
  refine H0.oldCoef_entry ρc
    (fun x => mem_collarCoreC_aff g hnn hM1 σ hI hk r X x)
    (fun b x => locDomsLF_aff g hnn hM1 σ hk H0 ρ b x)
    (fun q i => by simp) (B := oldTermLF g hnn hM1 rep A X hk
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ψ ψ' hv gx)
    (B' := oldTermLF g hnn hM1 rep A' (X.map (σ.ec k).toEmbedding) hk
      (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)).G' (symM σ ψ) (symM σ ψ') hv (symG σ gx))
    (fun c => ?_) _ _ hR hana hana' J₀
  unfold oldTermLF
  rw [composedMulti_symM g hnn hM1 σ hk H0 ψ c]
  exact heuc _ _ _ _

/-- **`oldCoefLF_aff` with the local set and the fixed values given by value-level relations**: the
local set `V''` of the image step is the image of `V`, the fixed values and the cube families are
related through the coarsening of the isometry on the unit points and the action `τ` on the centres.
This is the form in which the coefficient on the local pair `oldCoefLoc` is compared. -/
theorem oldCoefLF_aff' (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (hm₁ : 2 ≤ m₁)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts}
    (rep : Rep S n R k0 K M N geo cs P k) (A A' : LabHist S n R k0 K)
    (X : Finset (Torus S.d (n k))) (ρc : ℝ) (ρ r : ℕ)
    (ψ' : MultiFieldC S n M K N) (hv : EuclideanSpace ℝ (Fin N)) (gx : GIdx S n M K N → ℂ)
    (V V'' : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (hV'' : V'' = (coverAff g hnn hM1 σ hk).toEquiv '' V)
    (heuc : ∀ (ψ₂ ψ₃ : MultiFieldC S n M K N) (h : Fin N → ℂ) (g₂ : GIdx S n M K N → ℂ),
      rep.B A' (X.map (σ.ec k).toEmbedding) (symM σ ψ₂) (symM σ ψ₃) h (symG σ g₂) =
        rep.B A X ψ₂ ψ₃ h g₂)
    (ψout : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U → Fin N → ℂ)
    (ψout' : (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').U →
      Fin N → ℂ)
    (hψ : ∀ (b : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U)
      (b' : (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').U),
      (b' : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) =
        ((coverAff g hnn hM1 σ hk).coarse (S.L ^ k)
          ((g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1 - k))).toFun
          (b : UnitTorus S.d S.L (g.c * n (k + 1)) m₁ k) → ∀ i, ψout' b' i = ψout b i)
    {R₀ : ℝ} (hR : 1 < R₀)
    (J₀ : Finset (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G').cubeIdx)
    (J₀' : Finset (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
      V'').G').cubeIdx)
    (hJ : ∀ Q', Q' ∈ J₀' ↔ ∃ Q ∈ J₀, (Q' : ℕ × CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) =
      DecEquiv.affCentres (m₁ := m₁) (coverAff g hnn hM1 σ hk) m₁ (Q : ℕ × CTorus S.d S.L
        (g.c * n (k + 1)) m₁ (k + 1)))
    (hana : AnalyticOnNhd ℂ ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).oldInterp
      (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
      (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
      (collarCoreC (c := g.c) (H.step k) hM1 r X) ∅ ψout
      (oldTermLF g hnn hM1 rep A X hk
        (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ψ ψ' hv gx)
      (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')) fun _ => R₀))
    (hana' : AnalyticOnNhd ℂ ((holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').oldInterp
      (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').G') ρc
      (locDomsLF g hM1 (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'') ρ)
      (collarCoreC (c := g.c) (H'.step k) hM1 r (X.map (σ.ec k).toEmbedding)) ∅ ψout'
      (oldTermLF g hnn hM1 rep A' (X.map (σ.ec k).toEmbedding) hk
        (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').G' (symM σ ψ)
        (symM σ ψ') hv (symG σ gx))
      (fun b => absurd b.2 (Finset.notMem_empty _)))
      (Analysis.polydisc (0 : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').G')) fun _ => R₀)) :
    oldCoefLF g hnn hM1 (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'') H' hk
      (coverOf (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ V'').G') ρc ρ r ∅
      ψout' rep A' (X.map (σ.ec k).toEmbedding) (symM σ ψ) (symM σ ψ') hv (symG σ gx) J₀'
      (fun b => absurd b.2 (Finset.notMem_empty _)) =
    oldCoefLF g hnn hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) H hk
      (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc ρ r ∅ ψout
      rep A X ψ ψ' hv gx J₀ (fun b => absurd b.2 (Finset.notMem_empty _)) := by
  subst hV''
  set H0 := holeStepLoc_stepAff g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI hm₁ with hH0
  have hψ' : ψout' = fun b' i => ψout (H0.u.symm b') i := by
    funext b' i
    obtain ⟨b, rfl⟩ := H0.u.surjective b'
    rw [Equiv.symm_apply_apply]
    exact hψ b (H0.u b) (H0.u_val b) i
  have hJ' : J₀' = J₀.map H0.kappa.toEmbedding := by
    ext Q'
    rw [hJ, Finset.mem_map]
    constructor
    · rintro ⟨Q, hQ, h⟩
      exact ⟨Q, hQ, Subtype.ext h.symm⟩
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q, hQ, rfl⟩
  subst hψ' hJ'
  exact oldCoefLF_aff g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ σ hI hm₁ rep A A' X ρc ρ r ψ' hv
    gx V heuc ψout hR hana hana' J₀

end Balaban.RootFSpine
