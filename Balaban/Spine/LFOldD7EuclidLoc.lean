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

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
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
theorem holeStepLoc_D'_aff_Ψ (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (hρ' : 2 ≤ m₁)
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
    rw [if_pos hx, if_pos h2]
    unfold mixedLift
    by_cases hΩ : x ∈ ((holeStepLF g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ).G'.inter
        (locB g hM1 V)).Ω (k + 1)
    · rw [if_pos hΩ, if_pos (hΩt.2 hΩ)]
      have := blockLift_coverField_symM g hnn hM1 σ hk (k + 1) le_rfl (scaleMulti z ψ) x
      exact congrFun this i
    · rw [if_neg hΩ, if_neg (fun h => hΩ (hΩt.1 h))]
      have := blockLift_coverField_symM g hnn hM1 σ hk k (Nat.le_succ k) ψ x
      exact congrFun this i
  · have h2 : (coverAff g hnn hM1 σ hk).toFun x ∉
        dataSites ((holeStepLF g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ).G'.inter
          (locB g hM1 ((coverAff g hnn hM1 σ hk).toEquiv '' V))) := fun h => hx (hdata.1 h)
    rw [if_neg hx, if_neg h2]

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
  · rw [if_pos hx, if_pos (hΩ1.2 hx)]
  · rw [if_neg hx, if_neg (fun h => hx (hΩ1.1 h))]

/-- **The local steps of two histories related by a lattice symmetry are related by `StepAff`.** -/
theorem holeStepLoc_stepAff (σ : LatTorusSym S n M K) (hI : RegionIso σ H H') (hm₁ : 2 ≤ m₁) :
    StepAff (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V)
      (holeStepLoc g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ
        ((coverAff g hnn hM1 σ hk).toEquiv '' V)) (coverAff g hnn hM1 σ hk) where
  hAl := coverAff_aligned g hnn hM1 σ hk
  hΩ := holeStepLoc_G_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI
  hΩ' := holeStepLoc_G'_aff g hnn hM1 H H' hk hk1 hρ ψ (symM σ ψ) z h₀ a₁ ν β p₁ δ V σ hI
  hca := holeStepLoc_cubeAligned g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V hm₁
  hca' := holeStepLoc_cubeAligned g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _ hm₁
  hΨ := holeStepLoc_D'_aff_Ψ g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI hm₁
  hh := holeStepLoc_D'_aff_h g hnn hM1 H H' hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V σ hI
  ha₁ := (holeStepLoc_consts g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _).2.1.trans
    (holeStepLoc_consts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).2.1.symm
  hν := (holeStepLoc_consts g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _).2.2.1.trans
    (holeStepLoc_consts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).2.2.1.symm
  hβ := (holeStepLoc_consts g hnn hM1 H' hk hk1 hρ (symM σ ψ) z h₀ a₁ ν β p₁ δ _).2.2.2.1.trans
    (holeStepLoc_consts g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).2.2.2.1.symm

end LocStep

end Balaban.RootFSpine
