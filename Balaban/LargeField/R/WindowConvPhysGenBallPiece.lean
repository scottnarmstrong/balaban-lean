/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireLayers
public import Balaban.Fluctuation.Theorem42WireGeom
public import Balaban.LargeField.R.WindowConvPhysGenBallHist

/-!
# Layers of the local family `G^{Z'}_{k+1}` near a site of `X_{Z'}`

A site `y` whose `π_{k+1}`-cube is within `⌊R_k⌋` of `Z'` and whose `π_k`-cube is within
`2(⌊R_{k-1}⌋ + 1)` of the `π_k`-cube of a site of `X_{Z'}` lies in `Ω_n(G^{Z'}_{k+1})` for all
`n ≤ k`; and it lies in `Ω_{k+1}` exactly when its `π_{k+1}`-cube lies in `Ω_{k+1}` of the step.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.Background RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)

/-- Layers `n ≤ k` of the local family on the ball around a site of `X_{Z'}`. -/
theorem locGen_Ω_of_near {y}
    (hyU : y ∈ stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1)))))
    (hyW : blockMap (S.L ^ k * (g.c * g.M1)) (n k) y ∈
      nbhd (2 * (⌊R (k - 1)⌋₊ + 1)) ((Hl.step k).Z)ᶜ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) :
    y ∈ (locGen g Hl k Zc hZc hk).Ω m := by
  by_cases hOm : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) y ∈ (Hl.step k).Omega
  · exact (locGen g Hl k Zc hZc hk).Ω_antitone hm1 (by omega) (by omega)
      ((locGen_Ω_top_iff' g Hl k Zc hZc hk).2 ⟨hyU, hOm⟩)
  · have hW : y ∈ stepWLoc g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ ⌊R k⌋₊ (Hl.step k).Z
        (Zc : Set (Torus S.d (n (k + 1)))) := by
      unfold stepWLoc stepW
      refine Finset.mem_inter.2 ⟨?_, hyU⟩
      rw [mem_fineK, thick2_eq]
      exact hyW
    have hWu : IsCubeUnion g.M1 (g.c * n (k + 1)) S.L (k + 1) k
        (stepWLoc g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ ⌊R k⌋₊ (Hl.step k).Z
          (Zc : Set (Torus S.d (n (k + 1))))) :=
      isCubeUnion_stepWLoc (Hl.F.hnn k (by omega)) _ _ _ _
    unfold Balaban.LargeField.locGen genBoundaryLocal
    rw [boundaryGenSet_Ω]
    unfold boundaryLayer
    exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hWu.subset_minLayer hmk hW, by
      rw [mem_fineK1]; exact hOm⟩)

end Balaban.Fluctuation
