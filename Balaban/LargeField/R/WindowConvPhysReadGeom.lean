/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireLayers
public import Balaban.LargeField.R.WindowRegion

/-!
# Neighbours of the region of a piece lie in the first domain of the local family

The local background of a piece `Z'` of the step `k → k + 1` reads, through the crossing bonds of
`X_{Z'}`, the field at the neighbours of the sites of `X_{Z'}` (P6 p. 11 after (2.25)).  The
neighbours of a site of `X_{Z'}` lie in `Ω_k` of `G^{Z'}_{k+1}`: their `π_{k+1}`-cube is within
distance one of `Z'`, and their `π_k`-cube is within distance one of the complement of `Z_k`.  So
all bond reads of the local action at `X_{Z'}` are reads of the background field, never of the
collar datum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.Background RegionHistory

set_option linter.unusedSectionVars false

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)

/-- A site adjacent to a site of `X_{Z'}` lies in `Ω_k` of the local family `G^{Z'}_{k+1}`. -/
theorem locGen_adj_mem_Ω_k (hk1 : 1 ≤ k) {x y : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))}
    (hx : x ∈ Xfine g Hl k Zc) (hadj : Adj x y) : y ∈ (locGen g Hl k Zc hZc hk).Ω k := by
  have hxy : supDist y x ≤ 1 := by
    have h2 := supDist_le_torusDist y x
    have h3 := Multiscale.Adj.torusDist_le hadj.symm
    have : (supDist y x : ℝ) ≤ 1 := h2.trans h3
    exact_mod_cast this
  have hPpos : ∀ q : ℕ, 0 < S.L ^ q * (g.c * g.M1) := fun q => Nat.pos_of_ne_zero (by
    have := NeZero.ne S.L; have := NeZero.ne g.M1; have := NeZero.ne g.c; positivity)
  have hyU : y ∈ stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1)))) := by
    have h := (Xfine_mem g Hl k Zc hx).1
    unfold stepU
    rw [mem_fineK1]
    refine mem_nbhd.2 ⟨_, h, ?_⟩
    have := supDist_blockMap_le_one (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L)
      (q := k + 1) (P := S.L ^ (k + 1) * (g.c * g.M1)) (m' := n (k + 1)) (by ring)
      (D := 1) (hPpos (k + 1)) y x hxy
    omega
  have hyW : y ∈ stepWLoc g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ ⌊R k⌋₊ (Hl.step k).Z
      (Zc : Set (Torus S.d (n (k + 1)))) := by
    have h := (Xfine_mem g Hl k Zc hx).2
    unfold stepWLoc stepW
    refine Finset.mem_inter.2 ⟨?_, hyU⟩
    rw [mem_fineK, thick2_eq]
    refine mem_nbhd.2 ⟨_, h, ?_⟩
    have := supDist_blockMap_le_one (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L)
      (q := k + 1) (P := S.L ^ k * (g.c * g.M1)) (m' := n k)
      (by rw [Hl.F.hnn k (by omega)]; ring) (D := 1) (hPpos k) y x hxy
    omega
  by_cases hOm : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) y ∈ (Hl.step k).Omega
  · have htop : y ∈ (locGen g Hl k Zc hZc hk).Ω (k + 1) := by
      unfold Balaban.LargeField.locGen genBoundaryLocal
      rw [boundaryGenSet_Ω]
      unfold boundaryLayer
      have hU : IsCubeUnion g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1)
          (stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))) :=
        isCubeUnion_fineK1 _
      rw [minLayer_of_gt _ (Nat.lt_succ_self k), minLayer_self, hU.cubeInterior_eq]
      simp only [Finset.empty_sdiff, Finset.empty_union, Finset.mem_inter, mem_fineK1]
      exact ⟨hyU, hOm⟩
    exact (locGen g Hl k Zc hZc hk).Ω_antitone hk1 (Nat.le_succ k) (by omega) htop
  · unfold Balaban.LargeField.locGen genBoundaryLocal
    rw [boundaryGenSet_Ω]
    unfold boundaryLayer
    have hW : IsCubeUnion g.M1 (g.c * n (k + 1)) S.L (k + 1) k
        (stepWLoc g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ ⌊R k⌋₊ (Hl.step k).Z
          (Zc : Set (Torus S.d (n (k + 1))))) :=
      isCubeUnion_stepWLoc (Hl.F.hnn k (by omega)) _ _ _ _
    rw [minLayer_self, hW.cubeInterior_eq]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hyW, by rw [mem_fineK1]; exact hOm⟩)

/-- The neighbours `x ± e_μ` of a site of `X_{Z'}` lie in `Ω₁` of the local family. -/
theorem locGen_nbr_mem_Ω_one (hk1 : 1 ≤ k)
    {x : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))}
    (hx : x ∈ Xfine g Hl k Zc) (μ : Fin S.d) :
    x + Pi.single μ 1 ∈ (locGen g Hl k Zc hZc hk).Ω 1 ∧
      x - Pi.single μ 1 ∈ (locGen g Hl k Zc hZc hk).Ω 1 := by
  refine ⟨(locGen g Hl k Zc hZc hk).Ω_antitone le_rfl hk1 (by omega)
      (locGen_adj_mem_Ω_k g Hl k Zc hZc hk hk1 hx ⟨μ, Or.inl rfl⟩),
    (locGen g Hl k Zc hZc hk).Ω_antitone le_rfl hk1 (by omega)
      (locGen_adj_mem_Ω_k g Hl k Zc hZc hk hk1 hx ⟨μ, Or.inr (by simp)⟩)⟩

end Step

end Balaban.Fluctuation
