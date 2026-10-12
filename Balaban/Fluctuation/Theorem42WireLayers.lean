/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeActionReal
public import Balaban.LargeField.Background.StepGenSetsFlow
import Balaban.LargeField.Region.SymmLat

/-!
# The layers of `𝔹_{k+1}` and of the local family on `X_{Z'}` (LFR Definition II.5.4)

`mainActionLoc` pairs the multiscale action `A_{𝔹_{k+1}}(X_{Z'}; ψ, φ)` of the history's
generating set `histGenLevel` with the local background `locPhi` built on the generating set
`locGen = G^{Z'}_{k+1}`.  The two generating sets are different families on the level-`(k+1)` torus,
but on `X_{Z'} = Z^c_k ∩ Z'` (for `k ≥ 1`) they have the same layers:

* `Xfine_mem_U`, `Xfine_mem_W`: `X_{Z'}` lies in the fine sets `U_{Z'}` and `W_k ∩ U_{Z'}`;
* `locGen_Ω_top_iff`, `locGen_Ω_k`, `histGenLevel_top_iff`, `histGenLevel_k`: every site of `X_{Z'}`
  lies in `Ω_k` of both families, and lies in `Ω_{k+1}` iff its `π_{k+1}`-cube lies in
  `Ω_{k+1}` (the output domain of the step);
* `layer_hist_iff_loc`: the layers `Λ_j` of the two families agree on `X_{Z'}`;
* `actionG_histGenLevel_eq_locGen`: `A_{𝔹_{k+1}}(X_{Z'}; ψ, φ) = A_{G^{Z'}_{k+1}}(X_{Z'}; ψ, φ)`.

For `k = 0` the site set `X_{Z'} = Z'` is not contained in `Ω_1` (the layer `Λ_0 = Ω_1^c ∩ X` of
Definition II.5.4 is read at the spin field), so the identification with the cube action, which
lives on `Ω_1`, is stated for `k ≥ 1` only.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.Background RegionHistory

set_option linter.unusedSectionVars false
section Gen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem layer_mem_iff_of_top (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {x : Torus d (N₀ * L ^ (k + 1))} (hxk : x ∈ G.Ω k) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) :
    x ∈ G.layer j ↔ (j = k ∧ x ∉ G.Ω (k + 1)) ∨ (j = k + 1 ∧ x ∈ G.Ω (k + 1)) := by
  rw [GeneratingSet.mem_layer]
  rcases Nat.lt_or_ge j k with hlt | hge
  · have : x ∈ G.Ω (j + 1) := G.Ω_antitone (by omega : 1 ≤ j + 1) (by omega : j + 1 ≤ k) (by omega) hxk
    constructor
    · intro h; exact absurd this h.2
    · rintro (h | h) <;> omega
  · rcases Nat.eq_or_lt_of_le hge with heq | hgt
    · subst heq
      simp [hxk]
    · have hj : j = k + 1 := by omega
      subst hj
      have : x ∉ G.Ω (k + 1 + 1) := by rw [G.top]; exact Finset.notMem_empty _
      simp [this]

end Gen

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)

theorem Xfine_mem {x} (hx : x ∈ Xfine g Hl k Zc) :
    blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ (Zc : Set (Torus S.d (n (k + 1)))) ∧
    blockMap (S.L ^ k * (g.c * g.M1)) (n k) x ∉ (Hl.step k).Z := by
  classical
  unfold Xfine at hx
  rw [Finset.mem_sdiff, mem_fineK1, mem_fineK] at hx
  exact hx


theorem Xfine_mem_U {x} (hx : x ∈ Xfine g Hl k Zc) :
    x ∈ stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1)))) := by
  have h := (Xfine_mem g Hl k Zc hx).1
  unfold stepU
  rw [mem_fineK1]
  exact subset_nbhd _ _ h

theorem Xfine_mem_W {x} (hx : x ∈ Xfine g Hl k Zc) :
    x ∈ stepWLoc g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ ⌊R k⌋₊ (Hl.step k).Z
      (Zc : Set (Torus S.d (n (k + 1)))) := by
  have h := (Xfine_mem g Hl k Zc hx).2
  unfold stepWLoc stepW
  refine Finset.mem_inter.2 ⟨?_, Xfine_mem_U g Hl k Zc hx⟩
  rw [mem_fineK]
  exact subset_nbhd _ _ (subset_nbhd _ _ h)


theorem locGen_Ω_top_iff {x} (hx : x ∈ Xfine g Hl k Zc) :
    x ∈ (locGen g Hl k Zc hZc hk).Ω (k + 1) ↔
      blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ (Hl.step k).Omega := by
  unfold locGen genBoundaryLocal
  rw [boundaryGenSet_Ω]
  unfold boundaryLayer
  have hU : IsCubeUnion g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1)
      (stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))) :=
    isCubeUnion_fineK1 _
  rw [minLayer_of_gt _ (Nat.lt_succ_self k), minLayer_self, hU.cubeInterior_eq]
  simp only [Finset.empty_sdiff, Finset.empty_union, Finset.mem_inter, mem_fineK1]
  exact ⟨fun h => h.2, fun h => ⟨Xfine_mem_U g Hl k Zc hx, h⟩⟩


theorem locGen_Ω_k {x} (hk1 : 1 ≤ k) (hx : x ∈ Xfine g Hl k Zc) :
    x ∈ (locGen g Hl k Zc hZc hk).Ω k := by
  by_cases hOm : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ (Hl.step k).Omega
  · exact (locGen g Hl k Zc hZc hk).Ω_antitone hk1 (Nat.le_succ k) (by omega)
      ((locGen_Ω_top_iff g Hl k Zc hZc hk hx).2 hOm)
  · unfold locGen genBoundaryLocal
    rw [boundaryGenSet_Ω]
    unfold boundaryLayer
    have hW : IsCubeUnion g.M1 (g.c * n (k + 1)) S.L (k + 1) k
        (stepWLoc g.M1 g.c (n (k + 1)) S.L k ⌊R (k - 1)⌋₊ ⌊R k⌋₊ (Hl.step k).Z
          (Zc : Set (Torus S.d (n (k + 1))))) :=
      isCubeUnion_stepWLoc (Hl.F.hnn k (by omega)) _ _ _ _
    rw [minLayer_self, hW.cubeInterior_eq]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨Xfine_mem_W g Hl k Zc hx, by
      rw [mem_fineK1]; exact hOm⟩)


variable (hrem : ∀ j, Hl.rem j = ∅)

theorem histGenLevel_mem_iff (j : ℕ) (x : Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1)) :
    x ∈ (histGenLevel g Hl k hk hrem).Ω j ↔ j ≤ k + 1 ∧
      blockMap (S.L ^ j * (g.c * g.M1)) (n j) x ∈ (Hl.toSeq hk hrem).OmegaAt j := by
  unfold histGenLevel
  rw [mem_castGen, RegionHistory.mem_histGen]
  rw [← g.hM]
  unfold cubeMap
  rw [torusCast_blockMap]


theorem histGenLevel_top_iff (x : Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1)) :
    x ∈ (histGenLevel g Hl k hk hrem).Ω (k + 1) ↔
      blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ (Hl.step k).Omega := by
  rw [histGenLevel_mem_iff]
  simp only [le_refl, true_and]
  rfl

theorem histGenLevel_k {x} (hk1 : 1 ≤ k) (hx : x ∈ Xfine g Hl k Zc) :
    x ∈ (histGenLevel g Hl k hk hrem).Ω k := by
  rw [histGenLevel_mem_iff]
  refine ⟨by omega, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  by_contra hc
  have h := (Xfine_mem g Hl k Zc hx).2
  subst hi
  exact h ((Hl.toSeq hk hrem).OmegaAt_compl_subset_Z i hc)


theorem layer_hist_iff_loc (hk1 : 1 ≤ k) {x} (hx : x ∈ Xfine g Hl k Zc) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k + 1) :
    x ∈ (histGenLevel g Hl k hk hrem).layer j ↔ x ∈ (locGen g Hl k Zc hZc hk).layer j := by
  rw [layer_mem_iff_of_top _ (histGenLevel_k g Hl k Zc hk hrem hk1 hx) hj1 hjk,
    layer_mem_iff_of_top _ (locGen_Ω_k g Hl k Zc hZc hk hk1 hx) hj1 hjk,
    histGenLevel_top_iff, locGen_Ω_top_iff g Hl k Zc hZc hk hx]

/-- **The layers of `𝔹_{k+1}` and `G^{Z'}_{k+1}` agree on `X_{Z'}`**, hence the multiscale
actions of `X_{Z'}` for the two generating sets coincide. -/
theorem actionG_histGenLevel_eq_locGen (hk1 : 1 ≤ k) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a : ℕ → ℝ) (μ : ℝ) (h : E)
    (ψ : (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) m → E)
    (φ : Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) → E) :
    actionG (histGenLevel g Hl k hk hrem) a μ h (Xfine g Hl k Zc) ψ φ =
      actionG (locGen g Hl k Zc hZc hk) a μ h (Xfine g Hl k Zc) ψ φ := by
  unfold actionG
  congr 3
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  have : lam (histGenLevel g Hl k hk hrem) j ∩ Xfine g Hl k Zc =
      lam (locGen g Hl k Zc hZc hk) j ∩ Xfine g Hl k Zc := by
    ext x
    simp only [lam, show j ≠ 0 by omega, ↓reduceIte, Finset.mem_inter]
    exact and_congr_left fun hx => layer_hist_iff_loc g Hl k Zc hZc hk hrem hk1 hx hj1 hjk
  rw [this]

end Step

end Balaban.Fluctuation
