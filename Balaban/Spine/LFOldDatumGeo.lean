/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldDatumFree
public import Balaban.Background.DataPatchScaled
public import Balaban.LargeField.History.H7Holes
public import Balaban.LargeField.History.BondLiftY
public import Balaban.LargeField.R.WindowLiftDatum
public import Balaban.LargeField.Region.SymmLevel

/-!
# Geometry of the data sites of the local pair and of the cube tests (target (3) of W1154d)

The datum of the local pair `G′_V` of reading HS-2 is patched from the splits of the cube tests of
the target H7 domain of scale `k + 1` (`Δ^c_{k+1}(□)`, `Δ'^c_{k+1}(□)`), each read at the cube `□` of
`𝕋_{k+1}` of a data site.  This file gives the geometric facts of the patching.

* `toCube`, `cubeOfC_eq_toCube`, `cubeKOfC_eq_toCube`, `torusCast_toCube`, `jBlock_toCube`,
  `jBlock_toCube_eq`, `adj_castSide`, `adj_toCube`: the cast of the cover torus to the torus of the cube
  tests, compatible with blocks, cubes, adjacency and the history torus;
* `cubeOfC_eq_of_jBlock`, `cubeKOfC_eq_of_jBlock`: a `j`-block lies in one cube;
* `cubeOfC_mem_of_top_locG'`, `layerIndex_locG'_le`, `jBlock_of_mem_blockSet`,
  `cubeOfC_near_of_pair`, `toCube_mem_blk_of_blockSet`, `toCube_mem_blk`: the layers, blocks and
  interface pairs of `G′_V` (an interface pair lies over cubes within one cube);
* `genCube_site_spec`, `genCubeMixed_site_spec`: a site over a cube within two cubes of the centre of a
  cube test is a data site of its generating set, in the top layer (single test) or in the layer
  `k + 1` / `k` according as it lies in `Ω` (mixed test);
* `cubeSub_fineSet_iff`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

set_option linter.unusedSectionVars false

section Geo

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- The site of the cube torus of scale `k + 1` (the torus of the cube tests `G_{k+1}(□)`) of a site
of the cover torus. -/
def toCube {k : ℕ} (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)) :=
  LargeField.torusCast (congrArg (· * S.L ^ (k + 1)) (p6_side (c := g.c) (n1 := n (k + 1)) hM1)).symm x

theorem cubeOfC_eq_toCube {k : ℕ} (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x =
      blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) (toCube g hM1 x) := rfl

theorem cubeKOfC_eq_toCube {k : ℕ} (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x =
      blockMap (S.L ^ k * (g.c * g.M1)) (n k) (toCube g hM1 x) := rfl

/-- The history site of the cube-torus site of a site of the cover torus is its history site. -/
theorem torusCast_toCube {k : ℕ} (hk : k + 1 ≤ K) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    LargeField.torusCast (histScale_top g.hM hnn hk) (toCube g hM1 x) = fineOfC g hnn hM1 hk x := by
  unfold toCube fineOfC
  rw [LargeField.torusCast_torusCast_comp]

/-- **The `j`-blocks of a cover-torus site and of its cube-torus site agree** (read on the history
torus). -/
theorem jBlock_toCube {k j : ℕ} (hk : k + 1 ≤ K) (hj : j ≤ k + 1)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    LargeField.torusCast (histScale_eq g.hM hnn hj hk)
        (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) j (toCube g hM1 x)) =
      coverBlk g hnn hM1 hk j hj x := by
  rw [← jBlock_torusCast_top g.hM hnn hj hk, torusCast_toCube g hnn hM1 hk,
    jBlock_fineOfC g hnn hM1 hk j hj]

/-- Two cover-torus sites in one `j`-block have their cube-torus sites in one `j`-block. -/
theorem jBlock_toCube_eq {k j : ℕ}
    {x x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j x =
      jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j x') :
    jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) j (toCube g hM1 x) =
      jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) j (toCube g hM1 x') := by
  unfold jBlock toCube at *
  rw [LargeField.blockMap_torusCast, LargeField.blockMap_torusCast]
  have e : g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - j) =
      g.c * n (k + 1) * S.L ^ m₁ * S.L ^ (k + 1 - j) := by rw [p6_side hM1]
  have := congrArg (LargeField.torusCast e.symm) h
  rwa [LargeField.torusCast_blockMap_right, LargeField.torusCast_blockMap_right] at this

/-- Adjacency is preserved by the cast of tori along `N₀ = N₀'`. -/
theorem adj_castSide {d L N₀ N₀' k : ℕ} (h : N₀ = N₀') {x x' : Torus d (N₀ * L ^ k)} (hx : Adj x x') :
    Adj (LargeField.torusCast (congrArg (· * L ^ k) h) x : Torus d (N₀' * L ^ k))
      (LargeField.torusCast (congrArg (· * L ^ k) h) x') := by
  subst h; exact hx

theorem adj_toCube {k : ℕ} {x x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)} (h : Adj x x') :
    Adj (toCube g hM1 x) (toCube g hM1 x') :=
  adj_castSide (p6_side (c := g.c) (n1 := n (k + 1)) hM1).symm h

/-- Adjacency is preserved by the cast of tori along an equality of their sizes. -/
theorem adj_torusCast_sides {d L L' N₀ N₀' j j' : ℕ} (h : N₀ * L ^ j = N₀' * L' ^ j')
    {x x' : Torus d (N₀ * L ^ j)} (hx : Adj x x') :
    Adj (LargeField.torusCast h x : Torus d (N₀' * L' ^ j')) (LargeField.torusCast h x') := by
  obtain ⟨μ, e | e⟩ := hx
  · exact ⟨μ, Or.inl (by rw [e, LargeField.torusCast_add_single])⟩
  · exact ⟨μ, Or.inr (by rw [e, LargeField.torusCast_add_single])⟩

/-! ### The cube torus of scale `k` -/

/-- **The site of the cube torus of scale `k`** (the torus of the cube tests `G_k(□)` of `𝕋_k`) of a
site of the cover torus: both are the fine torus of the history. -/
def toCubeK {k : ℕ} (hk : k + 1 ≤ K) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    Torus S.d (g.M1 * (g.c * n k) * S.L ^ k) :=
  LargeField.torusCast
    ((coverSide g hnn hM1 hk).trans (histScale_top g.hM hnn (Nat.le_of_succ_le hk)).symm) x

/-- The history site of the cube-torus site of scale `k` of a site of the cover torus is its history
site. -/
theorem torusCast_toCubeK {k : ℕ} (hk : k + 1 ≤ K) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    LargeField.torusCast (histScale_top g.hM hnn (Nat.le_of_succ_le hk)) (toCubeK g hnn hM1 hk x) =
      fineOfC g hnn hM1 hk x := by
  unfold toCubeK fineOfC
  rw [LargeField.torusCast_torusCast_comp]

/-- The cube of `𝕋_k` of a site of the cover torus, read at its cube-torus site of scale `k`. -/
theorem cubeKOfC_eq_toCubeK {k : ℕ} (hk : k + 1 ≤ K) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x =
      blockMap (S.L ^ k * (g.c * g.M1)) (n k) (toCubeK g hnn hM1 hk x) := by
  rw [← cubeMap_fineOfC_k g hnn hM1 hk x, ← torusCast_toCubeK g hnn hM1 hk x,
    cubeMap_torusCast_top g.hM hnn (Nat.le_of_succ_le hk)]

/-- **The `j`-blocks (`j ≤ k`) of a cover-torus site and of its cube-torus site of scale `k` agree**
(read on the history torus). -/
theorem coverBlk_eq_toCubeK {k j : ℕ} (hk : k + 1 ≤ K) (hj : j ≤ k)
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    LargeField.torusCast (histScale_eq g.hM hnn hj (Nat.le_of_succ_le hk))
        (jBlock S.d S.L (g.M1 * (g.c * n k)) k j (toCubeK g hnn hM1 hk x)) =
      coverBlk g hnn hM1 hk j (hj.trans (Nat.le_succ k)) x := by
  rw [← jBlock_torusCast_top g.hM hnn hj (Nat.le_of_succ_le hk), torusCast_toCubeK g hnn hM1 hk x,
    jBlock_fineOfC g hnn hM1 hk j]

/-- Two cover-torus sites in one `j`-block (`j ≤ k`) have their cube-torus sites of scale `k` in one
`j`-block. -/
theorem jBlock_toCubeK_eq {k j : ℕ} (hk : k + 1 ≤ K) (hj : j ≤ k)
    {x x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j x =
      jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j x') :
    jBlock S.d S.L (g.M1 * (g.c * n k)) k j (toCubeK g hnn hM1 hk x) =
      jBlock S.d S.L (g.M1 * (g.c * n k)) k j (toCubeK g hnn hM1 hk x') := by
  have hb : coverBlk g hnn hM1 hk j (hj.trans (Nat.le_succ k)) x =
      coverBlk g hnn hM1 hk j (hj.trans (Nat.le_succ k)) x' := by
    unfold coverBlk; rw [h]
  rw [← coverBlk_eq_toCubeK g hnn hM1 hk hj x, ← coverBlk_eq_toCubeK g hnn hM1 hk hj x'] at hb
  have := congrArg (LargeField.torusCast (histScale_eq g.hM hnn hj (Nat.le_of_succ_le hk)).symm) hb
  rwa [LargeField.torusCast_torusCast_comp, LargeField.torusCast_torusCast_comp] at this

theorem adj_toCubeK {k : ℕ} (hk : k + 1 ≤ K) {x x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : Adj x x') : Adj (toCubeK g hnn hM1 hk x) (toCubeK g hnn hM1 hk x') :=
  adj_torusCast_sides _ h

include hnn in
/-- The cube of `𝕋_{k+1}` of a site of the cover torus is the coarse cube of its cube of `𝕋_k`. -/
theorem blockMap_cubeKOfC {k : ℕ} (hk : k + 1 ≤ K) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    blockMap S.L (n (k + 1)) (cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x) =
      cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x := by
  rw [← cubeMap_fineOfC_k g hnn hM1 hk x, ← cubeMap_fineOfC_succ g hnn hM1 hk x, cubeMap_succ hnn hk]

/-! ### The local set `G′_V` -/

include hnn in
/-- The sites of one `j`-block (`j ≤ k + 1`) of the cover torus lie in one cube of `𝕋_{k+1}`. -/
theorem cubeOfC_eq_of_jBlock {k j : ℕ} (hk : k + 1 ≤ K) (hj : j ≤ k + 1)
    {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j y =
      jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j x) :
    cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 y = cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x := by
  rw [← cubeMap_fineOfC_succ g hnn hM1 hk y, ← cubeMap_fineOfC_succ g hnn hM1 hk x]
  refine cubeMap_eq_of_jBlock_eq hj hk hnn ?_
  rw [jBlock_fineOfC g hnn hM1 hk j hj, jBlock_fineOfC g hnn hM1 hk j hj]
  unfold coverBlk
  rw [h]

include hnn in
/-- The sites of one `j`-block (`j ≤ k`) of the cover torus lie in one cube of `𝕋_k`. -/
theorem cubeKOfC_eq_of_jBlock {k j : ℕ} (hk : k + 1 ≤ K) (hj : j ≤ k)
    {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j y =
      jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) j x) :
    cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 y =
      cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x := by
  rw [← cubeMap_fineOfC_k g hnn hM1 hk y, ← cubeMap_fineOfC_k g hnn hM1 hk x]
  refine cubeMap_eq_of_jBlock_eq hj (Nat.le_of_succ_le hk) hnn ?_
  rw [jBlock_fineOfC g hnn hM1 hk j (hj.trans (Nat.le_succ k)),
    jBlock_fineOfC g hnn hM1 hk j (hj.trans (Nat.le_succ k))]
  unfold coverBlk
  rw [h]

/-- The top layer of `G′_V` lies over `Ω_{k+1}`. -/
theorem cubeOfC_mem_of_top_locG' (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hx : x ∈ (locG' g hnn hM1 H hk hρ V).Ω (k + 1)) :
    cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∈ (H.step k).Omega :=
  (mem_stepG'_top_iff g hnn hM1 H hk hρ x).1 (Finset.mem_inter.1 hx).1

/-- The layer index of `G′_V` is at most `k` off `Ω_{k+1}`. -/
theorem layerIndex_locG'_le (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    (locG' g hnn hM1 H hk hρ V).layerIndex x ≤ k + 1 ∧
      (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x ∉ (H.step k).Omega →
        (locG' g hnn hM1 H hk hρ V).layerIndex x ≤ k) := by
  by_cases h1 : x ∈ (locG' g hnn hM1 H hk hρ V).Ω 1
  · obtain ⟨-, h2, h3⟩ := (locG' g hnn hM1 H hk hρ V).layerIndex_spec h1
    refine ⟨h2, fun hΩ => ?_⟩
    by_contra hlt
    have he : (locG' g hnn hM1 H hk hρ V).layerIndex x = k + 1 := by omega
    rw [he] at h3
    exact hΩ (cubeOfC_mem_of_top_locG' g hnn hM1 H hk hρ V
      ((locG' g hnn hM1 H hk hρ V).mem_layer.1 h3).1)
  · rw [layerIndex_of_not_mem _ h1]
    exact ⟨Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- A site of the block of a site of `G′_V` is in its `j`-block, `j` the layer index. -/
theorem jBlock_of_mem_blockSet (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hy : y ∈ blockSet (locG' g hnn hM1 H hk hρ V) x) :
    jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1)
        ((locG' g hnn hM1 H hk hρ V).layerIndex x) y =
      jBlock S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1)
        ((locG' g hnn hM1 H hk hρ V).layerIndex x) x := by
  classical
  unfold blockSet at hy
  split_ifs at hy with h1
  · exact (GeneratingSet.mem_blk).1 hy
  · rw [Finset.mem_singleton.1 hy]

/-- The two sites of an interface pair of `G′_V` lie over cubes of `𝕋_{k+1}` within one cube. -/
theorem cubeOfC_near_of_pair (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : BlocksAdjacent (locG' g hnn hM1 H hk hρ V) x x') :
    LargeField.supDist (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x)
      (cubeOfC (c := g.c) (n1 := n (k + 1)) hM1 x') ≤ 1 := by
  obtain ⟨y₀, hy₀, y₀', hy₀', hadj⟩ := h
  have e1 := cubeOfC_eq_of_jBlock g hnn hM1 hk (layerIndex_locG'_le g hnn hM1 H hk hρ V x).1
    (jBlock_of_mem_blockSet g hnn hM1 H hk hρ V hy₀)
  have e2 := cubeOfC_eq_of_jBlock g hnn hM1 hk (layerIndex_locG'_le g hnn hM1 H hk hρ V x').1
    (jBlock_of_mem_blockSet g hnn hM1 H hk hρ V hy₀')
  rw [← e1, ← e2, cubeOfC_eq_toCube, cubeOfC_eq_toCube]
  have hc := g.hc
  exact cube_adj_near (M1 := g.M1) (N₁ := g.c * n (k + 1)) (q := k + 1) (by simp)
    (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne g.M1))) (adj_toCube g hM1 hadj)

/-- A site of the block of a site `x` of `G′_V` goes to the block of layer `l ≥ l(x)` of `toCube x`. -/
theorem toCube_mem_blk_of_blockSet (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hy : y ∈ blockSet (locG' g hnn hM1 H hk hρ V) x) {l : ℕ}
    (hl : (locG' g hnn hM1 H hk hρ V).layerIndex x ≤ l) (hlk : l ≤ k + 1)
    {ϱ' : ℝ} (Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) ϱ') :
    toCube g hM1 y ∈ Gc.blk l (toCube g hM1 x) :=
  GeneratingSet.mem_blk.2 (Background.jBlock_mono hl hlk (jBlock_toCube_eq g hM1
    (jBlock_of_mem_blockSet g hnn hM1 H hk hρ V hy)))

/-- A site of the `n`-block of `x` goes to the block of layer `l ≥ n` of `toCube x`. -/
theorem toCube_mem_blk {k : ℕ} {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)} {j l : ℕ}
    (hjl : j ≤ l) (hlk : l ≤ k + 1) {ϱ ϱ' : ℝ}
    {G : GeneratingSet S.d S.L (g.c * n (k + 1) * S.L ^ m₁) (k + 1) ϱ} (hy : y ∈ G.blk j x)
    (Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) ϱ') :
    toCube g hM1 y ∈ Gc.blk l (toCube g hM1 x) :=
  GeneratingSet.mem_blk.2 (Background.jBlock_mono hjl hlk (jBlock_toCube_eq g hM1
    (GeneratingSet.mem_blk.1 hy)))

/-- A site of the block of a site `x` of `G′_V` goes to the block of layer `l` (`l(x) ≤ l ≤ k`) of
`toCubeK x`. -/
theorem toCubeK_mem_blk_of_blockSet (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x y : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (hy : y ∈ blockSet (locG' g hnn hM1 H hk hρ V) x) {l : ℕ}
    (hl : (locG' g hnn hM1 H hk hρ V).layerIndex x ≤ l) (hlk : l ≤ k)
    {ϱ' : ℝ} (Gc : GeneratingSet S.d S.L (g.M1 * (g.c * n k)) k ϱ') :
    toCubeK g hnn hM1 hk y ∈ Gc.blk l (toCubeK g hnn hM1 hk x) :=
  GeneratingSet.mem_blk.2 (Background.jBlock_mono hl hlk (jBlock_toCubeK_eq g hnn hM1 hk (hl.trans hlk)
    (jBlock_of_mem_blockSet g hnn hM1 H hk hρ V hy)))

/-- **The two sites of an interface pair of `G′_V` off `Ω_{k+1}` lie over cubes of `𝕋_k` within one
cube** (their blocks, of layers `≤ k`, lie in one cube of `𝕋_k` each). -/
theorem cubeKOfC_near_of_pair (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {x x' : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)}
    (h : BlocksAdjacent (locG' g hnn hM1 H hk hρ V) x x')
    (hx : (locG' g hnn hM1 H hk hρ V).layerIndex x ≤ k)
    (hx' : (locG' g hnn hM1 H hk hρ V).layerIndex x' ≤ k) :
    LargeField.supDist (cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x)
      (cubeKOfC (c := g.c) (n1 := n (k + 1)) (n0 := n k) hM1 x') ≤ 1 := by
  obtain ⟨y₀, hy₀, y₀', hy₀', hadj⟩ := h
  have e1 := cubeKOfC_eq_of_jBlock g hnn hM1 hk hx (jBlock_of_mem_blockSet g hnn hM1 H hk hρ V hy₀)
  have e2 := cubeKOfC_eq_of_jBlock g hnn hM1 hk hx' (jBlock_of_mem_blockSet g hnn hM1 H hk hρ V hy₀')
  rw [← e1, ← e2, cubeKOfC_eq_toCubeK g hnn hM1 hk, cubeKOfC_eq_toCubeK g hnn hM1 hk]
  have hc := g.hc
  exact cube_adj_near (M1 := g.M1) (N₁ := g.c * n k) (q := k) (by simp)
    (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (NeZero.ne g.M1))) (adj_toCubeK g hnn hM1 hk hadj)

end Geo

end Balaban.RootFSpine

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section CubeSets

variable {d M1 N₁ L N q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- **A site over a cube within two cubes of the centre is in the top layer of `G_q(□)`**, a data site,
of layer index `q` (`1 ≤ q`). -/
theorem genCube_site_spec (hm : N₁ * L ^ (q - q) = c * n) (hq : 1 ≤ q) (y₀ : Torus d n)
    {s : Torus d (M1 * N₁ * L ^ q)} (hs : blockMap (L ^ q * (c * M1)) n s ∈ nbhd 2 {y₀}) :
    s ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y₀).Ω 1 ∧
      s ∈ dataSites (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y₀) ∧
      (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y₀).layerIndex s = q ∧
      s ∈ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y₀).layer q := by
  set G := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y₀
  have htop : s ∈ G.Ω q := (genCube_top_mem hm y₀).2 hs
  have h1 : s ∈ G.Ω 1 := G.Ω_antitone le_rfl hq (Nat.le_succ q) htop
  have hl : s ∈ G.layer q := G.mem_layer.2 ⟨htop, by rw [G.top]; exact Finset.notMem_empty _⟩
  exact ⟨h1, (mem_dataSites _).2 (Or.inl h1), G.layerIndex_eq hq le_rfl hl, hl⟩

/-- **A site over a cube within two cubes of the centre in the mixed set `G_{k+1}(□')`**: in the top
layer `k + 1` if it lies in `Ω`, in the layer `k` otherwise; a data site. -/
theorem genCubeMixed_site_spec {k : ℕ} (hm : N₁ * L ^ (k + 1 - (k + 1)) = c * n) (hk : 1 ≤ k)
    (y₀ : Torus d n) (Om : Finset (Torus d (M1 * N₁ * L ^ (k + 1))))
    (hOm : IsBlockUnion L (M1 * N₁) (k + 1) (k + 1) Om) {s : Torus d (M1 * N₁ * L ^ (k + 1))}
    (hs : blockMap (L ^ (k + 1) * (c * M1)) n s ∈ nbhd 2 {y₀}) :
    s ∈ (genCubeMixed hm y₀ Om hOm).Ω 1 ∧ s ∈ dataSites (genCubeMixed hm y₀ Om hOm) ∧
      (s ∈ Om → (genCubeMixed hm y₀ Om hOm).layerIndex s = k + 1 ∧
        s ∈ (genCubeMixed hm y₀ Om hOm).layer (k + 1)) ∧
      (s ∉ Om → (genCubeMixed hm y₀ Om hOm).layerIndex s = k ∧
        s ∈ (genCubeMixed hm y₀ Om hOm).layer k) := by
  set G := genCubeMixed hm y₀ Om hOm
  set G₀ := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := k + 1) c n y₀
  have hA : s ∈ cubePre M1 N₁ L (k + 1) (L ^ (k + 1) * (c * M1)) n (nbhd 2 {y₀}) := by
    rw [mem_cubePre]; exact hs
  have htop0 : s ∈ G₀.Ω (k + 1) := (genCube_top_mem hm y₀).2 hs
  have hk0 : s ∈ G₀.Ω k := G₀.Ω_antitone hk (Nat.le_succ k) (by omega) htop0
  have hGk : s ∈ G.Ω k := by
    rw [genCubeMixed_Ω']; simp only [show k ≠ k + 1 by omega, ↓reduceIte]; exact hk0
  have h1 : s ∈ G.Ω 1 := G.Ω_antitone le_rfl hk (by omega) hGk
  refine ⟨h1, (mem_dataSites _).2 (Or.inl h1), fun hO => ?_, fun hO => ?_⟩
  · have ht : s ∈ G.Ω (k + 1) := by
      rw [genCubeMixed_Ω']; simp only [↓reduceIte]; exact Finset.mem_inter.2 ⟨hO, hA⟩
    have hl : s ∈ G.layer (k + 1) := G.mem_layer.2 ⟨ht, by rw [G.top]; exact Finset.notMem_empty _⟩
    exact ⟨G.layerIndex_eq (by omega) le_rfl hl, hl⟩
  · have hn : s ∉ G.Ω (k + 1) := by
      rw [genCubeMixed_Ω']; simp only [↓reduceIte]; exact fun h => hO (Finset.mem_inter.1 h).1
    have hl : s ∈ G.layer k := G.mem_layer.2 ⟨hGk, hn⟩
    exact ⟨G.layerIndex_eq hk (Nat.le_succ k) hl, hl⟩

end CubeSets

end Balaban.LargeField

namespace Balaban.RootFSpine

section Datum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

/-- A cube lies in a fine set of cubes iff all its sites do. -/
theorem cubeSub_fineSet_iff (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {j : ℕ} (hj : j ≤ K)
    (W : Set (Torus S.d (n j))) (y : Torus S.d (n j)) :
    CubeSub (S := S) (n := n) M K j y (fineSet (S := S) (n := n) M K j W) ↔ y ∈ W := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := cubeMap_surjective (S := S) (M := M) hnn hj y
    have := h x hx
    simp only [fineSet, Set.mem_ofPred_eq, hx] at this
    exact this
  · intro hy x hx
    show LargeField.cubeMap n S.L M K j x ∈ W
    rw [hx]; exact hy


end Datum

end Balaban.RootFSpine
