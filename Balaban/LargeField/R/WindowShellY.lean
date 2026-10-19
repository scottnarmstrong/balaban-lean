/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.ParentR2Y

/-!
# The block bounds over `Y` for sites of any generating set (blocker 4)

The bounds of `ParentR2Y` are stated for the interface pairs of the small-field generating set
`genW`.  Their proofs read only the top-scale blocks of the two sites: the cube of one site lies in
`Y`, the cube of the other within one cube of it, and the two `(j+1)`-blocks contain adjacent
sites.  This file states them in that form, so that they apply to the sites of the local
generating sets of the window pieces:

* `parentPsi_pair_of_adj_over_Y`: `rn (Ψ(s) - Ψ(s')) < 3 δ_{j+1}` for the field `parentPsi` of
  a global `ψ_{j+1}` with `χ_Y(ψ_{j+1}) ≠ 0`;
* `parentPsi_sq_of_over_Y`: the sphere bound, the lemma `parentPsi_sphere_over_Y` restated for
  sites without a generating set.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section ShellY

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- The datum of a cube generating set reads `ψ_{j+1}` at the top block of a data site: it is the
field `parentPsi` there. -/
theorem cubeData_Ψ_eq_parentPsi (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (y₁ : Torus S.d (n (j + 1))) {s : BgT Cx.geo (j + 1)}
    (hs : s ∈ dataSites (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₁)) (i : Fin N) :
    (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) (fun i => hv i) Cx.geo.c (n (j + 1)) y₁
      (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s i = ((parentPsi Cx ψk s i : ℝ) : ℂ) := by
  unfold cubeData
  rw [liftSingle_Ψ _ _ _ hs]
  rfl

/-- A site over a cube within two cubes of `y₁` is a data site of the cube generating set. -/
theorem mem_dataSites_genCube {y₁ : Torus S.d (n (j + 1))} {s : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ nbhd 2 {y₁}) :
    s ∈ dataSites (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₁) := by
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  exact (mem_dataSites _).2 (Or.inl (mem_Ω_one_of_top _ (Nat.succ_pos j)
    ((genCube_top_mem hm y₁).2 hs)))

/-- **The pair bound over `Y` for adjacent top blocks.**  If `χ_Y(ψ) ≠ 0`, `s` lies over a cube
`y₁ ∈ Y`, the cube of `s'` is within one cube of `y₁` and the `(j+1)`-blocks of `s` and `s'`
contain adjacent sites, then `rn (Ψ(s) - Ψ(s')) < 3 δ_{j+1}` for `Ψ = parentPsi ψ`. -/
theorem parentPsi_pair_of_adj_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {y₁ : Torus S.d (n (j + 1))} (hy₁ : y₁ ∈ Y)
    {s s' : BgT Cx.geo (j + 1)}
    (hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s = y₁)
    (hs' : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s' ∈ nbhd 1 {y₁})
    (hadj : ∃ y y' : BgT Cx.geo (j + 1),
      jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) y =
        jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s ∧
      jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) y' =
        jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s' ∧ Adj y y') :
    rn (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) < 3 * Cx.cs.delta (j + 1) := by
  classical
  have hmem : y₁ ∈ cubeFin Y := by simp [cubeFin, hy₁]
  obtain ⟨hBC, hGC⟩ := chiY_ne_zero_blockClose_gradClose Cx Y ψk hv h hmem
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have hGc : ∀ x, x ∈ (genCube (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
      (q := j + 1) Cx.geo.c (n (j + 1)) y₁).Ω (j + 1) ↔
      blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) x ∈ nbhd 2 {y₁} :=
    fun x => genCube_top_mem hm y₁
  have hmain := pair_bound_of_close_blocks (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1))
    (L := S.L) (q := j + 1) (c := Cx.geo.c) (n := n (j + 1)) hm (Nat.succ_pos j) _ y₁ hGc _ _ _ _
    hBC hGC hs hs' (by obtain ⟨y, y', hy, hy', ha⟩ := hadj; exact ⟨y, GeneratingSet.mem_blk.2 hy, y', GeneratingSet.mem_blk.2 hy', ha⟩)
  have hy₁' : y₁ ∈ nbhd 2 ({y₁} : Set (Torus S.d (n (j + 1)))) := subset_nbhd 2 _ rfl
  have e1 := cubeData_Ψ_eq_parentPsi Cx ψk hv y₁ (mem_dataSites_genCube Cx (by rw [hs]; exact hy₁'))
  have e2 := cubeData_Ψ_eq_parentPsi Cx ψk hv y₁
    (mem_dataSites_genCube Cx (nbhd_mono (by omega) subset_rfl hs'))
  have hv0 : vn (fun i => ((parentPsi Cx ψk s i : ℝ) : ℂ) - ((parentPsi Cx ψk s' i : ℝ) : ℂ)) <
      3 * Cx.cs.delta (j + 1) := by
    have : (fun i => ((parentPsi Cx ψk s i : ℝ) : ℂ) - ((parentPsi Cx ψk s' i : ℝ) : ℂ)) =
        fun i => (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
          (q := j + 1) (fun i => hv i) Cx.geo.c (n (j + 1)) y₁
          (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s i -
          (cubeData (M1 := Cx.geo.M1) (N₁ := Cx.geo.c * n (j + 1)) (L := S.L)
          (q := j + 1) (fun i => hv i) Cx.geo.c (n (j + 1)) y₁
          (blockCfgOf Cx.geo Cx.hnn le_rfl Cx.hkK ψk)).Ψ s' i := by
      funext i; rw [e1 i, e2 i]
    rw [this]; exact hmain
  have e3 : (fun i => ((parentPsi Cx ψk s i : ℝ) : ℂ) - ((parentPsi Cx ψk s' i : ℝ) : ℂ)) =
      fun i => (((parentPsi Cx ψk s i - parentPsi Cx ψk s' i : ℝ)) : ℂ) := by
    funext i; push_cast; rfl
  rwa [e3, vn_ofReal] at hv0

end ShellY

end Balaban.LargeField
