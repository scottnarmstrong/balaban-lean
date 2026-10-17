/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysCountBridge

/-!
# The physical two-scale count of a quiet piece

P6 p. 14 (2.31) charges the two portions of a quiet piece in physical
`π_j` and `π_{j+1}` cubes.  The local positive decomposition has at most
`M^d` layer blocks over each such cube.  The wall-slot charge still requires
the analytic estimate for the corresponding physical faces.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation
  Balaban.LargeField.ActionConv Finset

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {k0 M K : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M) (Hl : RegionHistory S n R k0 K)
  (j : ℕ) (Zc : Finset (Torus S.d (n (j + 1))))
  (hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1)))
  (hk : j + 1 ≤ K)

open Classical in
/-- The `j`-layer cells of a quiet piece lie over the first mixed-count set
of P6 (2.31), and their number is at most `M^d` times its size. -/
theorem piece_lower_layerBlock_count_le (X : Region (locGen g Hl j Zc hZc hk))
    (hXs : X.sites = Xfine g Hl j Zc) :
    ((X.sites.filter fun x => (locGen g Hl j Zc hZc hk).layerIndex x = j).image
      fun x => (locGen g Hl j Zc hZc hk).blk j x).card ≤
      M ^ S.d * (Finset.univ.filter fun y : Torus S.d (n j) =>
        y ∉ (Hl.step j).Z ∧
        blockMap S.L (n (j + 1)) y ∈ Zc ∧
        blockMap S.L (n (j + 1)) y ∉ (Hl.step j).Omega).card := by
  classical
  let G := locGen g Hl j Zc hZc hk
  have hmod : g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1 - j) = M * n j := by
    rw [show j + 1 - j = 1 by omega, pow_one, Hl.F.hnn j (by omega)]
    calc
      g.M1 * (g.c * n (j + 1)) * S.L =
          (g.c * g.M1) * (S.L * n (j + 1)) := by ring
      _ = M * (S.L * n (j + 1)) := congrArg (fun t => t * (S.L * n (j + 1))) g.hM.symm
  apply X.layerBlock_count_le_cubeMap (q := j) (M := M) (n := n j)
    (by omega) hmod _
  intro x hx hxj
  have hxX : x ∈ Xfine g Hl j Zc := by rw [← hXs]; exact hx
  have hmem := Xfine_mem g Hl j Zc hxX
  have hnotTop : x ∉ G.Ω (j + 1) := by
    have hxΩ := X.sub_Ω hx
    obtain ⟨_, _, hlayer⟩ := G.layerIndex_spec hxΩ
    rw [hxj] at hlayer
    exact (G.mem_layer.mp hlayer).2
  have hOm : blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) x ∉
      (Hl.step j).Omega := by
    intro h
    exact hnotTop ((locGen_Ω_top_iff g Hl j Zc hZc hk hxX).mpr h)
  have hsuc := blockMap_k_succ (M1 := g.M1) (c := g.c)
    (Hl.F.hnn j (by omega)) x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hfactor : S.L ^ j * M = S.L ^ j * (g.c * g.M1) :=
    congrArg (fun t => S.L ^ j * t) g.hM
  rw [hfactor]
  refine ⟨hmem.2, ?_, ?_⟩
  · rw [hsuc]
    exact hmem.1
  · rw [hsuc]
    exact hOm

open Classical in
/-- The `j+1`-layer cells lie over the second mixed-count set of P6 (2.31). -/
theorem piece_upper_layerBlock_count_le (X : Region (locGen g Hl j Zc hZc hk))
    (hXs : X.sites = Xfine g Hl j Zc) :
    ((X.sites.filter fun x => (locGen g Hl j Zc hZc hk).layerIndex x = j + 1).image
      fun x => (locGen g Hl j Zc hZc hk).blk (j + 1) x).card ≤
      M ^ S.d * (Finset.univ.filter fun y : Torus S.d (n (j + 1)) =>
        y ∈ Zc ∧ y ∈ (Hl.step j).Omega).card := by
  classical
  let G := locGen g Hl j Zc hZc hk
  have hmod : g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1 - (j + 1)) =
      M * n (j + 1) := by
    rw [Nat.sub_self, pow_zero, mul_one]
    calc
      g.M1 * (g.c * n (j + 1)) = (g.c * g.M1) * n (j + 1) := by ring
      _ = M * n (j + 1) := congrArg (fun t => t * n (j + 1)) g.hM.symm
  apply X.layerBlock_count_le_cubeMap (q := j + 1) (M := M) (n := n (j + 1))
    le_rfl hmod _
  intro x hx hxj
  have hxX : x ∈ Xfine g Hl j Zc := by rw [← hXs]; exact hx
  have hmem := Xfine_mem g Hl j Zc hxX
  have htop : x ∈ G.Ω (j + 1) := by
    have hxΩ := X.sub_Ω hx
    obtain ⟨_, _, hlayer⟩ := G.layerIndex_spec hxΩ
    rw [hxj] at hlayer
    exact (G.mem_layer.mp hlayer).1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hfactor : S.L ^ (j + 1) * M = S.L ^ (j + 1) * (g.c * g.M1) :=
    congrArg (fun t => S.L ^ (j + 1) * t) g.hM
  rw [hfactor]
  exact ⟨hmem.1, (locGen_Ω_top_iff g Hl j Zc hZc hk hxX).mp htop⟩


open Classical in
/-- The positive decomposition of a quiet piece has total count at most `M^d`
times the P6 (2.31) mixed count, with at most `2d` wall slots per cell.  The
bound with the decomposition's own count therefore dominates P6's count by the
constant `M^d`, and no identification of cells with physical cubes is needed. -/
theorem exists_piece_stepDecomp_total_le (hj : 1 ≤ j)
    (X : Region (locGen g Hl j Zc hZc hk))
    (hXs : X.sites = Xfine g Hl j Zc) :
    ∃ Dc : StepDecomp X,
      (∀ i, 0 < Dc.wt i) ∧ Dc.inc = 2 * S.d ∧
      Dc.total ≤ (M ^ S.d : ℝ) *
        (((Finset.univ.filter fun y : Torus S.d (n j) =>
          y ∉ (Hl.step j).Z ∧
          blockMap S.L (n (j + 1)) y ∈ Zc ∧
          blockMap S.L (n (j + 1)) y ∉ (Hl.step j).Omega).card : ℝ) +
        ((Finset.univ.filter fun y : Torus S.d (n (j + 1)) =>
          y ∈ Zc ∧ y ∈ (Hl.step j).Omega).card : ℝ)) ∧
      (∀ q, Dc.wall q ⊆ (Dc.cube (Dc.wallCube q)).crossing) := by
  obtain ⟨Dc, hpos, hinc, hcount, hwall⟩ :=
    exists_piece_stepDecomp_positive_blocks g Hl j Zc hZc hk hj X hXs
  refine ⟨Dc, hpos, hinc, ?_, hwall⟩
  rw [hcount]
  have h1 := piece_lower_layerBlock_count_le g Hl j Zc hZc hk X hXs
  have h2 := piece_upper_layerBlock_count_le g Hl j Zc hZc hk X hXs
  have h1' := (Nat.cast_le (α := ℝ)).mpr h1
  have h2' := (Nat.cast_le (α := ℝ)).mpr h2
  push_cast at h1' h2'
  linarith

end Balaban.LargeField
