/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgClose
public import Balaban.LargeField.Characteristic.Stencil
public import Balaban.Fluctuation.H7Bridge
public import Balaban.Background.GenSetStabilityRestrict

/-!
# The cube generating set inside the global one: geometry and closeness

For the generating set `G_q(□) = genCube □` (the preimage of the `2`-neighbourhood of the cube
`□ = y0` of side `P = L^q c M₁`), the set `Ω_q = cubePre (nbhd 2 {y0})`
(`genCube_Omega_top`). A site of the cube `y0` is at path distance at least `c M₁`
from the shadow of the complement of `Ω₁` (`genCube_far`): the shadow lies in the outer ring of
cubes at index distance `2` from `y0`, and the fine sup-distance between two sites whose cubes are
at index distance `2` is at least `P + 1`.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.Fluctuation

variable {d M1 N₁ L q : ℕ} [NeZero L] [NeZero M1] [NeZero N₁]

/-- The top layer of the cube generating set is the preimage of the `2`-neighbourhood of the cube. -/
theorem genCube_Omega_top {c n : ℕ} [NeZero n] (hm : N₁ * L ^ (q - q) = c * n) (a : Torus d n) :
    (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n a).Ω q =
      cubePre M1 N₁ L q (L ^ q * (c * M1)) n (nbhd 2 {a}) := by
  rw [genCube_Ω, minLayer_self,
    (isCubeUnion_cubePre (M1 := M1) (N₁ := N₁) (L := L) (q := q) (le_refl q) hm
      (nbhd 2 {a})).cubeInterior_eq]

variable {c n : ℕ} [NeZero n]

open Classical in
/-- **A site of the cube is far from the shadow of the complement of `Ω₁`** (`q = 1`): for `x` in
the cube `y0` and `w` in the shadow of `{y ∉ Ω₁(G_1(□))}`, the path distance is at least `c M₁`. -/
theorem genCube_far (hm : N₁ * L ^ (1 - 1) = c * n) (y0 : Torus d n)
    {x w : Torus d (M1 * N₁ * L ^ 1)} (hx : blockMap (L ^ 1 * (c * M1)) n x = y0)
    (hw : w ∈ shadowN (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0)
      (Finset.univ.filter fun y => y ∉ (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0).Ω 1)) :
    ENNReal.ofReal ((c * M1 : ℕ) : ℝ) ≤
      (genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0).pathDist x w := by
  set G0 := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := 1) c n y0 with hG0
  have hΩ : G0.Ω 1 = cubePre M1 N₁ L 1 (L ^ 1 * (c * M1)) n (nbhd 2 {y0}) :=
    genCube_Omega_top hm y0
  have hn : M1 * N₁ * L ^ 1 = (L ^ 1 * (c * M1)) * n := cube_fine_eq hm
  have hPpos : 0 < L ^ 1 * (c * M1) := by
    rcases Nat.eq_zero_or_pos (L ^ 1 * (c * M1)) with h0 | h0
    · exfalso
      have : 0 < M1 * N₁ * L ^ 1 := Nat.pos_of_ne_zero (by
        have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne N₁; positivity)
      rw [hn, h0] at this; simp at this
    · exact h0
  simp only [shadowN, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  obtain ⟨hwΩ, hcase⟩ := hw
  have hwc : blockMap (L ^ 1 * (c * M1)) n w ∈ nbhd 2 {y0} := by
    have := hwΩ; rw [hΩ, mem_cubePre] at this; exact this
  obtain ⟨y', hy'W, hadj⟩ : ∃ y', y' ∉ G0.Ω 1 ∧ Adj w y' := by
    rcases hcase with h | ⟨y', hy', hadj⟩
    · exact absurd hwΩ h
    · exact ⟨y', hy', hadj⟩
  have hy'c : blockMap (L ^ 1 * (c * M1)) n y' ∉ nbhd 2 {y0} := by
    intro h; apply hy'W; rw [hΩ, mem_cubePre]; exact h
  have hd1 : supDist w y' ≤ 1 := Balaban.LargeField.Adj.supDist_le_one hadj
  have hd2 : supDist (blockMap (L ^ 1 * (c * M1)) n w) (blockMap (L ^ 1 * (c * M1)) n y') ≤ 1 :=
    supDist_blockMap_le_one (M1 := M1) (N₁ := N₁) (L := L) (q := 1) hn (D := 1)
      hPpos w y' hd1
  have hfar : 2 ≤ supDist (blockMap (L ^ 1 * (c * M1)) n w) y0 := by
    by_contra hlt
    push Not at hlt
    apply hy'c
    rw [mem_nbhd]
    refine ⟨y0, Set.mem_singleton _, ?_⟩
    have t := supDist_triangle (blockMap (L ^ 1 * (c * M1)) n y')
      (blockMap (L ^ 1 * (c * M1)) n w) y0
    have hd3 := (supDist_comm (blockMap (L ^ 1 * (c * M1)) n w)
      (blockMap (L ^ 1 * (c * M1)) n y')).symm ▸ hd2
    omega
  have hfine : L ^ 1 * (c * M1) + 1 ≤ supDist x w := by
    by_contra hlt
    push Not at hlt
    have h1 := supDist_blockMap_le_one (M1 := M1) (N₁ := N₁) (L := L) (q := 1) hn
      (D := L ^ 1 * (c * M1)) le_rfl x w (by omega)
    rw [hx] at h1
    rw [supDist_comm] at hfar
    omega
  have ht : ((L ^ 1 * (c * M1) + 1 : ℕ) : ℝ) ≤ Green.torusDist d (M1 * N₁ * L ^ 1) x w :=
    ((Nat.cast_le.2 hfine).trans (supDist_le_torusDist x w))
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (Balaban.Background.pathDist_ge_torusDist G0 x w)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ 1 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [le_div_iff₀ hL0]
  push_cast at ht ⊢
  nlinarith

end Balaban.LargeField.Base
