/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowLiftRead
public import Balaban.LargeField.R.WindowRegionGeom
public import Balaban.LargeField.Operators.MainAction
public import Balaban.LargeField.Background.StepGenSetsFlow

/-!
# Geometry of the data sites of a piece against its ancestors

P7 p. 501 (2.14): a data site of the local generating set of the piece of a component `c` has its
`π_{j+1}`-cube within `⌊R_j⌋ + 2` of `c`, hence its `π_{j+2}`-cube within `⌊R_{j+1}⌋ + 2` of the
parent.  Components of `Z^pre_s` are `ω_s`-separated, so a cube close to a descendant of the window
component is in it or not over the lineage of the window component.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory Balaban.Background

section Near

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K}

/-- A cube close to a descendant `Y` of `Z` is in `Y` or is not over the lineage of `Z`. -/
theorem near_cases_desc {k m : ℕ} {Y : H.Comp k} {Z : H.Comp m} (hd : H.Desc k m Y Z)
    {e v : Torus S.d (n k)} (hv : v ∈ Y.1) (hdist : supDist e v < S.omega k) :
    e ∈ Y.1 ∨ e ∉ ((H.lin k m Z : Finset (Torus S.d (n k))) : Set _) := by
  by_cases hmem : e ∈ ((H.lin k m Z : Finset (Torus S.d (n k))) : Set _)
  · left
    obtain ⟨c, hd', hec⟩ := mem_lin.mp (Finset.mem_coe.mp hmem)
    have hzX : v ∈ H.Zp k := comp_subset Y.2 hv
    have hzc : v ∈ c.1 := mem_comp_of_close c.2 hec hzX hdist
    have hcY : c = Y := Subtype.ext (comp_eq_of_mem c.2 Y.2 hzc hv)
    subst hcY
    exact hec
  · right
    exact hmem

/-- The cube of a data site of the local generating set of `c` is within `⌊R_j⌋ + 2` of `c`. -/
theorem dataSite_cube_near_comp (g : Geo S n R M) {j : ℕ} (hK : j + 1 ≤ K) (c : H.Comp (j + 1))
    {u : Torus S.d (g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1))}
    (hu : u ∈ dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)) :
    ∃ v ∈ c.1, supDist (blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) u) v ≤ ⌊R j⌋₊ + 2 := by
  have h := genBoundaryLocal_subset_V _ _ _ _ _ _ _ _ hu
  obtain ⟨w, hw, hd1⟩ := mem_nbhd.mp h
  obtain ⟨v, hv, hd2⟩ := mem_nbhd.mp (show w ∈ nbhd (⌊R j⌋₊ + 1) (c.1 : Set _) from hw)
  refine ⟨v, hv, ?_⟩
  have := supDist_triangle (blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) u) w v
  omega

/-- The `π_{j+1}`-cube of a window site over a data site of the piece `c` is within `⌊R_j⌋ + 2` of
`c`. -/
theorem cube_near_piece (g : Geo S n R M) {m' j : ℕ} (hmK : m' + 1 ≤ K) (hj : j ≤ m')
    (c : H.Comp (j + 1)) (hK : j + 1 ≤ K) {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)) :
    ∃ v ∈ c.1, supDist (cubeMap n S.L M (m' + 1) (j + 1) y) v ≤ ⌊R j⌋₊ + 2 := by
  obtain ⟨v, hv, hd⟩ := dataSite_cube_near_comp g hK c hy
  rw [blockMap_castSite_cube g] at hd
  exact ⟨v, hv, hd⟩

/-- At a data site of the piece `c`, the `π_{j+1}`-cube of the window site is in `c` or is not over
the lineage of the window component. -/
theorem hcase_piece (g : Geo S n R M) {m' j : ℕ} (hmK : m' + 1 ≤ K) (hj : j ≤ m')
    {Z : H.Comp (m' + 1)} (c : H.Comp (j + 1)) (hc : H.Desc (j + 1) (m' + 1) c Z) (hK : j + 1 ≤ K)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)) :
    cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1 ∨
      cubeMap n S.L M (m' + 1) (j + 1) y ∉ ((H.lin (j + 1) (m' + 1) Z : Finset _) : Set _) := by
  obtain ⟨v, hv, hd⟩ := cube_near_piece g hmK hj c hK hy
  refine near_cases_desc hc hv (lt_of_le_of_lt hd ?_)
  have := (H.stepGeom (show j < K by omega)).rad.omega_rho
  omega

/-- At a data site of the piece `c`, a child of the component `P`, the `π_{j+2}`-cube of the window
site is in `P` or is not over the lineage of the window component. -/
theorem hcase_parent (g : Geo S n R M) {m' j : ℕ} (hmK : m' + 1 ≤ K) (hj : j < m')
    {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} {P : H.Comp (j + 2)} (hcP : c ∈ H.parts (j + 1) P)
    (hP : H.Desc (j + 2) (m' + 1) P Z) (hK : j + 1 ≤ K)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : torusCast (piece_torus_eq g H.F.hnn hmK hj.le) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK)) :
    cubeMap n S.L M (m' + 1) (j + 2) y ∈ P.1 ∨
      cubeMap n S.L M (m' + 1) (j + 2) y ∉ ((H.lin (j + 2) (m' + 1) Z : Finset _) : Set _) := by
  obtain ⟨v, hv, hd⟩ := cube_near_piece g hmK hj.le c hK hy
  have hsucc := ((H.mem_parts (j + 1) c P).mp hcP).2
  have hvP : blockMap S.L (n (j + 2)) v ∈ P.1 := hsucc ⟨v, hv, rfl⟩
  have hnn : ∀ i, i < m' + 1 → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (by omega)
  have hsucc2 := cubeMap_succ (M := M) hnn (j := j + 1) (by omega) y
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  have h1 := supDist_blockMap_le (L := S.L) (m := n (j + 2)) (H.F.hnn (j + 1) (by omega))
    (cubeMap n S.L M (m' + 1) (j + 1) y) v
  rw [hsucc2] at h1
  have h2 : (supDist (cubeMap n S.L M (m' + 1) (j + 1) y) v + S.L - 1) / S.L ≤ ⌊R j⌋₊ + 2 := by
    refine Nat.div_le_of_le_mul ?_
    have e : S.L * (⌊R j⌋₊ + 2) = S.L * ⌊R j⌋₊ + 2 * S.L := by ring
    have e2 : ⌊R j⌋₊ ≤ S.L * ⌊R j⌋₊ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hmono := g.hRmono (j + 1)
  simp only [Nat.add_sub_cancel] at hmono
  have hom : 2 * ⌊R (j + 1)⌋₊ + S.L + 11 ≤ S.omega (j + 2) :=
    (H.stepGeom (show j + 1 < K by omega)).rad.omega_rho
  refine near_cases_desc hP hvP (lt_of_le_of_lt (h1.trans h2) ?_)
  omega

end Near

end Balaban.LargeField
