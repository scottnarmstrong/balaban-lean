/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RetainedShellWitness
public import Balaban.LargeField.History.TopBlockTransport

/-!
# Non-vacuity of `TopBlockTransport`

On the lineage localization `H0.locRH T Z0` of the genuine-radii ripe history (the history of
`retained_shell_witness`), at the scale `q = k₁(T) ≤ T`: there are a scale `j + 1 ≤ T`, a
non-removed component `C` of `Z^pre_{j+1}`, a fine site `x` over a cube `q ∈ C` of the retained
shell (`q ∈ Ω''_{j+1}`, within one cube of `Y = Z_{j+1}ᶜ`), such that `q` satisfies the two
conditions of the first family of `ChiDomProp` for the localized history of `C`
(`cube_conditions_of_mem_Omega`) and the top-scale block of `x` belongs to
`genBlocksIn (chiDomGen …) (j+1) (nbhd 1 {q})` (`topBlock_mem_genBlocksIn`).

This exhibits the cube-level content of `datum_site_topBlock` on a genuine history.  No small-field
context `SFCtx` is built here, so no datum site of `G_{j+1}` is named: the statements that use
`dataSites_cube_near` (`datum_site_topBlock`, `interface_pair_topBlocks`) are not instantiated.
-/

@[expose] public section

namespace Balaban.Inhabited.RipeGeo

open Balaban Balaban.LargeField Balaban.Inhabited Balaban.Multiscale

theorem aux_scale (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T) (u w : Torus S0.d (n0 q))
    (hu : u ∈ ((H0.locRH T Z0).step q).Z) (hw : w ∉ ((H0.locRH T Z0).step q).Z) :
    ∃ j, j + 1 ≤ T ∧ ∃ C : (H0.locRH T Z0).Comp (j + 1), C.1 ∉ (H0.locRH T Z0).rem (j + 1) ∧
      ∃ x ∈ C.1, ∃ y ∈ (((H0.locRH T Z0).step (j + 1)).Z)ᶜ, supDist x y ≤ 1 ∧
        x ∈ ((H0.locRH T Z0).step j).OmegaDD := by
  cases q with
  | zero => omega
  | succ j =>
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_adj_cross (conn0 (j + 1) u w) hu hw
    obtain ⟨C, hC, hxC⟩ := RegionHistory.exists_retained_of_mem_Z (H := H0.locRH T Z0) hx
    have hd : supDist x y ≤ 1 := Adj.supDist_le_one hxy
    exact ⟨j, hqT, C, hC, x, hxC, y, hy, hd,
      (H0.locRH T Z0).retained_shell_subset_OmegaDD_of_dist j hC hxC hy (hd.trans (by omega))⟩

/-- **Non-vacuity of `TopBlockTransport` (cube level).**  On the localized genuine-radii ripe
history, at a scale `j + 1 ≤ T`, for a non-removed component `C` and a cube `q ∈ C ∩ Ω''_{j+1}`
within one cube of `Z_{j+1}ᶜ`, there is a fine site `x` over `q` whose top-scale block belongs to
`genBlocksIn (chiDomGen …) (j+1) (nbhd 1 {q})`, and `q` satisfies the two conditions of the first
family of `ChiDomProp` for the localized history of `C`. -/
theorem topBlockTransport_witness :
    ∃ j, j + 1 ≤ T ∧ ∃ C : (H0.locRH T Z0).Comp (j + 1),
      C.1 ∉ (H0.locRH T Z0).rem (j + 1) ∧
      ∃ q ∈ C.1, (∃ y ∈ (((H0.locRH T Z0).step (j + 1)).Z)ᶜ, supDist q y ≤ 1) ∧
        q ∈ ((H0.locRH T Z0).step j).OmegaDD ∧
        CubeSub (S := S0) (n := n0) S0.M T (j + 1) q
          (((H0.locRH T Z0).localHistory S0.M T (j + 1) C).Z (j + 1)) ∧
        q ∈ lhOmegaSim ((H0.locRH T Z0).localHistory S0.M T (j + 1) C) (j + 1) (j + 1) ∧
        ∃ x : Torus S0.d (S0.M * n0 T * S0.L ^ T), cubeMap n0 S0.L S0.M T (j + 1) x = q ∧
          (⟨j + 1, jBlock S0.d S0.L (S0.M * n0 T) T (j + 1) x⟩ : BlockPt S0 n0 S0.M T) ∈
            genBlocksIn (chiDomGen (H0.locRH T Z0) g0 (j + 1) C) (j + 1) (nbhd 1 {q}) := by
  have hk1 := hW0.k1_pos hkK0
  have hqk := RegionHistory.k1_le hW0
  obtain ⟨u, hu, -⟩ := deepA (S0.k1 T) hk1 hqk
  obtain ⟨w, hw⟩ := exists_out0 (S0.k1 T) hW0.core_k1
  obtain ⟨j, hjT, C, hC, q, hq, y, hy, hd, hΩ⟩ := aux_scale (S0.k1 T) hk1 hqk u w hu hw
  have hΩ' := ((H0.locRH T Z0).step j).OmegaDD_subset_Omega hΩ
  obtain ⟨hZ, hsim⟩ := cube_conditions_of_mem_Omega (M := S0.M) (H0.locRH T Z0) hjT C hq hΩ'
  have hN : 0 < S0.L ^ (j + 1) * S0.M := by
    have := NeZero.ne S0.L; have := NeZero.ne S0.M; positivity
  obtain ⟨x, hx⟩ := Balaban.exists_blockMap_eq
    (fine_eq (M := S0.M) (H0.locRH T Z0).F.hnn hjT) hN q
  have hxq : cubeMap n0 S0.L S0.M T (j + 1) x = q := hx
  refine ⟨j, hjT, C, hC, q, hq, ⟨y, hy, hd⟩, hΩ, hZ, hsim, x, hxq, ?_⟩
  exact topBlock_mem_genBlocksIn (H0.locRH T Z0) g0 hjT C
    (by rw [hxq]; exact mem_nbhd.mpr ⟨_, hq, by simp [supDist_self]⟩)
    (by rw [hxq]; exact fun _ => hΩ') (by rw [hxq]; simp [supDist_self])

end Balaban.Inhabited.RipeGeo
