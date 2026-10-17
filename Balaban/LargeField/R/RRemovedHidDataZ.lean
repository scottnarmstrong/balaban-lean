/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeafWindow
public import Balaban.LargeField.R.ZeroDomainScales
public import Balaban.LargeField.R.ZeroDomain

/-!
# `Z_{k₁} ⊆ Z₀` for the window of the history (W944)

`notes/phase1/LF4R-PLAN.md` §8.5.  `locFine_subset_fineZzero`: for a ripe window `H.RipeWindow (m'+1) Z` with core
`k₁ = S.k1 (m'+1)`, the fine set `Z_{k₁}` (`H.locFine Z S.M k₁`) lies in the fine set of `Z₀ = H.Zzero`: the core
is below `k₂` (`lateScale_geom`, Lemma III.3.2 (a)) and the lineage is compatible with coarsening
(`cubeMap_lin_coarsen`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section DataZ

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} [NeZero S.L] [NeZero S.M] {m' : ℕ}

theorem locFine_subset_fineZzero (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (h3 : 8 ≤ S.L * S.lateR (m' + 1)) (hmK : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hW : H.RipeWindow (m' + 1) Z) {x : Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : x ∈ H.locFine Z S.M (S.k1 (m' + 1))) :
    blockMap (S.L ^ (m' + 1)) (S.M * n (m' + 1)) x ∈ H.Zzero (m' + 1) Z := by
  have hq := hW.core_window.1
  obtain ⟨-, hq2, -, h23, h3k, -⟩ := G.lateScale_geom h18 hq hW.point.2.1 h3
  rw [← hW.core_k1] at hq2
  have hk1k : S.k1 (m' + 1) ≤ m' + 1 := by
    have := hW.core_window.1; rw [← hW.core_k1] at this; omega
  rw [mem_locFine_iff_lin hmK hk1k] at hx
  have hx' : cubeMap n S.L S.M K (S.k1 (m' + 1))
      (torusCast (fine_eq_top (M := S.M) H.F.hnn hmK).symm x) ∈
        ((H.lin (S.k1 (m' + 1)) (m' + 1) Z : Finset (Torus S.d (n (S.k1 (m' + 1))))) : Set _) := by
    rwa [cubeMap_castSite H.F.hnn hmK]
  have hco := cubeMap_lin_coarsen (H := H) hq2.le (h23.trans h3k) hmK hx'
  rw [cubeMap_castSite H.F.hnn hmK] at hco
  refine ⟨torusCast (fineSide_eq_mul (S := S) (n := n) (m' + 1)).symm x, ?_, ?_⟩
  · unfold zeroBlockOf
    exact Balaban.LargeField.blockMap_torusCast _ _ _ _
  · rw [← cubeMap_torusCast_fineSide (S := S) (n := n)]
    rw [torusCast_cast_symm]
    exact hco

end DataZ

end Balaban.LargeField
