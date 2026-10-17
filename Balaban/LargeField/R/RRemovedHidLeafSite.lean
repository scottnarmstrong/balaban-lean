/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidLeaf
public import Balaban.LargeField.R.RRemovedChainRead
public import Balaban.LargeField.R.ZeroDomainB

/-!
# The sites of the Gaussian region of the window and their leaves (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  Site-level geometry of the localized history `H.locGen Z M …` (the layers
of the window on `Z ∖ Z_{k₁}`) against the Gaussian blocks of the ancestors: for a site `x` that is in `Z`, not in
`Z_{k₁}`, and not in `Ω_{m'+1}`, with `n = layerIndex x`: `k₁ ≤ n ≤ m'`, the blocks of `x` of the scales
`n + 1, …, m' + 1` are nodes and the block of scale `n` is not a node.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section Site

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

theorem locFine_of_not_mem_locGen (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {j : ℕ} (hj : j + 1 ≤ m' + 1)
    {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : x ∉ (H.locGen Z M hmK hL hR).Ω (j + 1)) : x ∈ H.locFine Z M (j + 1) := by
  rw [mem_locGen] at hx
  have hc : cubeMap n S.L M (m' + 1) (j + 1) x ∉
      ((H.locRH (m' + 1) Z).toSeq hmK (fun _ => rfl)).OmegaAt (j + 1) := fun h => hx ⟨hj, h⟩
  exact (RegionSeq.OmegaAt_compl_subset_Z _ j) hc

theorem fine_eq_top (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) :
    M * n K * S.L ^ K = M * n (m' + 1) * S.L ^ (m' + 1) := by
  rw [fine_eq (M := M) hnn hmK]; ring

theorem cubeMap_castSite (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) (j : ℕ)
    (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) :
    cubeMap n S.L M K j (torusCast (fine_eq_top (M := M) hnn hmK).symm x) =
      cubeMap n S.L M (m' + 1) j x := by
  unfold cubeMap
  exact Balaban.LargeField.blockMap_torusCast _ _ _ _

theorem blockCube_castSite (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K) {j : ℕ}
    (hj : j ≤ K) (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) :
    blockCube S n M K j (jBlock S.d S.L (M * n K) K j
      (torusCast (fine_eq_top (M := M) hnn hmK).symm x)) = cubeMap n S.L M (m' + 1) j x := by
  rw [cubeMap_jBlock hnn hj, cubeMap_castSite hnn hmK]

theorem mem_locGen_of_not_locFine (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {k1 : ℕ} (hk1p : 1 ≤ k1)
    (hk1 : k1 ≤ m') {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : x ∉ H.locFine Z M k1) : x ∈ (H.locGen Z M hmK hL hR).Ω k1 := by
  by_contra h
  obtain ⟨j, rfl⟩ : ∃ j, k1 = j + 1 := ⟨k1 - 1, by omega⟩
  exact hx (locFine_of_not_mem_locGen hmK hL hR (by omega) h)

theorem nd_block_of_not_mem (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K)
    (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {k1 : ℕ}
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    {j : ℕ} (hk1 : k1 ≤ j) (hj : j ≤ m') {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : x ∉ (H.locGen Z M hmK hL hR).Ω (j + 1)) :
    nd ⟨j + 1, jBlock S.d S.L (M * n K) K (j + 1) (torusCast (fine_eq_top hnn hmK).symm x)⟩ := by
  have hjK : j + 1 ≤ K := by omega
  have hxl := locFine_of_not_mem_locGen hmK hL hR (by omega : j + 1 ≤ m' + 1) hx
  rw [mem_locFine_iff_lin hmK (by omega : j + 1 ≤ m' + 1)] at hxl
  obtain ⟨c, hc, hxc⟩ := mem_lin.mp (Finset.mem_coe.mp hxl)
  refine (hnd j _).mpr ⟨hk1, hj, c, mem_ancFin.mpr hc, ?_⟩
  exact (gaussBlocks_iff_locGen hjK hmK (by omega) hL hR (mem_ancFin.mpr hc) _ x
    (blockCube_castSite hnn hmK hjK x).symm).mpr ⟨by rwa [blockCube_castSite hnn hmK hjK x], hx⟩

theorem not_nd_block_of_mem (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K)
    (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j) {Z : H.Comp (m' + 1)} {k1 : ℕ}
    (hk1p : 1 ≤ k1) (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    {q : ℕ} (hk1 : k1 ≤ q) (hq : q ≤ m' + 1) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : x ∈ (H.locGen Z M hmK hL hR).Ω q) :
    ¬ nd ⟨q, jBlock S.d S.L (M * n K) K q (torusCast (fine_eq_top hnn hmK).symm x)⟩ := by
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  intro h
  obtain ⟨h1, h2, c, hc, hg⟩ := (hnd j _).mp h
  have hjK : j + 1 ≤ K := by omega
  have := (gaussBlocks_iff_locGen hjK hmK (by omega) hL hR hc _ x
    (blockCube_castSite hnn hmK hjK x).symm).mp hg
  exact this.2 hx

end Site

end Balaban.LargeField
