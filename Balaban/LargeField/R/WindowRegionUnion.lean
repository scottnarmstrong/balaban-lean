/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowRegion

/-!
# The pieces of the window are pairwise disjoint and cover `Z ∖ Z_{k₁}` (blocker 4, item S2)

* `piece_sites_disjoint_same`, `piece_sites_disjoint_lt`: the site sets `X_c` of two different pieces
  `(j, c) ≠ (j', c')` are disjoint (stated for the cube conditions of `mem_Xfine_cast_iff`);
* `exists_piece_of_mem_diff`: every site of `Z ∖ Z_{k₁}` lies in the site set of a piece `(j, c)`,
  `k₁ ≤ j ≤ m'`, `c` an ancestor of `Z` at scale `j + 1`;
* `exists_region_window`: the union of the pieces is the site set of a `Region` of the window generating set,
  and the site set is `Z ∖ Z_{k₁}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.LargeField.ActionConv

section Union

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

/-- Two different ancestors at the same scale have no common site. -/
theorem piece_sites_disjoint_same {j : ℕ} {c c' : H.Comp (j + 1)} (hne : c ≠ c')
    {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) (hx' : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c'.1) :
    False :=
  hne (Subtype.ext (comp_eq_of_mem c.2 c'.2 hx hx'))

/-- A site of the piece `(j, c)` is not a site of a piece `(j', c')` with `j < j'`. -/
theorem piece_sites_disjoint_lt (hmK : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} {j j' : ℕ} (hjj : j < j')
    (hj' : j' ≤ m') {c : H.Comp (j + 1)} {c' : H.Comp (j' + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    (hc' : c' ∈ H.ancFin (j' + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hy1 : cubeMap n S.L M (m' + 1) (j' + 1) x ∈ c'.1)
    (hy2 : cubeMap n S.L M (m' + 1) j' x ∉ H.lin j' (j' + 1) c') : False := by
  have h1 := cube_mem_lin_succ hmK hc (show j ≤ m' by omega) hx1
  have h2 := locFine_mono (H := H) (Z := Z) (M := M) hmK (show j + 1 ≤ j' by omega) (by omega) h1
  exact not_mem_locFine_of_not_mem_lin hmK hc' hj' hy1 hy2 h2

/-- Every site of `Z ∖ Z_{k₁}` lies in a piece `(j, c)` with `k₁ ≤ j ≤ m'`. -/
theorem exists_piece_of_mem_diff {k1 : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hk1 : k1 ≤ m')
    {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hxZ : x ∈ H.locFine Z M (m' + 1))
    (hxk1 : x ∉ H.locFine Z M k1) :
    ∃ j, k1 ≤ j ∧ j ≤ m' ∧ ∃ c : H.Comp (j + 1), c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
      cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1 ∧ cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c := by
  classical
  have hex : ∃ i, k1 < i ∧ x ∈ H.locFine Z M i := ⟨m' + 1, by omega, hxZ⟩
  set i0 := Nat.find hex with hi0
  obtain ⟨hi0k, hi0x⟩ := Nat.find_spec hex
  rw [← hi0] at hi0k hi0x
  have hi0le : i0 ≤ m' + 1 := Nat.find_min' hex ⟨by omega, hxZ⟩
  obtain ⟨j, hj⟩ : ∃ j, i0 = j + 1 := ⟨i0 - 1, by omega⟩
  have hnotj : x ∉ H.locFine Z M j := by
    by_cases hjk : j = k1
    · rw [hjk]; exact hxk1
    · intro hxj
      exact Nat.find_min hex (show j < i0 by omega) ⟨by omega, hxj⟩
  rw [hj] at hi0x
  rw [mem_locFine_iff_lin hmK (by omega)] at hi0x
  obtain ⟨c, hd, hxc⟩ := mem_lin.mp (Finset.mem_coe.mp hi0x)
  refine ⟨j, by omega, by omega, c, mem_ancFin.mpr hd, hxc, fun hl => hnotj ?_⟩
  obtain ⟨Y, hY, hxY⟩ := mem_lin.mp hl
  rw [mem_locFine_iff_lin hmK (by omega)]
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨Y, hY.trans hd, hxY⟩)

/-- **The window region** (blocker 4, item S2): the union of the cast site sets `X_c` of the pieces `(j, c)`,
`k₁ ≤ j ≤ m'`, is the site set `Z ∖ Z_{k₁}` of a `Region` of the window generating set. -/
theorem exists_region_window {k1 : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M) (hmK : m' + 1 ≤ K)
    (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i) (hk1p : 1 ≤ k1) (hk1m : k1 ≤ m')
    {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : W.Hyp)
    (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1) :
    ∃ D : Region (W.windowGenSet hWh), D.sites = W.Z \ W.Zk1 ∧
      ∀ x, x ∈ D.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
        c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
          torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 := by
  classical
  have hiff : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)), x ∈ W.Z \ W.Zk1 ↔
      ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1), c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 := by
    intro x
    constructor
    · intro hx
      rw [Finset.mem_sdiff, hWZ, hWZk1, mem_locFineFin, mem_locFineFin] at hx
      obtain ⟨j, hj1, hj2, c, hc, hx1, hx2⟩ := exists_piece_of_mem_diff hmK hk1m hx.1 hx.2
      exact ⟨j, ⟨hj1, hj2⟩, c, hc, (mem_Xfine_cast_iff g hmK hj2 c (by omega) x).mpr ⟨hx1, hx2⟩⟩
    · rintro ⟨j, hj, c, hc, hx⟩
      obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hmK hj.2 c (by omega) x).mp hx
      exact window_site_mem_diff hmK hj.1 hj.2 W hWZ hWZk1 hc hx1 hx2
  have hpiece : ∀ x ∈ W.Z \ W.Zk1, ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 :=
    fun x hx => (hiff x).mp hx
  refine ⟨⟨W.Z \ W.Zk1, ?_, ?_⟩, rfl, hiff⟩
  · intro x hx
    obtain ⟨j, hj, c, hc, hxX⟩ := hpiece x hx
    obtain ⟨D, hD, -⟩ := exists_region_Xfine_window (j := j) g hmK hL hR hk1p hj.1 hj.2 (by omega) W hWh hWfull
      hWZ hWZk1 hc
    exact D.sub_Ω ((hD x).mpr hxX)
  · intro x hx y hy
    obtain ⟨j, hj, c, hc, hxX⟩ := hpiece x hx
    obtain ⟨D, hD, -⟩ := exists_region_Xfine_window (j := j) g hmK hL hR hk1p hj.1 hj.2 (by omega) W hWh hWfull
      hWZ hWZk1 hc
    have hyD := D.blockClosed x ((hD x).mpr hxX) y hy
    obtain ⟨hy1, hy2⟩ := (mem_Xfine_cast_iff g hmK hj.2 c (by omega) y).mp ((hD y).mp hyD)
    exact window_site_mem_diff hmK hj.1 hj.2 W hWZ hWZk1 hc hy1 hy2

end Union

end Balaban.LargeField
