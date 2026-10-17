/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidDataInst
public import Balaban.LargeField.R.RRemovedHidBridgeStep

/-!
# The sites of a piece of the window (blocker 4, item S2 of `notes/phase1/LF4R-PLAN.md` §9)

For a ripe component `Z` of scale `m' + 1`, an ancestor `c` of `Z` at scale `j + 1` with `k₁ ≤ j ≤ m'` and the
localized history `H.locRH (j + 1) c`, the sites `X_{c}` (`Xfine`) of the piece `(j, c)` of the window, read on
the level-`(m'+1)` torus through `torusCast`:

* `mem_Xfine_cast_iff`: a site is in `X_c` iff its `(j+1)`-cube is in `c` and its `j`-cube is not in `Lin_j(c)`;
* `cube_mem_lin_of_mem_lin_anc`: a `j`-cube of the lineage of `Z` whose `(j+1)`-cube is in `c` is in `Lin_j(c)`;
* `Xfine_cast_mem_diff`: such a site lies in `Z ∖ Z_{k₁}` (the fine sets of the window);
* `Xfine_cast_layer`: its layer in the full piece of the window is `j + 1` or `j`, according to the output of step `j`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory

section Geom

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ}

/-- The level-`(j+1)` torus of a piece and the level-`(m'+1)` torus of the window have the same size. -/
theorem piece_torus_eq (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K)
    (hj : j ≤ m') :
    M * n (m' + 1) * S.L ^ (m' + 1) = g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1) := by
  have h1 := nn_eq_pow' (fun i hi => hnn i (lt_of_lt_of_le hi hmK)) (show j + 1 ≤ m' + 1 by omega)
  have h2 : S.L ^ (m' + 1) = S.L ^ (m' + 1 - (j + 1)) * S.L ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  have hM : M = g.c * g.M1 := g.hM
  rw [h1, h2]
  nth_rewrite 1 [hM]
  ring

theorem blockMap_castSite_cube (g : Geo S n R M) {b : ℕ} (hT : M * n (m' + 1) * S.L ^ (m' + 1) = b) (q : ℕ)
    (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) :
    blockMap (S.L ^ q * (g.c * g.M1)) (n q) (torusCast hT x) = cubeMap n S.L M (m' + 1) q x := by
  rw [torusCast_blockMap, cubeMap, show g.c * g.M1 = M from g.hM.symm]

/-- A `j`-cube of the lineage of `Z` whose `(j+1)`-cube lies in an ancestor `c` of `Z` lies in the lineage of
`c`. -/
theorem cube_mem_lin_of_anc (hmK : m' + 1 ≤ K) (hj : j ≤ m') {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∈ H.lin j (m' + 1) Z) :
    cubeMap n S.L M (m' + 1) j x ∈ H.lin j (j + 1) c := by
  obtain ⟨Y, hd, hxY⟩ := mem_lin.mp hx2
  obtain ⟨W, h1, h2⟩ := Desc.split (show j ≤ j + 1 by omega) (show j + 1 ≤ m' + 1 by omega) hd
  have hW : cubeMap n S.L M (m' + 1) (j + 1) x ∈ W.1 :=
    cubeMap_mem_of_desc' (hnn_k H hmK) (show j + 1 ≤ m' + 1 by omega) h1 hxY
  have hWc : W = c := Subtype.ext (comp_eq_of_mem W.2 c.2 hW hx1)
  subst hWc
  exact mem_lin.mpr ⟨Y, h1, hxY⟩

/-- Membership in `X_c` of the cast of a site of the level-`(m'+1)` torus, in terms of its cubes. -/
theorem mem_Xfine_cast_iff (g : Geo S n R M) (hmK : m' + 1 ≤ K) (hj : j ≤ m') (c : H.Comp (j + 1))
    (hK : j + 1 ≤ K) (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) :
    torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 ↔
      cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1 ∧
        cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c := by
  classical
  unfold Xfine
  rw [Finset.mem_sdiff, mem_fineK1, mem_fineK, blockMap_castSite_cube, blockMap_castSite_cube,
    locRH_Z c (Nat.le_succ j) (by omega)]
  simp only [Finset.mem_coe]

section Facts

theorem cube_mem_lin_succ (hmK : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hj : j ≤ m') (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) :
    x ∈ H.locFine Z M (j + 1) := by
  rw [mem_locFine_iff_lin hmK (show j + 1 ≤ m' + 1 by omega)]
  exact Finset.mem_coe.mpr (mem_lin.mpr ⟨c, mem_ancFin.mp hc, hx1⟩)

theorem cube_mem_locFine_top (hmK : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) :
    x ∈ H.locFine Z M (m' + 1) := by
  rw [mem_locFine_k hmK]
  exact cubeMap_mem_of_desc' (hnn_k H hmK) le_rfl (mem_ancFin.mp hc) hx1

theorem not_mem_locFine_of_not_mem_lin (hmK : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hj : j ≤ m') (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) : x ∉ H.locFine Z M j := by
  intro h
  rw [mem_locFine_iff_lin hmK (show j ≤ m' + 1 by omega)] at h
  exact hx2 (cube_mem_lin_of_anc hmK hj hc hx1 (Finset.mem_coe.mp h))

theorem not_mem_locFine_k1 (hmK : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} {k1 : ℕ} (hk1j : k1 ≤ j) (hj : j ≤ m')
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) : x ∉ H.locFine Z M k1 := fun h =>
  not_mem_locFine_of_not_mem_lin hmK hc hj hx1 hx2 (locFine_mono hmK hk1j (by omega) h)

theorem mem_locGen_j (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hj1 : 1 ≤ j) (hj : j ≤ m') (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) :
    x ∈ (H.locGen Z M hmK hL hR).Ω j := by
  by_contra h
  exact not_mem_locFine_of_not_mem_lin hmK hc hj hx1 hx2
    (compl_Omega_subset (hkK := hmK) (hL := hL) (hR := hR) hj1 (by omega) h)

theorem not_mem_locGen_j2 (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hj : j ≤ m') (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) :
    x ∉ (H.locGen Z M hmK hL hR).Ω (j + 2) := by
  rcases Nat.lt_or_ge j m' with h | h
  · exact locFine_not_mem_Omega (hkK := hmK) (hL := hL) (hR := hR) (show j + 1 < m' + 1 by omega)
      (cube_mem_lin_succ hmK hc hj hx1)
  · intro hx
    rw [mem_locGen] at hx
    omega

theorem mem_locGen_succ_iff (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i) {Z : H.Comp (m' + 1)} {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hj : j ≤ m') (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) :
    x ∈ (H.locGen Z M hmK hL hR).Ω (j + 1) ↔ cubeMap n S.L M (m' + 1) (j + 1) x ∈ (H.step j).Omega := by
  rw [mem_locGen_succ (show j < m' + 1 by omega), mem_locOmega_iff' hmK Z (show j < m' + 1 by omega)]
  have : cubeMap n S.L M (m' + 1) (j + 1) x ∈ ((H.lin (j + 1) (m' + 1) Z : Finset _) : Set _) :=
    Finset.mem_coe.mpr (mem_lin.mpr ⟨c, mem_ancFin.mp hc, hx1⟩)
  simp [this]

end Facts

end Geom

end Balaban.LargeField
