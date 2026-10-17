/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowRegionGeom
public import Balaban.LargeField.R.PsiZeroWindowGeom

/-!
# The region of a piece of the window on the window generating set (blocker 4, item S2)

`exists_region_Xfine_window`: for a piece `(j, c)` of the window of a ripe component `Z` (an ancestor `c` of `Z`
at scale `j + 1`, `k₁ ≤ j ≤ m'`), the cast of the site set `X_c` (`Xfine`) to the level-`(m'+1)` torus is the site
set of a `Region` of the window generating set, and the layer index of the window generating set at each of its
sites is the layer index of `locGen` of the piece at the corresponding site.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.LargeField.ActionConv

section Region

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ}

theorem piece_block_eq (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hmK : m' + 1 ≤ K)
    (hj : j ≤ m') {q : ℕ} (hq : q ≤ j + 1) :
    M * n (m' + 1) * S.L ^ (m' + 1 - q) = g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1 - q) := by
  have hT := piece_torus_eq g hnn hmK hj
  have hpos : 0 < S.L ^ q := pow_pos (Nat.pos_of_ne_zero (NeZero.ne _)) q
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  have e1 : S.L ^ (m' + 1 - q) * S.L ^ q = S.L ^ (m' + 1) := by
    rw [← pow_add]; congr 1; omega
  have e2 : S.L ^ (j + 1 - q) * S.L ^ q = S.L ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  calc M * n (m' + 1) * S.L ^ (m' + 1 - q) * S.L ^ q
      = M * n (m' + 1) * (S.L ^ (m' + 1 - q) * S.L ^ q) := by ring
    _ = g.M1 * (g.c * n (j + 1)) * (S.L ^ (j + 1 - q) * S.L ^ q) := by rw [e1, e2]; exact hT
    _ = g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1 - q) * S.L ^ q := by ring

theorem window_site_mem_diff {k1 : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hk1j : k1 ≤ j) (hj : j ≤ m') {ϱ : ℝ}
    (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWZ : W.Z = H.locFineFin Z (m' + 1))
    (hWZk1 : W.Zk1 = H.locFineFin Z k1) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) : x ∈ W.Z \ W.Zk1 := by
  rw [Finset.mem_sdiff, hWZ, hWZk1, mem_locFineFin, mem_locFineFin]
  exact ⟨cube_mem_locFine_top hmK hc hx1, not_mem_locFine_k1 hmK hc hk1j hj hx1 hx2⟩

open Classical in
theorem windowGen_layerIndex_eq {k1 : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i) (hk1p : 1 ≤ k1) (hk1j : k1 ≤ j) (hj : j ≤ m') {ϱ : ℝ}
    (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : W.Hyp)
    (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) :
    (W.windowGenSet hWh).layerIndex x =
      if cubeMap n S.L M (m' + 1) (j + 1) x ∈ (H.step j).Omega then j + 1 else j := by
  have hd := window_site_mem_diff hmK hk1j hj W hWZ hWZk1 hc hx1 hx2
  have hZ := (Finset.mem_sdiff.mp hd).1
  have hj1 : 1 ≤ j := by omega
  have hj2 := not_mem_locGen_j2 hmK hL hR hc hj hx1
  have hjΩ := mem_locGen_j hmK hL hR hc hj1 hj hx1 hx2
  have hsucc := mem_locGen_succ_iff hmK hL hR hc hj hx1
  split_ifs with h
  · refine (W.windowGenSet hWh).layerIndex_eq (by omega) (by omega) ?_
    rw [GeneratingSet.mem_layer, windowGenSet_mem_iff_full W hWh hd hZ, windowGenSet_mem_iff_full W hWh hd hZ,
      hWfull, hWfull]
    exact ⟨hsucc.mpr h, hj2⟩
  · refine (W.windowGenSet hWh).layerIndex_eq hj1 (by omega) ?_
    rw [GeneratingSet.mem_layer, windowGenSet_mem_iff_full W hWh hd hZ, windowGenSet_mem_iff_full W hWh hd hZ,
      hWfull, hWfull]
    exact ⟨hjΩ, fun h' => h (hsucc.mp h')⟩

theorem piece_top_iff (g : Geo S n R M) (hmK : m' + 1 ≤ K) (hj : j ≤ m') (hK : j + 1 ≤ K)
    {c : H.Comp (j + 1)} {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) :
    torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω (j + 1) ↔
      cubeMap n S.L M (m' + 1) (j + 1) x ∈ (H.step j).Omega := by
  have hxX := (mem_Xfine_cast_iff g hmK hj c hK x).mpr ⟨hx1, hx2⟩
  rw [locGen_Ω_top_iff g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK hxX, blockMap_castSite_cube,
    mem_locOmega_iff' hK c (Nat.lt_succ_self j)]
  have : cubeMap n S.L M (m' + 1) (j + 1) x ∈ ((H.lin (j + 1) (j + 1) c : Finset _) : Set _) := by
    rw [lin_self]; exact hx1
  simp [this]

open Classical in
theorem pieceGen_layerIndex_eq (g : Geo S n R M) (hmK : m' + 1 ≤ K) (hj1 : 1 ≤ j) (hj : j ≤ m')
    (hK : j + 1 ≤ K) {c : H.Comp (j + 1)} {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) :
    (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex
        (torusCast (piece_torus_eq g H.F.hnn hmK hj) x) =
      if cubeMap n S.L M (m' + 1) (j + 1) x ∈ (H.step j).Omega then j + 1 else j := by
  have hxX := (mem_Xfine_cast_iff g hmK hj c hK x).mpr ⟨hx1, hx2⟩
  have hjΩ := locGen_Ω_k g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK hj1 hxX
  have htop := piece_top_iff g hmK hj hK hx1 hx2
  split_ifs with h
  · refine GeneratingSet.layerIndex_eq _ (by omega) (by omega) ?_
    rw [GeneratingSet.mem_layer]
    exact ⟨htop.mpr h, by rw [GeneratingSet.top]; exact Finset.notMem_empty _⟩
  · refine GeneratingSet.layerIndex_eq _ hj1 (by omega) ?_
    rw [GeneratingSet.mem_layer]
    exact ⟨hjΩ, fun h' => h (htop.mp h')⟩

open Classical in
/-- **The region of a piece of the window** (blocker 4, item S2).  For a piece `(j, c)` of the window of the
ripe component `Z` (`c` an ancestor of `Z` at scale `j + 1`, `k₁ ≤ j ≤ m'`), the cast of `X_c = Xfine …` is the
site set of a `Region` of the window generating set, and the layer index of the window generating set at a site of
it is the layer index of `locGen` of the piece at the cast site. -/
theorem exists_region_Xfine_window {k1 : ℕ} {Z : H.Comp (m' + 1)} (g : Geo S n R M) (hmK : m' + 1 ≤ K)
    (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i) (hk1p : 1 ≤ k1) (hk1j : k1 ≤ j)
    (hj : j ≤ m') (hK : j + 1 ≤ K) {ϱ : ℝ} (W : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : W.Hyp) (hWfull : ∀ q, W.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : W.Z = H.locFineFin Z (m' + 1)) (hWZk1 : W.Zk1 = H.locFineFin Z k1) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) :
    ∃ D : Region (W.windowGenSet hWh),
      (∀ x, x ∈ D.sites ↔
        torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1) ∧
      ∀ x ∈ D.sites, (W.windowGenSet hWh).layerIndex x =
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex
          (torusCast (piece_torus_eq g H.F.hnn hmK hj) x) := by
  have hj1 : 1 ≤ j := by omega
  have hmem : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 ↔
        cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1 ∧ cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c :=
    fun x => mem_Xfine_cast_iff g hmK hj c hK x
  have hlay : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 →
      (W.windowGenSet hWh).layerIndex x =
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex
          (torusCast (piece_torus_eq g H.F.hnn hmK hj) x) := fun x hx => by
    obtain ⟨hx1, hx2⟩ := (hmem x).mp hx
    rw [windowGen_layerIndex_eq hmK hL hR hk1p hk1j hj W hWh hWfull hWZ hWZk1 hc hx1 hx2,
      pieceGen_layerIndex_eq g hmK hj1 hj hK hx1 hx2]
  set sites : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) := Finset.univ.filter fun x =>
      torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1 with hsites
  have hsub : sites ⊆ (W.windowGenSet hWh).Ω 1 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := (hmem x).mp hx.2
    have hd := window_site_mem_diff hmK hk1j hj W hWZ hWZk1 hc hx1 hx2
    rw [windowGenSet_mem_iff_full W hWh hd (Finset.mem_sdiff.mp hd).1, hWfull]
    exact (H.locGen Z M hmK hL hR).Ω_antitone le_rfl hj1 (by omega)
      (mem_locGen_j hmK hL hR hc hj1 hj hx1 hx2)
  have hblk : ∀ x ∈ sites, ∀ y ∈ (W.windowGenSet hWh).blk ((W.windowGenSet hWh).layerIndex x) x,
      y ∈ sites := by
    intro x hx y hy
    rw [hsites, Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have hxX := hx.2
    obtain ⟨hx1, hx2⟩ := (hmem x).mp hxX
    have hd := window_site_mem_diff hmK hk1j hj W hWZ hWZk1 hc hx1 hx2
    have hxΩ : x ∈ (W.windowGenSet hWh).Ω 1 := by
      rw [windowGenSet_mem_iff_full W hWh hd (Finset.mem_sdiff.mp hd).1, hWfull]
      exact (H.locGen Z M hmK hL hR).Ω_antitone le_rfl hj1 (by omega)
        (mem_locGen_j hmK hL hR hc hj1 hj hx1 hx2)
    have hxΩ' : torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω 1 :=
      (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω_antitone le_rfl hj1 (by omega)
        (locGen_Ω_k g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK hj1 hxX)
    obtain ⟨hq1, hqk, hql⟩ := (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex_spec hxΩ'
    have hq := hlay x hxX
    rw [hq] at hy
    have hB := piece_block_eq g H.F.hnn hmK hj
      (q := (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).layerIndex
        (torusCast (piece_torus_eq g H.F.hnn hmK hj) x)) hqk
    have hyb := GeneratingSet.mem_blk.1 hy
    refine Xfine_blk g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK hj1 hxX hq1 hqk hql ?_
    rw [GeneratingSet.mem_blk, jBlock_torusCast (by omega) hqk (piece_torus_eq g H.F.hnn hmK hj) hB,
      jBlock_torusCast (by omega) hqk (piece_torus_eq g H.F.hnn hmK hj) hB, hyb]
  refine ⟨⟨sites, hsub, hblk⟩, fun x => ?_, fun x hx => hlay x (Finset.mem_filter.mp hx).2⟩
  show x ∈ sites ↔ _
  rw [hsites, Finset.mem_filter]
  simp

end Region

end Balaban.LargeField
