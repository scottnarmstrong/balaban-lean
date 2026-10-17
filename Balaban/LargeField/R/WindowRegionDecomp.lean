/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowRegionUnion
public import Balaban.LargeField.R.RRemovedHidDataInst

/-!
# The window region of `cancellation_identity` from the history (blocker 4, item S2)

`window_region_decomp`: the region `D = Z ∖ Z_{k₁}` of the window generating set (`exists_region_window`) is
`D₀ ∪ D_ω ∪ ⋃_{z ∈ Zb} fib z`, where `Zb` is the image of the top Gaussian blocks outside `Z₀`, `D₀` the sites of
`D` over `Z₀`, `D_ω` the other sites of `D` of layer `m' + 1`, with the layer bounds of the fibres and the
separation `D ∩ Z_{k₁} = ∅`, `D ∪ Z_{k₁} = Z`, `Z_{k₁}` over the box.  These are the hypotheses `hD`, `hD0ω`,
`hDr`, `hZr`, `hZd`, `hD0Z`, `hZk1Z`, `hZb` and the layer part of `hDω` of `cancellation_identity`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.LargeField.ActionConv

section Decomp

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ}

/-- The block of scale `m' + 1` of a site is a Gaussian block of the top step iff its cube is in `Z` and the site is
not in `Ω_{m'+1}` of the localized generating set. -/
theorem gauss_iff_site (hmK : m' + 1 ≤ K) (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    {Z : H.Comp (m' + 1)} (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) :
    jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hmK).symm x) ∈
        gaussBlocks (H.localHistory M K (m' + 1) Z) m' ↔
      cubeMap n S.L M (m' + 1) (m' + 1) x ∈ Z.1 ∧ x ∉ (H.locGen Z M hmK hL hR).Ω (m' + 1) := by
  have hxy := (blockCube_castSite H.F.hnn hmK hmK x).symm
  rw [gaussBlocks_iff_locGen hmK hmK (Nat.lt_succ_self m') hL hR (mem_ancFin.mpr (Desc.refl Z)) _ x hxy,
    blockCube_castSite H.F.hnn hmK hmK x]
  simp only [Finset.mem_coe]

open Classical in
/-- **The window region of `cancellation_identity` from the history.**  Let `Z` be a ripe component, `Wp` the window
pieces with the layers of `𝔹_k` (`hWfull`) and the regions `Z`, `Z_{k₁}` (`hWZ`, `hWZk1`; definitional for
`windowOfHistory`), `Z₀` the box blocks (`hZ0box`, `hBx`), `Zb` the top Gaussian blocks outside `Z₀` (`hZb`).  Then
the region `D = Z ∖ Z_{k₁}` of `exists_region_window` splits as `D₀ ∪ D_ω ∪ ⋃_{z ∈ Zb} fib z`. -/
theorem window_region_decomp {k1 : ℕ} {Z : H.Comp (m' + 1)} (hMS : M = S.M) (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (h3 : 8 ≤ S.L * S.lateR (m' + 1)) (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hk1def : S.k1 (m' + 1) = k1) (g : Geo S n R M) {ϱ : ℝ}
    (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : Wp.Hyp)
    (hWfull : ∀ q, Wp.full.Ω q = (H.locGen Z M hmK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω q)
    (hWZ : Wp.Z = H.locFineFin Z (m' + 1)) (hWZk1 : Wp.Zk1 = H.locFineFin Z k1)
    (Z0 : Set (BlockAt S n M K (m' + 1)))
    (Bx : Set (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
    (hZ0box : ∀ s : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      torusCast (congrArg (· * n (m' + 1)) hMS)
        (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) s) ∈ H.Zzero (m' + 1) Z →
        jBlock S.d S.L (M * n K) K (m' + 1) (torusCast (fine_eq_top H.F.hnn hmK).symm s) ∈ Z0)
    (hBx : ∀ y : BlockAt S n M K (m' + 1), y ∈ Z0 ↔
      torusCast (blk_eq_top H.F.hnn hmK (le_refl (m' + 1))).symm y ∈ Bx)
    (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
    (hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1),
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ y ∉ Z0 ∧
        zb = torusCast (blk_eq_top H.F.hnn hmK (le_refl (m' + 1))).symm y) :
    ∃ (D : Region (Wp.windowGenSet hWh))
      (D0 Dω : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)))),
      D.sites = Wp.Z \ Wp.Zk1 ∧
      D.sites = D0 ∪ Dω ∪ Zb.biUnion (fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1)) ∧
      Disjoint D0 Dω ∧
      Disjoint (D0 ∪ Dω) (Zb.biUnion (fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1))) ∧
      (∀ x ∈ D0, jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ Bx) ∧
      (∀ x ∈ Dω, (Wp.windowGenSet hWh).layerIndex x = m' + 1) ∧
      (∀ z ∈ Zb, ∀ x ∈ fib S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) z,
        1 ≤ (Wp.windowGenSet hWh).layerIndex x ∧ (Wp.windowGenSet hWh).layerIndex x < m' + 1) ∧
      D.sites ∪ Wp.Zk1 = Wp.Z ∧ Disjoint D.sites Wp.Zk1 ∧
      (∀ x ∈ Wp.Zk1, jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ Bx) := by
  subst hMS
  have hnn := H.F.hnn
  have hL : 2 ≤ S.L := H.F.ok.two_le_L
  have hR : ∀ j, 1 ≤ j → j < m' + 1 → S.Rb ≤ R j := fun j _ _ => g.hRlow j
  have hk1p : 1 ≤ k1 := hk1def ▸ hW.k1_pos hmK
  have hk1m : k1 ≤ m' := by
    have hq := hW.core_window.1
    have hq1 : S.k1 (m' + 1) = (H.bk (m' + 1) Z).q := hW.core_k1
    have : 1 ≤ S.nq (H.bk (m' + 1) Z).q := by unfold Setting.nq; omega
    omega
  have hZk1 : ∀ x : Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1)), x ∈ H.locFine Z S.M k1 →
      jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x) ∈ Z0 := by
    intro x hx
    exact hZ0box x (locFine_subset_fineZzero G h18 h3 hmK hW (x := x) (hk1def ▸ hx))
  obtain ⟨D, hDsites, -⟩ := exists_region_window g hmK hL hR hk1p hk1m Wp hWh hWfull hWZ hWZk1
  have hZsub : Wp.Zk1 ⊆ Wp.Z := by
    intro x hx
    rw [hWZk1, mem_locFineFin] at hx
    rw [hWZ, mem_locFineFin]
    exact locFine_mono hmK (by omega) le_rfl hx
  have hwin : ∀ x ∈ Wp.Z \ Wp.Zk1, ∀ q, x ∈ (Wp.windowGenSet hWh).Ω q ↔
      x ∈ (H.locGen Z S.M hmK hL hR).Ω q := fun x hx q => by
    rw [windowGenSet_mem_iff_full Wp hWh hx (Finset.mem_sdiff.mp hx).1, hWfull]
  have hbox : ∀ x : Torus S.d (S.M * n (m' + 1) * S.L ^ (m' + 1)),
      jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x) ∈ Z0 →
        jBlock S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ Bx := fun x hx => by
    have h1 := (mem_fib_cast hnn hmK (le_refl (m' + 1))
      (jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x)) x).mpr rfl
    rw [mem_fib] at h1
    have h2 := (hBx _).mp hx
    rw [← h1] at h2
    exact h2
  -- the sites of `D` of layer `< m' + 1` are Gaussian sites, and conversely
  have hgauss : ∀ x ∈ Wp.Z \ Wp.Zk1, (Wp.windowGenSet hWh).layerIndex x < m' + 1 →
      jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x) ∈
        gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' := by
    intro x hx hlt
    have hxΩ : x ∈ (Wp.windowGenSet hWh).Ω 1 := by
      have := D.sub_Ω (show x ∈ D.sites by rw [hDsites]; exact hx)
      exact this
    obtain ⟨-, -, hl⟩ := (Wp.windowGenSet hWh).layerIndex_spec hxΩ
    have hxl := (GeneratingSet.mem_layer _).mp hl
    refine (gauss_iff_site hmK hL hR x).mpr ⟨?_, fun hΩ => hxl.2 ?_⟩
    · have := (Finset.mem_sdiff.mp hx).1
      rw [hWZ, mem_locFineFin, mem_locFine_k hmK] at this
      exact this
    · rw [← hwin x hx] at hΩ
      exact (Wp.windowGenSet hWh).Ω_antitone (by omega) (by omega) (by omega) hΩ
  have hfib : ∀ z ∈ Zb, ∀ x ∈ fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) z,
      x ∈ Wp.Z \ Wp.Zk1 ∧ jBlock S.d S.L (S.M * n K) K (m' + 1)
        (torusCast (fine_eq_top hnn hmK).symm x) ∉ Z0 ∧
      jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x) ∈
        gaussBlocks (H.localHistory S.M K (m' + 1) Z) m' ∧
      x ∉ (H.locGen Z S.M hmK hL hR).Ω (m' + 1) := by
    intro z hz x hx
    obtain ⟨y, hyg, hy0, rfl⟩ := (hZb z).mp hz
    have hxy := (mem_fib_cast hnn hmK (le_refl (m' + 1)) y x).mp hx
    rw [hxy]
    have hg := (gauss_iff_site hmK hL hR (Z := Z) x)
    rw [hxy] at hg
    obtain ⟨hZx, hΩ⟩ := hg.mp hyg
    refine ⟨?_, hy0, hyg, hΩ⟩
    rw [Finset.mem_sdiff, hWZ, hWZk1, mem_locFineFin, mem_locFineFin, mem_locFine_k hmK]
    refine ⟨hZx, fun hk => hy0 ?_⟩
    have := hZk1 x hk
    rwa [hxy] at this
  have hlayer : ∀ z ∈ Zb, ∀ x ∈ fib S.d S.L (S.M * n (m' + 1)) (m' + 1) (m' + 1) z,
      1 ≤ (Wp.windowGenSet hWh).layerIndex x ∧ (Wp.windowGenSet hWh).layerIndex x < m' + 1 := by
    intro z hz x hx
    obtain ⟨hxd, -, -, hΩ⟩ := hfib z hz x hx
    have hxΩ : x ∈ (Wp.windowGenSet hWh).Ω 1 := D.sub_Ω (show x ∈ D.sites by rw [hDsites]; exact hxd)
    obtain ⟨h1, h2, hl⟩ := (Wp.windowGenSet hWh).layerIndex_spec hxΩ
    refine ⟨h1, lt_of_le_of_ne h2 fun heq => hΩ ?_⟩
    have := ((GeneratingSet.mem_layer _).mp hl).1
    rw [heq, hwin x hxd] at this
    exact this
  refine ⟨D, D.sites.filter (fun x => jBlock S.d S.L (S.M * n K) K (m' + 1)
      (torusCast (fine_eq_top hnn hmK).symm x) ∈ Z0),
    D.sites.filter (fun x => jBlock S.d S.L (S.M * n K) K (m' + 1)
      (torusCast (fine_eq_top hnn hmK).symm x) ∉ Z0 ∧ (Wp.windowGenSet hWh).layerIndex x = m' + 1),
    hDsites, ?_, ?_, ?_, ?_, ?_, hlayer, ?_, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro hx
      by_cases h0 : jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x) ∈ Z0
      · exact Or.inl (Or.inl ⟨hx, h0⟩)
      · by_cases hl : (Wp.windowGenSet hWh).layerIndex x = m' + 1
        · exact Or.inl (Or.inr ⟨hx, h0, hl⟩)
        · have hxd : x ∈ Wp.Z \ Wp.Zk1 := by rw [← hDsites]; exact hx
          have hxΩ : x ∈ (Wp.windowGenSet hWh).Ω 1 := D.sub_Ω hx
          have hle := ((Wp.windowGenSet hWh).layerIndex_spec hxΩ).2.1
          have hg := hgauss x hxd (lt_of_le_of_ne hle hl)
          refine Or.inr ⟨torusCast (blk_eq_top hnn hmK (le_refl (m' + 1))).symm
            (jBlock S.d S.L (S.M * n K) K (m' + 1) (torusCast (fine_eq_top hnn hmK).symm x)),
            (hZb _).mpr ⟨_, hg, h0, rfl⟩, ?_⟩
          exact (mem_fib_cast hnn hmK (le_refl (m' + 1)) _ x).mpr rfl
    · rintro ((⟨hx, -⟩ | ⟨hx, -⟩) | ⟨z, hz, hx⟩)
      · exact hx
      · exact hx
      · rw [hDsites]; exact (hfib z hz x hx).1
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    exact hx'.2.1 hx.2
  · rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.mp hx'
    obtain ⟨-, hn0, -, -⟩ := hfib z hz x hxz
    have hlt := (hlayer z hz x hxz).2
    simp only [Finset.mem_union, Finset.mem_filter] at hx
    rcases hx with hx | hx
    · exact hn0 hx.2
    · omega
  · intro x hx
    exact hbox x (Finset.mem_filter.mp hx).2
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.2
  · rw [hDsites]
    exact Finset.sdiff_union_of_subset hZsub
  · rw [hDsites]
    exact Finset.sdiff_disjoint
  · intro x hx
    rw [hWZk1, mem_locFineFin] at hx
    exact hbox x (hZk1 x hx)

end Decomp

end Balaban.LargeField
