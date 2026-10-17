/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.WindowRegionDecomp
public import Balaban.LargeField.R.ActionConvReal

/-!
# The reference generating set `𝔹_k(U_k)` of the window: order, regions and block unions (blocker 4, W964)

`notes/phase1/LF4R-PLAN.md` §9.  Data of `window_quotient_of_history_gen` for the actual window
`W = windowOfHistory H Z g hkK hW` with `G₀ = W.windowGenSet` and `G = W.bdry`:

* `windowOfHistory_bdryCover`: `Z ⊆ Ω_k(𝔹_k(U_k))`;
* `WindowPieces.precedes_bdry`, `windowOfHistory_precedes`: `𝔹_{k₁,k} ≺ 𝔹_k(U_k)`;
* `windowOfHistory_hbZ`: `Z` is a union of `k`-blocks;
* `exists_region_bdry_Z`: a `Region` of `𝔹_k(U_k)` with sites `Z`, all in the layer `k` (`hlay'`);
* `exists_region_bdry_of_blockUnion`: a `Region` of `𝔹_k(U_k)` with the sites of a set that is a union of `k`-blocks.

The region `Z_{k₁}` is a union of `π_{k₁}`-cubes (side `M L^{k₁}`), not of `k`-blocks (side `L^k`,
`k - k₁ ≥ n_q(k₁)`): no `Region` of `𝔹_k(U_k)` has the sites `Z_{k₁}`; see the status line in
`LF4R-PLAN.md` §9.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.ActionConv

section Precedes

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **`𝔹_{k₁,k} ≺ 𝔹_k(U_k)`**: the window generating set is contained layerwise in the boundary piece, because
`Z_{k₁} ⊆ Z ⊆ Ω_k(𝔹_k(U_k))`. -/
theorem WindowPieces.precedes_bdry (W : WindowPieces d L N₀ k ϱ) (hW : W.Hyp) (hZ : W.Zk1 ⊆ W.Z)
    (hcov : ∀ x ∈ W.Z, x ∈ W.bdry.Ω k) : Precedes (W.windowGenSet hW) W.bdry := by
  intro i hi1 hik x hx
  rw [WindowPieces.windowGenSet_Ω] at hx
  have hZi : ∀ y ∈ W.Z, y ∈ W.bdry.Ω i := fun y hy =>
    W.bdry.Ω_antitone hi1 hik (by omega) (hcov y hy)
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact hZi x (hZ (Finset.mem_inter.mp h).2)
    · exact hZi x (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).1
  · exact (Finset.mem_inter.mp h).1

end Precedes

section History

open RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} (g : Geo S n R M) (hkK : k ≤ K)
  (hW : H.RipeWindow k Z)

/-- `Z ⊆ Ω_k(𝔹_k(U_k))` for the actual window. -/
theorem windowOfHistory_bdryCover :
    ∀ x ∈ (windowOfHistory H Z g hkK hW).Z, x ∈ (windowOfHistory H Z g hkK hW).bdry.Ω k := by
  intro x hx
  rw [windowOfHistory_Z, mem_locFineFin, mem_locFine_k hkK] at hx
  refine windowBdry_top_mem (g := g) ?_
  unfold bdryU thick
  exact subset_nbhd _ _ hx

/-- `Z` is a union of `m`-blocks, `1 ≤ m ≤ k`, for the actual window. -/
theorem windowOfHistory_hbZ :
    ∀ m, 1 ≤ m → m ≤ k → IsBlockUnion S.L (M * n k) k m (windowOfHistory H Z g hkK hW).Z := by
  intro m _ hm x x' h
  have hnn : ∀ i, i < k → n i = S.L * n (i + 1) := fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)
  show x ∈ H.locFineFin Z k ↔ x' ∈ H.locFineFin Z k
  rw [mem_locFineFin, mem_locFineFin, mem_locFine, mem_locFine,
    cubeMap_eq_of_jBlock_eq (hnn := hnn) hm le_rfl h]

/-- **`𝔹_{k₁,k} ≺ 𝔹_k(U_k)` for the actual window.** -/
theorem windowOfHistory_precedes :
    Precedes ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW))
      (windowOfHistory H Z g hkK hW).bdry :=
  WindowPieces.precedes_bdry _ _ (windowOfHistory_hZ (g := g) hkK hW)
    (windowOfHistory_bdryCover g hkK hW)

end History

section Regions

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- A set of sites of `Ω_k(G)` that is a union of `k`-blocks is the set of sites of a `Region` of `G` whenever its
sites are in the top layer `k`; this is the case for `G = 𝔹_k(U_k)` and all sites of `Z`. -/
theorem exists_region_of_top (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k)
    (X : Finset (Torus d (N₀ * L ^ k))) (hX : ∀ x ∈ X, x ∈ G.Ω k)
    (hbu : IsBlockUnion L N₀ k k X) :
    ∃ D : Region G, D.sites = X ∧ ∀ x ∈ D.sites, G.layerIndex x = k := by
  have hlay : ∀ x ∈ X, G.layerIndex x = k := fun x hx =>
    G.layerIndex_eq hk le_rfl (G.mem_layer.2 ⟨hX x hx, by rw [G.top]; simp⟩)
  refine ⟨⟨X, fun x hx => G.Ω_antitone le_rfl hk (by omega) (hX x hx), fun x hx y hy => ?_⟩, rfl, hlay⟩
  rw [hlay x hx] at hy
  exact (hbu y x (GeneratingSet.mem_blk.1 hy)).2 hx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {Z : H.Comp k} (g : Geo S n R M) (hkK : k ≤ K)
  (hW : H.RipeWindow k Z)

open RegionHistory in
/-- **The region `Z` of `𝔹_k(U_k)`** (`Zr` of `cancellation_identity`): sites `Z`, all in the top layer `k`. -/
theorem exists_region_bdry_Z (hk : 1 ≤ k) :
    ∃ D : Region (windowOfHistory H Z g hkK hW).bdry, D.sites = (windowOfHistory H Z g hkK hW).Z ∧
      ∀ x ∈ D.sites, (windowOfHistory H Z g hkK hW).bdry.layerIndex x = k :=
  exists_region_of_top _ hk _ (windowOfHistory_bdryCover g hkK hW) (windowOfHistory_hbZ g hkK hW k hk le_rfl)

open RegionHistory in
/-- **`Z_{k₁}` as a region of `𝔹_k(U_k)`, conditional on `Z_{k₁}` being a union of `k`-blocks.**  This hypothesis is
the source premise that `Z_{k₁}` is a union of `k`-blocks; it is not implied by the history (`Z_{k₁}` is a union of
`π_{k₁}`-cubes, `IsBlockUnion` only for the scales `m ≤ k₁`). -/
theorem exists_region_bdry_Zk1_of_blockUnion (hk : 1 ≤ k)
    (hbu : IsBlockUnion S.L (M * n k) k k (windowOfHistory H Z g hkK hW).Zk1) :
    ∃ D : Region (windowOfHistory H Z g hkK hW).bdry,
      D.sites = (windowOfHistory H Z g hkK hW).Zk1 ∧
      ∀ x ∈ D.sites, (windowOfHistory H Z g hkK hW).bdry.layerIndex x = k :=
  exists_region_of_top _ hk _ (fun x hx => windowOfHistory_bdryCover g hkK hW x
    (windowOfHistory_hZ (g := g) hkK hW hx)) hbu

end Regions

section BlockClosure

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The union of the `k`-blocks meeting a set `Y` of top-layer sites** is the set of sites of a `Region` of `G`
(all sites in the layer `k`); used for `Z_{k₁}^+`, the union of the `k`-blocks meeting `Z_{k₁}` (`Z_{k₁}` itself is a
union of `π_{k₁}`-cubes, not of `k`-blocks). -/
theorem exists_region_blockClosure (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k)
    (Y : Finset (Torus d (N₀ * L ^ k))) (hY : ∀ y ∈ Y, y ∈ G.Ω k) :
    ∃ D : Region G, (∀ x, x ∈ D.sites ↔ ∃ y ∈ Y, jBlock d L N₀ k k x = jBlock d L N₀ k k y) ∧
      ∀ x ∈ D.sites, G.layerIndex x = k := by
  classical
  obtain ⟨D, hD, hl⟩ := exists_region_of_top G hk
    (Finset.univ.filter fun x => ∃ y ∈ Y, jBlock d L N₀ k k x = jBlock d L N₀ k k y)
    (fun x hx => by
      obtain ⟨y, hy, hxy⟩ := (Finset.mem_filter.mp hx).2
      exact (G.blockUnion k hk le_rfl x y hxy).2 (hY y hy))
    (fun x x' h => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, h.symm.trans hxy⟩
      · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, h.trans hxy⟩)
  refine ⟨D, fun x => ?_, hl⟩
  rw [hD]
  simp

/-- **A region minus a union of blocks is a region**: if `Zp` is a union of `j`-blocks for every `1 ≤ j ≤ k`, then
`D ∖ Zp` is the set of sites of a `Region` of `G`. -/
theorem exists_region_sdiff (G : GeneratingSet d L N₀ k ϱ) (D : Region G) (Zp : Finset (Torus d (N₀ * L ^ k)))
    (hZp : ∀ j, 1 ≤ j → j ≤ k → IsBlockUnion L N₀ k j Zp) :
    ∃ D' : Region G, D'.sites = D.sites \ Zp := by
  classical
  refine ⟨⟨D.sites \ Zp, fun x hx => D.sub_Ω (Finset.mem_sdiff.mp hx).1, fun x hx y hy => ?_⟩, rfl⟩
  obtain ⟨hxD, hxZ⟩ := Finset.mem_sdiff.mp hx
  have hyD := D.blockClosed x hxD y hy
  refine Finset.mem_sdiff.mpr ⟨hyD, fun hyZ => hxZ ?_⟩
  obtain ⟨h1, h2, -⟩ := G.layerIndex_spec (D.sub_Ω hxD)
  exact (hZp _ h1 h2 y x (GeneratingSet.mem_blk.1 hy)).1 hyZ

/-- The `k`-block closure is a union of `j`-blocks for every `j ≤ k`. -/
theorem blockClosure_isBlockUnion (Y : Finset (Torus d (N₀ * L ^ k)))
    (Zp : Finset (Torus d (N₀ * L ^ k)))
    (hZp : ∀ x, x ∈ Zp ↔ ∃ y ∈ Y, jBlock d L N₀ k k x = jBlock d L N₀ k k y) :
    ∀ j, 1 ≤ j → j ≤ k → IsBlockUnion L N₀ k j Zp := by
  intro j _ hj x x' h
  have h' := Balaban.Background.jBlock_eq_of_le hj le_rfl h
  rw [hZp, hZp]
  constructor
  · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, h'.symm.trans hxy⟩
  · rintro ⟨y, hy, hxy⟩; exact ⟨y, hy, h'.trans hxy⟩

/-- **Monotonicity of the restricted action in the region** for real data (sum of squares with nonnegative weights):
`A_{D'}(Dat, φ) ≤ A_D(Dat, φ)` for `D' ⊆ D`. -/
theorem actionRegionR_mono {N : ℕ} {G : GeneratingSet d L N₀ k ϱ} (D D' : Region G)
    (h : D'.sites ⊆ D.sites) {a : ℕ → ℝ} {ν : ℝ} (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) (Dat : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) : actionRegionR D' a ν Dat φ ≤ actionRegionR D a ν Dat φ := by
  unfold actionRegionR
  have h1 : ∑ x ∈ D'.sites, (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
      ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 ≤ ∑ x ∈ D.sites, (a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2) *
      ∑ i, ‖Dat.Ψ x i - blockAvg G φ x i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => mul_nonneg (div_nonneg (ha _) (by positivity))
      (Finset.sum_nonneg fun i _ => by positivity)
  have h2 : ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, D'.starWeight x μ *
      ∑ i, ‖barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i‖ ^ 2 ≤
      ∑ x : Torus d (N₀ * L ^ k), ∑ μ : Fin d, D.starWeight x μ *
      ∑ i, ‖barField G Dat.Ψ φ (x + Pi.single μ 1) i - barField G Dat.Ψ φ x i‖ ^ 2 := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ => mul_le_mul_of_nonneg_right ?_
      (Finset.sum_nonneg fun i _ => by positivity)
    unfold Region.starWeight
    have e1 : (if x ∈ D'.sites then (1 : ℝ) else 0) ≤ if x ∈ D.sites then 1 else 0 := by
      split_ifs with a1 a2 <;> first | exact le_rfl | exact absurd (h a1) a2 | norm_num
    have e2 : (if x + Pi.single μ 1 ∈ D'.sites then (1 : ℝ) else 0) ≤
        if x + Pi.single μ 1 ∈ D.sites then 1 else 0 := by
      split_ifs with a1 a2 <;> first | exact le_rfl | exact absurd (h a1) a2 | norm_num
    linarith
  have h3 : ∑ x ∈ D'.sites, ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 ≤
      ∑ x ∈ D.sites, ∑ i, ‖svec G φ x i - Dat.h x i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg h fun x _ _ => Finset.sum_nonneg fun i _ => by positivity
  have : 0 ≤ ν / 2 := by positivity
  nlinarith

/-- **The real part of `β₀ A_{D'}` is at most that of `β₀ A_D`** for `D' ⊆ D` (real data, real field, `β₀ ≥ 0`,
`a ≥ 0`, `ν ≥ 0`). -/
theorem re_actionRegionC_mono {N : ℕ} {G : GeneratingSet d L N₀ k ϱ} (D D' : Region G)
    (h : D'.sites ⊆ D.sites) {a : ℕ → ℝ} {ν : ℝ} (ha : ∀ j, 0 ≤ a j) (hν : 0 ≤ ν) {Dat : BgData G N}
    (hDat : Dat.IsReal) {φ : G.Ω 1 × Fin N → ℂ} (hφ : ∀ p, (φ p).im = 0) {β0 : ℝ} (hβ0 : 0 ≤ β0) :
    ((β0 : ℂ) * actionRegionC D' a ν Dat φ).re ≤ ((β0 : ℂ) * actionRegionC D a ν Dat φ).re := by
  rw [actionRegionC_eq_ofReal D' a ν hDat hφ, actionRegionC_eq_ofReal D a ν hDat hφ,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left (actionRegionR_mono D D' h ha hν Dat φ) hβ0

end BlockClosure

end Balaban.LargeField
