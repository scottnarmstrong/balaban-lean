/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireTransfer
public import Balaban.Fluctuation.Theorem42WireAction
public import Balaban.LargeField.R.ChiBridge

/-!
# From the H7 cube domain to the local background (FLUCTUATION.md §4.2, Step 2)

The regularity inequalities are known (Definition II.3.5 (a), `DeltaC`) for the backgrounds of the
single-cube generating sets `G_{k+1}(□) = 𝔹_{k+1}(□^{∼2})` (`genCubeLoc`).  For a cube `□ ∋ y0` of
`Z'` with `□^{∼4} ⊂ Ω_{k+1}`:

* `genCubeLoc_precedes`: `G_{k+1}(□) ≺ G^{Z'}_{k+1}` (layer by layer);
* `genCubeLoc_top_subset`, `genCubeLoc_dataSites`: the top layers contain the fine set of `□^{∼2}` and
  the data sites of `G_{k+1}(□)` lie over `□^{∼4}`;
* `cube_locData_agree`: the lifted data of the cube and of the local family agree on the data sites of
  the cube;
* `near_geom`, `near_nbr`, `near_blk`, `near'_top`: the regions used for the transfer;
* `regIneq_locGen_of_deltaC`: **the regularity inequalities of the local background**
  `bg(G^{Z'}_{k+1}; lift_{k,k+1}(ψ_k, ψ_{k+1}))` on the sites at distance `≤ 1` from `□`, from the
  membership of `ψ_{k+1}` in `Δ^c_{k+1}(□; 1, r)`, with the radius `r` increased by the
  `Lemma 4.1` error (`regIneq_transfer`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  RegionHistory

set_option linter.unusedSectionVars false

section Geom

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)

/-- The generating set `G_{k+1}(□) = 𝔹_{k+1}(□^{∼2})` of a `π_{k+1}`-cube `□` of the level-`(k+1)` torus
(Definition II.2.4 (i)), on the torus of the local family. -/
noncomputable abbrev genCubeLoc (y0 : Torus S.d (n (k + 1))) :=
  genCube (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (q := k + 1) g.c (n (k + 1)) y0

include Hl in
theorem genCubeLoc_layer_near (y0 : Torus S.d (n (k + 1))) {i : ℕ} {x}
    (hx : x ∈ (genCubeLoc g k y0).Ω i) :
    blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ nbhd 3 {y0} := by
  classical
  rw [genCube_Ω] at hx
  have hi : i ≤ k + 1 := by
    by_contra h
    rw [minLayer_of_gt _ (by omega)] at hx
    exact absurd hx (Finset.notMem_empty _)
  obtain ⟨w, hw, hxw⟩ := exists_near_of_mem_minLayer' (M1 := g.M1) (N₁ := g.c * n (k + 1))
    (L := S.L) (q := k + 1) (j := k + 1) _ Hl.F.ok.two_le_L le_rfl hi hx
  have hc := cubes_close (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) (k := k)
    (eleven_le_P1 (k := k) (M1 := g.M1) (L := S.L) (by have := g.hc; omega) le_rfl) hxw
  rw [mem_cubePre] at hw
  obtain ⟨z, hz, hzd⟩ := mem_nbhd.1 hw
  have hz' : z = y0 := hz
  subst hz'
  refine mem_nbhd.2 ⟨z, rfl, ?_⟩
  have := supDist_triangle (blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x)
    (blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) w) z
  omega

theorem locGen_Ω_top_iff' {x} :
    x ∈ (locGen g Hl k Zc hZc hk).Ω (k + 1) ↔
      x ∈ stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1)))) ∧
        blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ (Hl.step k).Omega := by
  unfold locGen genBoundaryLocal
  rw [boundaryGenSet_Ω]
  unfold boundaryLayer
  have hU : IsCubeUnion g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1)
      (stepU g.M1 g.c (n (k + 1)) S.L k ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))) :=
    isCubeUnion_fineK1 _
  rw [minLayer_of_gt _ (Nat.lt_succ_self k), minLayer_self, hU.cubeInterior_eq]
  simp only [Finset.empty_sdiff, Finset.empty_union, Finset.mem_inter, mem_fineK1]

include Hl in
theorem genCubeLoc_precedes {y0 : Torus S.d (n (k + 1))} (hy0 : y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))))
    (hΩ : nbhd 4 {y0} ⊆ (Hl.step k).Omega) :
    Precedes (genCubeLoc g k y0) (locGen g Hl k Zc hZc hk) := by
  classical
  intro i hi1 hik x hx
  have hnear := genCubeLoc_layer_near g Hl k y0 hx
  have hUρ : 3 * S.L ≤ ⌊R k⌋₊ := g.three_L_le_floor Hl k
  have hL3 := Hl.F.ok.two_le_L
  unfold locGen genBoundaryLocal
  rw [boundaryGenSet_Ω]
  unfold boundaryLayer
  refine Finset.mem_union_right _ (Finset.mem_inter.2 ⟨?_, ?_⟩)
  · refine minLayer_mono (X := cubePre g.M1 (g.c * n (k + 1)) S.L (k + 1)
      (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) (nbhd 2 {y0})) ?_ i (by
        rw [genCube_Ω] at hx; exact hx)
    intro z hz
    rw [mem_cubePre] at hz
    unfold stepU
    rw [mem_fineK1]
    obtain ⟨w, hw, hwd⟩ := mem_nbhd.1 hz
    have hw' : w = y0 := hw
    subst hw'
    exact mem_nbhd.2 ⟨w, hy0, by omega⟩
  · rw [mem_fineK1]
    exact hΩ (nbhd_mono (by norm_num) (fun _ h => h) hnear)

include Hl in
theorem genCubeLoc_top_subset {y0 : Torus S.d (n (k + 1))}
    (hy0 : y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))))
    (hΩ : nbhd 4 {y0} ⊆ (Hl.step k).Omega) {x}
    (hx : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ nbhd 2 {y0}) :
    x ∈ (genCubeLoc g k y0).Ω (k + 1) ∧ x ∈ (locGen g Hl k Zc hZc hk).Ω (k + 1) := by
  have hUρ : 3 * S.L ≤ ⌊R k⌋₊ := g.three_L_le_floor Hl k
  have hL3 := Hl.F.ok.two_le_L
  refine ⟨?_, (locGen_Ω_top_iff' g Hl k Zc hZc hk).2 ⟨?_, ?_⟩⟩
  · rw [genCube_top_eq (by simp), mem_cubePre]; exact hx
  · unfold stepU
    rw [mem_fineK1]
    obtain ⟨w, hw, hwd⟩ := mem_nbhd.1 hx
    have hw' : w = y0 := hw
    subst hw'
    exact mem_nbhd.2 ⟨w, hy0, by omega⟩
  · exact hΩ (nbhd_mono (by norm_num) (fun _ h => h) hx)

include Hl in
theorem genCubeLoc_dataSites {y0 : Torus S.d (n (k + 1))} {x}
    (hx : x ∈ dataSites (genCubeLoc g k y0)) :
    blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ nbhd 4 {y0} := by
  have hL3 := Hl.F.ok.two_le_L
  have hP : 1 ≤ S.L ^ (k + 1) * (g.c * g.M1) := by
    have := NeZero.pos S.L; have := NeZero.pos g.M1; have := NeZero.pos g.c
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  rcases (mem_dataSites _).1 hx with h | h
  · exact nbhd_mono (by norm_num) (fun _ h => h) (genCubeLoc_layer_near g Hl k y0 h)
  · obtain ⟨-, x', hx', hadj⟩ := (mem_collar _).1 h
    have h3 := genCubeLoc_layer_near g Hl k y0 hx'
    have h1 : supDist x' x ≤ 1 := by
      have := supDist_le_torusDist x' x
      have h2 := hadj.torusDist_le
      have : (supDist x' x : ℝ) ≤ 1 := this.trans h2
      exact_mod_cast this
    have hc := cubes_close (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) (k := k) hP h1
    obtain ⟨z, hz, hzd⟩ := mem_nbhd.1 h3
    have hz' : z = y0 := hz
    subst hz'
    refine mem_nbhd.2 ⟨z, rfl, ?_⟩
    have := supDist_triangle (blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x)
      (blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x') z
    rw [supDist_comm] at hc
    omega

/-- The lifted datum `lift_{k,k+1}(ψ, ϑ, h)` of the local family `G^{Z'}_{k+1}` for arbitrary (complex)
fields `ψ = ψ_k`, `ϑ = ψ_{k+1}` and external direction `h` (Definition II.2.1 (b)). -/
noncomputable abbrev locDataC (ψ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - (k + 1))) → Fin N → ℂ)
    (hC : Fin N → ℂ) : BgData (locGen g Hl k Zc hZc hk) N :=
  liftMixed (locGen g Hl k Zc hZc hk)
    ((isCubeUnion_fineK1 (Hl.step k).Omega).isBlockUnion (le_refl _))
    (genBoundaryLocal_top_subset (Hl.step k) g.hc (Hl.F.hnn k (by omega)) Hl.F.ok.two_le_L
      (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
      (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc) ψ ϑ hC

include Hl in
theorem cube_locData_agree {y0 : Torus S.d (n (k + 1))}
    (hy0 : y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))))
    (hΩ : nbhd 4 {y0} ⊆ (Hl.step k).Omega)
    (ψ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - (k + 1))) → Fin N → ℂ)
    (hC : Fin N → ℂ) :
    (∀ x ∈ dataSites (genCubeLoc g k y0),
      (liftSingle (genCubeLoc g k y0) ϑ
        hC).Ψ x = (locDataC g Hl k Zc hZc hk ψ ϑ hC).Ψ x) ∧
    (∀ x ∈ (genCubeLoc g k y0).Ω 1,
      (liftSingle (genCubeLoc g k y0) ϑ
        hC).h x = (locDataC g Hl k Zc hZc hk ψ ϑ hC).h x) := by
  classical
  have hprec := genCubeLoc_precedes g Hl k Zc hZc hk hy0 hΩ
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have hxd : x ∈ dataSites (locGen g Hl k Zc hZc hk) := by
      rcases (mem_dataSites _).1 hx with h | h
      · exact (mem_dataSites _).2 (Or.inl (hprec.mem_Ω1 h))
      · by_cases h' : x ∈ (locGen g Hl k Zc hZc hk).Ω 1
        · exact (mem_dataSites _).2 (Or.inl h')
        · exact (mem_dataSites _).2 (Or.inr (mem_collar_of_not_mem hprec h h'))
    have hxO : x ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega := by
      rw [mem_fineK1]; exact hΩ (genCubeLoc_dataSites g Hl k hx)
    rw [liftSingle_Ψ _ _ _ hx]
    unfold locDataC
    rw [liftMixed_Ψ _ _ _ _ _ _ hxd]
    unfold mixedLift
    simp only [hxO, ↓reduceIte]
    rfl
  · have hx1 : x ∈ (locGen g Hl k Zc hZc hk).Ω 1 := hprec.mem_Ω1 hx
    rw [liftSingle_h _ _ _ hx]
    unfold locDataC
    rw [liftMixed_h _ _ _ _ _ _ hx1]

/-- `1 ≤ minSep`. -/
theorem one_le_minSep (L M1 : ℕ) [NeZero L] [NeZero M1] : 1 ≤ minSep L M1 := by
  unfold minSep
  have h1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h2 : (1 : ℝ) ≤ M1 := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M1)
  nlinarith

section Cubes

variable {d M1 c n1 L : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n1]

theorem cube_supDist_le (k : ℕ) {x x' : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (h : Green.torusDist d (M1 * (c * n1) * L ^ (k + 1)) x x' ≤ 1) :
    supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 x) (blockMap (L ^ (k + 1) * (c * M1)) n1 x')
      ≤ 1 := by
  have hP : 1 ≤ L ^ (k + 1) * (c * M1) := by
    have := NeZero.pos L; have := NeZero.pos M1; have := NeZero.pos c
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  refine cubes_close hP ?_
  have := supDist_le_torusDist x x'
  have : (supDist x x' : ℝ) ≤ 1 := this.trans h
  exact_mod_cast this

end Cubes

include Hl in
theorem near_geom {y0 : Torus S.d (n (k + 1))} (hy0 : y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))))
    (hΩ : nbhd 4 {y0} ⊆ (Hl.step k).Omega) :
    (∀ x ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))),
      x ∈ (genCubeLoc g k y0).Ω (k + 1) ∧ x ∈ (locGen g Hl k Zc hZc hk).Ω (k + 1)) := by
  intro x hx
  obtain ⟨x', hx', hxx'⟩ := mem_stepNearSites.1 hx
  refine genCubeLoc_top_subset g Hl k Zc hZc hk hy0 hΩ ?_
  have h1 := cube_supDist_le k hxx'
  have hx'' : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x' = y0 := hx'
  refine mem_nbhd.2 ⟨y0, rfl, ?_⟩
  rw [hx''] at h1
  omega

theorem regIneq_mono_sets {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ q ϱ} {a : ℕ → ℝ} {μ δ : ℝ} {D : BgData G N}
    {T S T' S' : Finset (Torus d (N₀ * L ^ q))} (h : RegIneq G a μ D δ T S) (hT : T' ⊆ T)
    (hS : S' ⊆ S) : RegIneq G a μ D δ T' S' :=
  ⟨fun x hx => h.1 x (hT hx), fun x hx => h.2.1 x (hS hx), fun hν x hx => h.2.2 hν x (hS hx)⟩

/-- A site at distance `≤ 1` from the fine cube of `y0` has its cube in `□^{∼1}`. -/
theorem near_cube_mem {y0 : Torus S.d (n (k + 1))} {x}
    (hx : x ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1))))) :
    blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈ nbhd 1 {y0} := by
  obtain ⟨x', hx', hxx'⟩ := mem_stepNearSites.1 hx
  have h1 := cube_supDist_le k hxx'
  have hx'' : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x' = y0 := hx'
  refine mem_nbhd.2 ⟨y0, rfl, ?_⟩
  rw [hx''] at h1
  exact h1

theorem near_nbr {y0 : Torus S.d (n (k + 1))} {x}
    (hx : x ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))))
    (μ : Fin S.d) :
    x + Pi.single μ 1 ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k
      (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) ∧
    x - Pi.single μ 1 ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k
      (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) := by
  have hc := near_cube_mem g k hx
  refine ⟨mem_stepNearSites.2 ⟨x, hc, ?_⟩, mem_stepNearSites.2 ⟨x, hc, ?_⟩⟩
  · rw [Green.torusDist_comm_gen]; exact (adj_add_single x μ).torusDist_le
  · rw [Green.torusDist_comm_gen]; exact (adj_sub_single x μ).torusDist_le

theorem near_blk {y0 : Torus S.d (n (k + 1))} {x}
    (hx : x ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))))
    {y} (hy : y ∈ (genCubeLoc g k y0).blk (k + 1) x) :
    y ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k
      (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) := by
  have hc := near_cube_mem g k hx
  have hb : jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) y =
      jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) x := GeneratingSet.mem_blk.1 hy
  have hcu : fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1) y =
      fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1) x := by
    rw [fineCubeIdx_eq_comp le_rfl, fineCubeIdx_eq_comp le_rfl, hb]
  have hU := isCubeUnion_fineK1 (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) (k := k)
    (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1)))))
  have hxU : x ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) := by
    rw [mem_fineK1]; exact hc
  have hyU := (hU y x hcu).2 hxU
  rw [mem_fineK1] at hyU
  exact mem_stepNearSites.2 ⟨y, hyU, by rw [Balaban.Multiscale.torusDist_self']; norm_num⟩

include Hl hZc hk in
theorem near'_top {y0 : Torus S.d (n (k + 1))} (hy0 : y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))))
    (hΩ : nbhd 4 {y0} ⊆ (Hl.step k).Omega) {y}
    (hy : y ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k
      (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1)))))) :
    y ∈ (genCubeLoc g k y0).Ω 1 := by
  obtain ⟨x, hx, hxy⟩ := mem_stepNearSites.1 hy
  have h1 := cube_supDist_le k hxy
  obtain ⟨z, hz, hzd⟩ := mem_nbhd.1 hx
  have hz' : z = y0 := hz
  subst hz'
  have htri := supDist_triangle (blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) y)
    (blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x) z
  have hmem : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) y ∈ nbhd 2 ({z} : Set (Torus S.d (n (k + 1)))) :=
    mem_nbhd.2 ⟨z, rfl, by omega⟩
  exact (genCubeLoc g k z).Ω_antitone le_rfl (by omega) (by omega)
    (genCubeLoc_top_subset g Hl k Zc hZc hk hy0 hΩ hmem).1

include Hl hZc hk in
/-- **The regularity inequalities of the local background from the H7 cube domain** (FLUCTUATION
§4.2 Step 2 and LFR Definition II.3.5 (a)): if the top-layer field `ψ_{k+1}` of the configuration
lies in `Δ^c_{k+1}(□; 1, r)` for a cube `□ ∋ y0` of `Z'` with `□^{∼4} ⊂ Ω_{k+1}`, the regularity
inequalities of the local background `bg(G^{Z'}_{k+1}; lift(ψ_k, ψ_{k+1}))` on the sites at
distance `≤ 1` from `□` hold with the radius `r` increased by
`(N+1)(1 + √ν_k) K_w c_F (2d+2) K₁ δ e^{-γ_w Dist}` (Lemma 4.1 for the composition `G_{k+1}(□) ≺
G^{Z'}_{k+1}`). -/
theorem regIneq_locGen_of_deltaC (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {a₁ ν r δ1 ε1 δ0 ε0 : ℝ} {y0 : Torus S.d (n (k + 1))}
        (ψ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - k)) → Fin N → ℂ)
        (ϑ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - (k + 1))) → Fin N → ℂ)
        (hC : Fin N → ℂ),
        0 < a₁ →
        BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) (ν) →
        2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1) →
        y0 ∈ (Zc : Set (Torus S.d (n (k + 1)))) → nbhd 4 {y0} ⊆ (Hl.step k).Omega →
        ϑ ∈ DeltaC (q := k + 1) (M1 := g.M1) (N₁ := g.c * n (k + 1))
          (L := S.L) (compWeight S.L a₁) (ν) r hC g.c (n (k + 1)) y0 →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
        InDomainC (locGen g Hl k Zc hZc hk) (ν) δ1 ε1 (locDataC g Hl k Zc hZc hk ψ ϑ hC) →
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ bgC1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        InDomainC (genCubeLoc g k y0) (ν) δ0 ε0
          (liftSingle (genCubeLoc g k y0) ϑ hC) →
        bgK1 S.d S.L N * δ0 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ0 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ δw →
        RegIneq (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) (ν)
          (locDataC g Hl k Zc hZc hk ψ ϑ hC)
          (r + transferShift S.d S.L N (k + 1) ν Kw δ1 (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1)))
          (stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))))
          (stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1))))) := by
  obtain ⟨Kw, δw, hK, hδ, htr⟩ := regIneq_transfer (d := S.d) (L := S.L) (N := N) hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro a₁ ν r δ1 ε1 δ0 ε0 y0 ψ ϑ hC ha₁ H hsep hy0 hΩ hΔ hδ10 hδε1 hε1 hδ1c hνε1 hD1 hδ00 hδε0 hε0
    hδ0c hνε0 hD0 hK0 hKw0 hK1 hKw1
  classical
  have hprec := genCubeLoc_precedes g Hl k Zc hZc hk hy0 hΩ
  obtain ⟨hΨ, hh⟩ := cube_locData_agree g Hl k Zc hZc hk hy0 hΩ ψ ϑ hC
  have hΔreg := (show RegC (genCubeLoc g k y0) (compWeight S.L a₁) (ν)
      (liftSingle (genCubeLoc g k y0) ϑ hC) r
      (cubeNbhd g.M1 (g.c * n (k + 1)) S.L (k + 1) g.c (n (k + 1)) 1 y0)
      (cubeNbhd g.M1 (g.c * n (k + 1)) S.L (k + 1) g.c (n (k + 1)) 1 y0) from hΔ).2
  have hReg : RegIneq (genCubeLoc g k y0) (compWeight S.L a₁) (ν)
      (liftSingle (genCubeLoc g k y0) ϑ hC) r
      (stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1)))))
      (stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k ({y0} : Set (Torus S.d (n (k + 1))))) := by
    have hsub : stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k
        ({y0} : Set (Torus S.d (n (k + 1)))) ⊆
        cubeNbhd g.M1 (g.c * n (k + 1)) S.L (k + 1) g.c (n (k + 1)) 1 y0 := by
      intro x hx
      unfold cubeNbhd
      rw [mem_cubePre]
      exact near_cube_mem g k hx
    exact regIneq_mono_sets hΔreg hsub hsub
  have hϱ : 1 ≤ minSep S.L g.M1 := one_le_minSep S.L g.M1
  have hdist := step_dist_premise (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) k
    (genCubeLoc g k y0) hϱ (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) 1
  have hE : ∀ x ∈ {x : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)) |
      blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈
        nbhd 1 (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1)))))}, ∀ m, 1 ≤ m → m ≤ k + 1 →
      (x ∈ (genCubeLoc g k y0).Ω m ↔ x ∈ (locGen g Hl k Zc hZc hk).Ω m) := by
    intro x hx m hm1 hm2
    have hx2 : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈
        nbhd 2 ({y0} : Set (Torus S.d (n (k + 1)))) := by
      have h2 : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈
          nbhd 1 (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) := hx
      rwa [nbhd_nbhd] at h2
    obtain ⟨h0, h1⟩ := genCubeLoc_top_subset g Hl k Zc hZc hk hy0 hΩ hx2
    exact ⟨fun _ => (locGen g Hl k Zc hZc hk).Ω_antitone hm1 hm2 (by omega) h1,
      fun _ => (genCubeLoc g k y0).Ω_antitone hm1 hm2 (by omega) h0⟩
  have hdist' : ∀ y ∈ stepNearSites (M1 := g.M1) (c := g.c) (L := S.L) k
      (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))),
      ∀ w ∈ shadowN (genCubeLoc g k y0) (stepFarSites (M1 := g.M1) (c := g.c) (L := S.L) k
        (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) 1),
      ENNReal.ofReal (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1)) ≤ (genCubeLoc g k y0).pathDist y w :=
    fun y hy w hw => hdist y hy (near'_top g Hl k Zc hZc hk hy0 hΩ hy) w hw
  exact htr (N₁ := g.M1 * (g.c * n (k + 1))) (m₁ := 0) (by simp) ha₁ H H hsep hprec hδ10 hδε1 hε1
    hδ1c hνε1 hD1 hδ00 hδε0 hε0 hδ0c hνε0 hD0 hK0 hKw0 hK1 hKw1 hΨ hh _ hE
    (stepFarSites (M1 := g.M1) (c := g.c) (L := S.L) k
      (nbhd 1 ({y0} : Set (Torus S.d (n (k + 1))))) 1)
    (fun y hy => mem_stepFarSites.2 hy) _ _ (by omega) (near_geom g Hl k Zc hZc hk hy0 hΩ)
    (fun x hx μ => near_nbr g k hx μ) (fun x hx y hy => near_blk g k hx hy)
    (fun y hy => near'_top g Hl k Zc hZc hk hy0 hΩ hy) hdist' hReg

end Geom

end Balaban.Fluctuation
