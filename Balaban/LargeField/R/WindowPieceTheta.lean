/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowThetaY
public import Balaban.LargeField.History.ParentDomain
public import Balaban.LargeField.R.WindowOfHistory

/-!
# The output side of the piece datum from the first family of `ChiDomProp` (blocker 4)

A piece `C` (a component of `Z^pre_{j+1}`) of the window with its localized history: the datum
`locData` is the output field `ψ_{j+1}` on the top blocks over `Ω_{j+1}`.  At a data site over `Ω_{j+1}`
whose cube is within one cube of a cube `q` of `C ∩ Ω_{j+1}`, the top block of the site is a block of
`genBlocksIn B (j+1) (nbhd_1 {q})`, `B` the generating set of the lineage localization, and the
multiscale field of `ChiDomAt` / `ChiNewProp` takes the value of the datum there.  The first family of
`ChiDomProp` at `q` (the same conditions as the first clause of `ChiNewProp`) gives `Ψ̃(𝔹 ∩ q^∼; η)`
for that field; hence

* `piece_theta_sphere`: `| Σ_i Re Ψ(s)_i² - 1 | < η` at such a site (R2);
* `piece_theta_pair`: `rn (Re Ψ(s) - Re Ψ(s')) < η` for an interface pair of two such sites (R1).

The hypothesis `hψ` is the first family of `ChiDomProp`/the first clause of `ChiNewProp` read as a
statement about the multiscale field (`η = 3 d L δ_j`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

section Helpers

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L]

/-- Two sites whose `m`-blocks are adjacent lie over `π_m`-cubes within one cube of each other. -/
theorem cube_near_of_blockAdj (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {m : ℕ} (hm : m ≤ K)
    {a a' : Torus S.d (M * n K * S.L ^ K)}
    (h : BlockAdj (⟨m, jBlock S.d S.L (M * n K) K m a⟩ : BlockPt S n M K)
      (⟨m, jBlock S.d S.L (M * n K) K m a'⟩ : BlockPt S n M K)) :
    supDist (cubeMap n S.L M K m a) (cubeMap n S.L M K m a') ≤ 1 := by
  obtain ⟨x, x', hx, hx', hadj⟩ := h
  have e1 : cubeMap n S.L M K m x = cubeMap n S.L M K m a := by
    rw [← cubeMap_eq_comp hnn hm, ← cubeMap_eq_comp hnn hm, hx]
  have e2 : cubeMap n S.L M K m x' = cubeMap n S.L M K m a' := by
    rw [← cubeMap_eq_comp hnn hm, ← cubeMap_eq_comp hnn hm, hx']
  rw [← e1, ← e2]
  exact cubeMap_adj hnn hm hadj


open Classical in
/-- A site of the block of `s` lies in the same `m`-block as `s` when the layer index of `s` is at
most `m`. -/
theorem jBlock_eq_of_mem_blockSet_le {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ q ϱ) {s y : Torus d (N₀ * L ^ q)} (hy : y ∈ blockSet G s) {m : ℕ}
    (hm : G.layerIndex s ≤ m) (hmq : m ≤ q) :
    jBlock d L N₀ q m y = jBlock d L N₀ q m s := by
  unfold blockSet at hy
  by_cases hs : s ∈ G.Ω 1
  · simp only [hs, ↓reduceIte] at hy
    exact jBlock_eq_of_le hm hmq (GeneratingSet.mem_blk.1 hy)
  · simp only [hs, ↓reduceIte, Finset.mem_singleton] at hy
    rw [hy]

section Gen

variable (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)

/-- The top layer of the local family lies in the fine set of `Ω_{k+1}`. -/
theorem locGen_top_subset :
    (locGen g Hl k Zc hZc hk).Ω (k + 1) ⊆ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega :=
  genBoundaryLocal_top_subset (Hl.step k) g.hc (Hl.F.hnn k (by omega)) Hl.F.ok.two_le_L
    (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc

end Gen

end Helpers

section PieceTheta

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N j : ℕ} (H : RegionHistory S n R k0 K) (g : Geo S n R M) (C : H.Comp (j + 1))
  (hjK : j + 1 ≤ K)

omit [NeZero S.L] in
include hjK in
/-- local Omega vs global on C -/
theorem omega_loc_iff {q : Torus S.d (n (j + 1))} (hq : q ∈ C.1) :
    q ∈ ((H.locRH (j + 1) C).step j).Omega ↔ q ∈ (H.step j).Omega := by
  have h1 := ((H.locRH_derived C (Nat.lt_succ_self j) (by omega)).2.1)
  have hl : q ∈ ((H.lin (j + 1) (j + 1) C : Finset (Torus S.d (n (j + 1)))) : Set _) := by
    rw [lin_self]; exact hq
  constructor
  · intro h
    by_contra h'
    have h2 : q ∈ (H.step j).Omegaᶜ ∩ ((H.lin (j + 1) (j + 1) C : Finset (Torus S.d (n (j + 1)))) : Set _) :=
      ⟨h', hl⟩
    rw [h1] at h2
    exact h2 h
  · intro h
    by_contra h'
    have h2 : q ∈ ((H.locRH (j + 1) C).step j).Omegaᶜ := h'
    rw [← h1] at h2
    exact h2.1 h

/-- The tested field -/
noncomputable abbrev pieceField (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A) : MultiField S n M K N :=
  subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
    (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o

/-- The value of the datum at a site over `Ω_{j+1}` that lies over a cube of the component or its
one-cube neighbourhood is the multiscale field of `ChiDomAt` at the top block of the site. -/
theorem piece_theta_value (hjK : j + 1 ≤ K)
    (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    (x : NewCfg N (H.localHistory M K (j + 1) C) j) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT g (j + 1)} (hs : s ∈ dataSites (locGen g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK))
    (hn : cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s) ∈ nbhd 1 C.1)
    (hO : blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) s ∈ ((H.locRH (j + 1) C).step j).Omega) :
    ∀ i, ((locData g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s i).re =
      (pieceField H C o x (j + 1) (jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s))) i := by
  have hΩ : cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1 →
      cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s) ∈ (H.step j).Omega := fun hq =>
    (omega_loc_iff H C hjK hq).1 (by rw [cubeMap_bgToFine_gen]; exact hO)
  obtain ⟨hV, hfield⟩ := subMultiscaleField_top_eq_out (R := R) (N := N) H hjK C hn hΩ o x
  have hb1 : blkToBlock g H.F.hnn hjK
      (jBlock S.d S.L (g.M1 * (g.c * n (j + 1))) (j + 1) (j + 1) s) =
      jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s) :=
    (jBlock_bgToFine_gen g H.F.hnn hjK le_rfl s).symm
  intro i
  rw [locData_Ψ_of_omega (H.locRH (j + 1) C) C.1 (locComp_mem H hjK C) hjK g o x hv hs hO]
  simp only [Complex.ofReal_re]
  rw [hb1]
  show (outField N o _) i = (subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
    (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o (j + 1) _) i
  rw [hfield]
  simp only [outField, hV, dite_true]

/-- **The sphere bound at a site over `Ω_{j+1}` over the component** (R2). -/
theorem piece_theta_sphere {η : ℝ} (hjK : j + 1 ≤ K)
    (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    (x : NewCfg N (H.localHistory M K (j + 1) C) j) (hv : EuclideanSpace ℝ (Fin N))
    (hψ : ∀ q : Torus S.d (n (j + 1)),
      CubeSub (S := S) (n := n) M K (j + 1) q ((H.localHistory M K (j + 1) C).Z (j + 1)) →
      q ∈ lhOmegaSim (H.localHistory M K (j + 1) C) (j + 1) (j + 1) →
      PsiTildeMulti (pieceField H C o x) (genBlocksIn (chiDomGen H g (j + 1) C) (j + 1) (nbhd 1 {q})) η)
    {s : BgT g (j + 1)} (hs : s ∈ dataSites (locGen g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK))
    (hq : cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1)
    (hO : blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) s ∈ ((H.locRH (j + 1) C).step j).Omega) :
    |∑ i, ((locData g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s i).re ^ 2 - 1| < η := by
  have hq' : cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s) ∈ (H.step j).Omega :=
    (omega_loc_iff H C hjK hq).1 (by rw [cubeMap_bgToFine_gen]; exact hO)
  obtain ⟨hZ, hsim⟩ := cube_conditions_of_mem_Omega (M := M) H hjK C hq hq'
  have hxn : cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s) ∈ nbhd 1 C.1 :=
    mem_nbhd.2 ⟨_, hq, by simp [supDist_self]⟩
  have hb := topBlock_mem_genBlocksIn H g hjK C hxn (fun _ => hq')
    (q := cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s)) (by simp [supDist_self])
  have key := (hψ _ hZ hsim).2 _ hb
  have e := piece_theta_value H g C hjK o x hv hs hxn hO
  simp_rw [e]
  rw [parent_sum_sq_eq_norm_sq]
  exact key

/-- Blocks of two scales `m, m' ≤ j + 1` of the sites of an interface pair of a generating set of the
level-`(j+1)` torus are adjacent when the layer indices are at most `m, m'`. -/
theorem blockAdj_of_interfacePair_le {ϱ' : ℝ}
    {G : GeneratingSet S.d S.L (g.M1 * (g.c * n (j + 1))) (j + 1) ϱ'} {s s' : BgT g (j + 1)}
    (hp : IsInterfacePair G s s') {m m' : ℕ} (hm : G.layerIndex s ≤ m) (hm' : G.layerIndex s' ≤ m')
    (hmq : m ≤ j + 1) (hmq' : m' ≤ j + 1) :
    BlockAdj (⟨m, jBlock S.d S.L (M * n K) K m (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K)
      (⟨m', jBlock S.d S.L (M * n K) K m' (bgToFine g H.F.hnn hjK s')⟩ : BlockPt S n M K) := by
  obtain ⟨-, -, -, y, hy, y', hy', hadj⟩ := hp
  have e1 := jBlock_eq_of_mem_blockSet_le G hy hm hmq
  have e2 := jBlock_eq_of_mem_blockSet_le G hy' hm' hmq'
  refine ⟨bgToFine g H.F.hnn hjK y, bgToFine g H.F.hnn hjK y', ?_, ?_, ?_⟩
  · show jBlock S.d S.L (M * n K) K m _ = _
    rw [jBlock_bgToFine_gen g H.F.hnn hjK hmq, jBlock_bgToFine_gen g H.F.hnn hjK hmq, e1]
  · show jBlock S.d S.L (M * n K) K m' _ = _
    rw [jBlock_bgToFine_gen g H.F.hnn hjK hmq', jBlock_bgToFine_gen g H.F.hnn hjK hmq', e2]
  · obtain ⟨μ, h | h⟩ := hadj
    · exact ⟨μ, Or.inl (by unfold bgToFine; rw [h, torusCast_add_single])⟩
    · exact ⟨μ, Or.inr (by unfold bgToFine; rw [h, torusCast_add_single])⟩

/-- An interface pair of any generating set of the level-`(j+1)` torus has adjacent top blocks over
cubes within one cube of each other. -/
theorem blockAdj_of_interfacePair {ϱ' : ℝ} (hjK : j + 1 ≤ K)
    {G : GeneratingSet S.d S.L (g.M1 * (g.c * n (j + 1))) (j + 1) ϱ'} {s s' : BgT g (j + 1)}
    (hp : IsInterfacePair G s s') :
    supDist (cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s'))
        (cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s)) ≤ 1 ∧
      BlockAdj (⟨j + 1, jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s)⟩ :
          BlockPt S n M K)
        (⟨j + 1, jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s')⟩ :
          BlockPt S n M K) := by
  have hadj := blockAdj_of_interfacePair_le H g hjK hp (layerIndex_le_k G s) (layerIndex_le_k G s')
    le_rfl le_rfl
  exact ⟨by rw [supDist_comm]; exact cube_near_of_blockAdj H.F.hnn hjK hadj, hadj⟩

/-- **The pair bound for two sites over `Ω_{j+1}` near a cube of the component** (R1). -/
theorem piece_theta_pair {η : ℝ} (hjK : j + 1 ≤ K)
    (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    (x : NewCfg N (H.localHistory M K (j + 1) C) j) (hv : EuclideanSpace ℝ (Fin N))
    (hψ : ∀ q : Torus S.d (n (j + 1)),
      CubeSub (S := S) (n := n) M K (j + 1) q ((H.localHistory M K (j + 1) C).Z (j + 1)) →
      q ∈ lhOmegaSim (H.localHistory M K (j + 1) C) (j + 1) (j + 1) →
      PsiTildeMulti (pieceField H C o x) (genBlocksIn (chiDomGen H g (j + 1) C) (j + 1) (nbhd 1 {q})) η)
    {s s' : BgT g (j + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK))
    (hs' : s' ∈ dataSites (locGen g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK))
    (hp : IsInterfacePair (locGen g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK) s s')
    {q : Torus S.d (n (j + 1))} (hqC : q ∈ C.1) (hqΩ : q ∈ (H.step j).Omega)
    (hsq : supDist (cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s)) q ≤ 1)
    (hs'q : supDist (cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK s')) q ≤ 1)
    (hO : blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) s ∈ ((H.locRH (j + 1) C).step j).Omega)
    (hO' : blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) s' ∈ ((H.locRH (j + 1) C).step j).Omega) :
    rn (fun i => ((locData g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s i).re -
      ((locData g (H.locRH (j + 1) C) j C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s' i).re) < η := by
  obtain ⟨hZ, hsim⟩ := cube_conditions_of_mem_Omega (M := M) H hjK C hqC hqΩ
  have hn : ∀ t : BgT g (j + 1), supDist (cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK t)) q ≤ 1 →
      cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK t) ∈ nbhd 1 C.1 := fun t ht =>
    mem_nbhd.2 ⟨q, hqC, ht⟩
  have hΩ : ∀ t : BgT g (j + 1),
      blockMap (S.L ^ (j + 1) * (g.c * g.M1)) (n (j + 1)) t ∈ ((H.locRH (j + 1) C).step j).Omega →
      cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK t) ∈ C.1 →
      cubeMap n S.L M K (j + 1) (bgToFine g H.F.hnn hjK t) ∈ (H.step j).Omega := fun t ht hq =>
    (omega_loc_iff H C hjK hq).1 (by rw [cubeMap_bgToFine_gen]; exact ht)
  have hb := topBlock_mem_genBlocksIn H g hjK C (hn s hsq) (hΩ s hO) (q := q) hsq
  have hb' := topBlock_mem_genBlocksIn H g hjK C (hn s' hs'q) (hΩ s' hO') (q := q) hs'q
  obtain ⟨-, hadj⟩ := blockAdj_of_interfacePair H g hjK hp
  have key := (hψ q hZ hsim).1 _ hb _ hb' (Or.inl rfl) hadj
  have e := piece_theta_value H g C hjK o x hv hs (hn s hsq) hO
  have e' := piece_theta_value H g C hjK o x hv hs' (hn s' hs'q) hO'
  simp_rw [e, e']
  rw [show (fun i => (pieceField H C o x (j + 1) (jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s))) i -
      (pieceField H C o x (j + 1) (jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s'))) i) =
    fun i => (pieceField H C o x (j + 1) (jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s)) -
      pieceField H C o x (j + 1) (jBlock S.d S.L (M * n K) K (j + 1) (bgToFine g H.F.hnn hjK s'))) i from rfl,
    rn_fun_eq_norm]
  exact key

end PieceTheta

end Balaban.LargeField
