/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.QuietIndep
public import Balaban.Fluctuation.Theorem42WireData
import Balaban.LargeField.Region.Inclusions

/-!
# The main action of a quiet step does not read the integrated Gaussian nodes (W958, S1)

`notes/phase1/LF4R-PLAN.md` §9.3, item S1; LFR Lemma III.1.5.  For the piece `c` (a component of
scale `j + 1`, `j ≥ 1`) of the quiet step `j → j + 1` of a window, the main action
`𝒜_{j+1}(c; ψ)` (`mainActionLoc`) reads the variables `ψ_j` of the step only on blocks over
`Ω_j` of the lineage localization of `c`, while a node of scale `j` of the window (a Gaussian block
of an ancestor of scale `j`) whose cube coarsens into `c` lies over `Ω^c_j`.

* `genBoundaryLocal_dataSite_near_W`: a data site of the local family `G^{Z'}_{k+1}` off
  `Ω_{k+1}` has its `π_k`-cube within `1` of `W_k = (Z^c_k)^{≈2}` or its `π_{k+1}`-cube within `1`
  of `Ω_{k+1}`;
* `locGen_dataSite_cube_mem_Omega`: for a region history without removals, such a site lies over
  `Ω_k` (Lemma I.3.5 (a), (g));
* `liftMixed_congr_psi`, `locData_congr_psi`, `locBg_congr_psi`: the lifted datum and the local
  background read `ψ_k` only at the blocks of the data sites off `Ω_{k+1}`;
* `node_cube_not_mem_locOmega`: the cube of a node lies outside `Ω_j` of the localization of `c`
  (Lemma I.3.9 (b): `Ω^c(loc) = Ω^c ∩ Lin`);
* `mainActionLoc_congr_nodes`: the main action of the piece takes the same value at two
  configurations of the new variables that agree off the nodes;
* `mainActionLoc_congr_window`: the same together with `mainActionLoc_congr` for the outputs.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section StepLevel

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}
  (st : RegionStep d L n0 n1 Rprev Rk)
  (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
  (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))

include hc in
/-- A data site of the local family off `Ω_{k+1}` has its `π_k`-cube within `1` of
`W_k = (Z_kᶜ)^{≈2}`, or its `π_{k+1}`-cube within `1` of `Ω_{k+1}`. -/
theorem genBoundaryLocal_dataSite_near_W {z : Torus d (M1 * (c * n1) * L ^ (k + 1))}
    (hz : z ∈ dataSites (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ'))
    (hzO : z ∉ fineK1 M1 c n1 L k st.Omega) :
    blockMap (L ^ k * (c * M1)) n0 z ∈ nbhd 1 (thick2 ⌊Rprev⌋₊ st.Zᶜ) ∨
      blockMap (L ^ (k + 1) * (c * M1)) n1 z ∈ nbhd 1 st.Omega := by
  have hP : M1 * (c * n1) * L ^ (k + 1) = (L ^ k * (c * M1)) * n0 := by rw [hn]; ring
  have hP1 : M1 * (c * n1) * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by ring
  have hD : 11 * M1 * L ^ k + 1 ≤ L ^ k * (c * M1) := by
    have hB : 1 ≤ M1 * L ^ k := Nat.one_le_iff_ne_zero.2 (by
      have := NeZero.ne L; have := NeZero.ne M1; positivity)
    calc 11 * M1 * L ^ k + 1 ≤ 14 * (M1 * L ^ k) := by nlinarith
      _ ≤ c * (M1 * L ^ k) := Nat.mul_le_mul_right _ hc
      _ = L ^ k * (c * M1) := by ring
  -- the `W`-side: a site of the first layer of `𝔹_k(W)` is within `11 M1 L^k` of `W`
  have hWside : ∀ z' : Torus d (M1 * (c * n1) * L ^ (k + 1)),
      z' ∈ minLayer M1 (c * n1) L (k + 1) k
        (stepWLoc M1 c n1 L k ⌊Rprev⌋₊ ⌊Rk⌋₊ st.Z (Z' : Set (Torus d n1))) 1 →
      supDist z z' ≤ 1 → blockMap (L ^ k * (c * M1)) n0 z ∈ nbhd 1 (thick2 ⌊Rprev⌋₊ st.Zᶜ) := by
    intro z' hz' hzz'
    have hk : 1 ≤ k := by
      by_contra h
      rw [minLayer_of_gt _ (by omega : k < 1)] at hz'
      exact absurd hz' (Finset.notMem_empty _)
    obtain ⟨y, hyW, hzy⟩ := exists_near_of_mem_minLayer' _ hL (Nat.le_succ k) hk hz'
    have hyW' := (Finset.mem_inter.1 hyW).1
    unfold stepW at hyW'
    rw [mem_fineK] at hyW'
    have hd : supDist z y ≤ 11 * M1 * L ^ k + 1 :=
      (supDist_triangle z z' y).trans (by omega)
    exact mem_nbhd.2 ⟨_, hyW', supDist_blockMap_le_one hP hD z y hd⟩
  rcases (mem_dataSites _).1 hz with h | h
  · unfold genBoundaryLocal at h
    rw [boundaryGenSet_Ω] at h
    simp only [boundaryLayer, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at h
    rcases h with ⟨hzW, -⟩ | ⟨-, hzOm⟩
    · exact Or.inl (hWside z hzW (by rw [supDist_self]; omega))
    · exact absurd hzOm hzO
  · obtain ⟨-, z', hz', hadj⟩ := (mem_collar _).1 h
    have hzz' : supDist z z' ≤ 1 := by
      have h2 := supDist_le_torusDist z z'
      have h3 := Multiscale.Adj.torusDist_le hadj.symm
      have : (supDist z z' : ℝ) ≤ 1 := h2.trans h3
      exact_mod_cast this
    unfold genBoundaryLocal at hz'
    rw [boundaryGenSet_Ω] at hz'
    simp only [boundaryLayer, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hz'
    rcases hz' with ⟨hz'W, -⟩ | ⟨-, hz'Om⟩
    · exact Or.inl (hWside z' hz'W hzz')
    · right
      rw [mem_fineK1] at hz'Om
      exact mem_nbhd.2 ⟨_, hz'Om, supDist_blockMap_le_one hP1
        (by have := NeZero.ne L; have := NeZero.ne M1; have := NeZero.ne c
            exact Nat.one_le_iff_ne_zero.2 (by positivity)) z z' hzz'⟩

end StepLevel

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (i : ℕ)
  (Zc : Finset (Torus S.d (n (i + 1 + 1))))
  (hZc : Zc ∈ comps (S.omega (i + 1 + 1)) (Hl.F.Zp (i + 1 + 1))) (hk : i + 1 + 1 ≤ K)

/-- **The data sites of the step `j = i + 1` off `Ω_{j+1}` lie over `Ω_j`** (LFR Lemma III.1.5):
the `π_j`-cube of a data site of `G^{Z'}_{j+1}` outside `Ω_{j+1}` is in `Ω_j`. -/
theorem locGen_dataSite_cube_mem_Omega (hrem : ∀ j, Hl.rem j = ∅)
    {z : Torus S.d (g.M1 * (g.c * n (i + 1 + 1)) * S.L ^ (i + 1 + 1))}
    (hz : z ∈ dataSites (locGen g Hl (i + 1) Zc hZc hk))
    (hzO : z ∉ fineK1 g.M1 g.c (n (i + 1 + 1)) S.L (i + 1) (Hl.step (i + 1)).Omega) :
    blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) z ∈ (Hl.step i).Omega := by
  have hgen := genBoundaryLocal_dataSite_near_W (Hl.step (i + 1)) g.hc (Hl.F.hnn (i + 1) (by omega))
    Hl.F.ok.two_le_L (g.three_L_le_floor Hl (i + 1 - 1)) (Hl.F.stepGeom (by omega)).rad.omega_rho
    (Omega_compl_subset_Zpre' (i + 1) (Hl.step (i + 1)) _ _) hZc hz hzO
  by_contra hw
  set w := blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) z with hwdef
  have hZeq : (Hl.step (i + 1)).Z = (Hl.step i).Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1)) := by
    have h := Hl.Z_eq (i + 1)
    rw [hrem (i + 1)] at h
    simpa [FlowSteps.Zpre] using h
  have hdisj := (Hl.step i).thick2_Zpre_compl_disjoint (Hl.F.RH.nonneg i) (S.omega (i + 1))
    (critOpt S k0 (i + 1))
  have hw3 : w ∈ nbhd 3 (Hl.step i).OmegaDDᶜ ∪ (Hl.step i).S :=
    Or.inl (subset_nbhd 3 _ (fun h => hw ((Hl.step i).OmegaDD_subset_Omega h)))
  have hwW : w ∉ nbhd 1 (thick2 ⌊R i⌋₊ ((Hl.step i).Zpre (S.omega (i + 1)) (critOpt S k0 (i + 1)))ᶜ) :=
    fun h => Set.disjoint_left.1 hdisj h hw3
  have hwZ : w ∈ (Hl.step (i + 1)).Z := by
    rw [hZeq]
    by_contra h
    exact hwW (subset_nbhd 1 _ (by rw [thick2_eq]; exact subset_nbhd _ _ h))
  rcases hgen with h1 | h2
  · apply hwW
    rw [← hZeq]
    simpa using h1
  · obtain ⟨p, hp, hd⟩ := mem_nbhd.1 h2
    have hcz : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) z =
        blockMap S.L (n (i + 1 + 1)) w := (blockMap_k_succ (Hl.F.hnn (i + 1) (by omega)) z).symm
    have hU : blockMap S.L (n (i + 1 + 1)) w ∈ (Hl.step (i + 1)).Uprime :=
      ⟨w, subset_nbhd _ _ hwZ, rfl⟩
    have hpU : p ∈ nbhd (⌊R (i + 1)⌋₊ + 4) (Hl.step (i + 1)).Uprime :=
      mem_nbhd.2 ⟨_, hU, by rw [supDist_comm, ← hcz]; omega⟩
    exact (Hl.step (i + 1)).nbhd_Uprime_subset hpU ((Hl.step (i + 1)).Omega_subset_OmegaPrime hp)

end History

section Congr

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The mixed lift reads `ψ` only at the data sites off `Ω`. -/
theorem liftMixed_congr_psi (G : GeneratingSet d L N₀ (k + 1) ϱ)
    {Ω : Finset (Torus d (N₀ * L ^ (k + 1)))} (hΩ : IsBlockUnion L N₀ (k + 1) (k + 1) Ω)
    (hG : G.Ω (k + 1) ⊆ Ω) {ψ ψ' : Torus d (N₀ * L ^ (k + 1 - k)) → Fin N → ℂ}
    {ϑ : Torus d (N₀ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ} {h : Fin N → ℂ}
    (hψ : ∀ x ∈ dataSites G, x ∉ Ω →
      ψ (jBlock d L N₀ (k + 1) k x) = ψ' (jBlock d L N₀ (k + 1) k x)) :
    liftMixed G hΩ hG ψ ϑ h = liftMixed G hΩ hG ψ' ϑ h := by
  classical
  refine BgData.ext' (funext fun x => ?_) rfl
  by_cases hx : x ∈ dataSites G
  · simp only [liftMixed, BgData.clip, hx, ↓reduceIte, mixedLift, blockLift]
    split_ifs with hxΩ
    · rfl
    · exact hψ x hx hxΩ
  · simp [liftMixed, BgData.clip, hx]

end Congr

section LocalData

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)

/-- The lifted datum of the local background reads the configuration of scale `k` only at the
blocks of the data sites off `Ω_{k+1}`. -/
theorem locData_congr_psi (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x x' : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hxx : ∀ z ∈ dataSites (locGen g Hl k Zc hZc hk),
      z ∉ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega →
      subVarField N x k (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ k) hk)
          (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k z)) =
        subVarField N x' k (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ k) hk)
          (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k z))) :
    locData g Hl k Zc hZc hk o x hv = locData g Hl k Zc hZc hk o x' hv := by
  unfold locData
  refine liftMixed_congr_psi _ _ _ (fun z hz hzO => ?_)
  funext i
  simp only [locLiftPsi, blockCfgOf, BlockCfg.toC, hxx z hz hzO]

/-- The local background reads the configuration of scale `k` only at the blocks of the data
sites off `Ω_{k+1}`. -/
theorem locBg_congr_psi (cs : OpConsts) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x x' : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    (hxx : ∀ z ∈ dataSites (locGen g Hl k Zc hZc hk),
      z ∉ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega →
      subVarField N x k (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ k) hk)
          (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k z)) =
        subVarField N x' k (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ k) hk)
          (jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k z))) :
    locBg g Hl k Zc hZc hk cs o x hv = locBg g Hl k Zc hZc hk cs o x' hv := by
  unfold locBg bgLocPiece
  congr 1
  refine liftMixed_congr_psi _ _ _ (fun z hz hzO => ?_)
  funext i
  simp only [locLiftPsi, blockCfgOf, BlockCfg.toC, hxx z hz hzO]

end LocalData

section Window

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open RegionHistory

/-- A node of scale `i + 1` of the window whose cube coarsens into the component `c` of scale
`i + 2` lies over `Ω^c_{i+1}` of the lineage localization of `c`. -/
theorem node_cube_not_mem_locOmega {k1 m' : ℕ} {Z : H.Comp (m' + 1)}
    (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    {i : ℕ} (him : i + 1 ≤ m') (hk : i + 1 + 1 ≤ K) (c : H.Comp (i + 1 + 1))
    {y : BlockAt S n M K (i + 1)} (hy : nd ⟨i + 1, y⟩)
    (hyc : blockMap S.L (n (i + 1 + 1)) (blockCube S n M K (i + 1) y) ∈ c.1) :
    blockCube S n M K (i + 1) y ∉ ((H.locRH (i + 1 + 1) c).step i).Omega := by
  obtain ⟨-, -, c', hc', hyg⟩ := (hnd i y).1 hy
  rw [gaussBlocks_iff (by omega) c'] at hyg
  obtain ⟨hyc', hyO'⟩ := hyg
  obtain ⟨hrem', -⟩ := (mem_ancFin.1 hc').first (by omega)
  obtain ⟨Z'', hs⟩ := H.exists_succ (k := i + 1) (by omega) hrem'
  have hZc : Z'' = c := Subtype.ext (comp_eq_of_mem Z''.2 c.2 (hs ⟨_, hyc', rfl⟩) hyc)
  subst hZc
  have hlin : blockCube S n M K (i + 1) y ∈
      ((H.lin (i + 1) (i + 1 + 1) Z'' : Finset _) : Set (Torus S.d (n (i + 1)))) :=
    Finset.mem_coe.2 (mem_lin.2 ⟨c', Desc.single hrem' hs, hyc'⟩)
  have hc'O := (locRH_derived c' (j := i) (Nat.lt_succ_self i) (by omega)).2.1
  have hcO := (locRH_derived Z'' (j := i) (by omega) (by omega)).2.1
  intro hmem
  have h1 : blockCube S n M K (i + 1) y ∈ ((H.locRH (i + 1) c').step i).Omegaᶜ := hyO'
  rw [← hc'O] at h1
  have h2 : blockCube S n M K (i + 1) y ∈
      (H.step i).Omegaᶜ ∩ ((H.lin (i + 1) (i + 1 + 1) Z'' : Finset _) : Set _) := ⟨h1.1, hlin⟩
  rw [hcO] at h2
  exact h2 hmem

/-- **S1: the main action of a quiet step does not read the integrated Gaussian nodes** (LFR
Lemma III.1.5).  For the piece `c` (a component of scale `j + 1`) of the quiet step `j → j + 1`
of the window, `k₁ ≤ j ≤ m'`, the main action `𝒜_{j+1}(c; ψ)` takes the same value at two
configurations of the new variables that agree off the nodes `nd` of the window. -/
theorem mainActionLoc_congr_nodes (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ}
    {Z : H.Comp (m' + 1)} (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m') (hk : j + 1 ≤ K) (c : H.Comp (j + 1))
    (o : OutT N R (H.localHistory M K (j + 1) c) (j + 1))
    (x x' : NewCfg N (H.localHistory M K (j + 1) c) j) (hv : EuclideanSpace ℝ (Fin N))
    (hxx : ∀ q (y : BlockAt S n M K q), ¬ nd ⟨q, y⟩ → subVarField N x q y = subVarField N x' q y) :
    mainActionLoc g (H.locRH (j + 1) c) j c.1 (locComp_mem H hk c) hk cs (locRH_rem (j + 1) c)
        o x hv =
      mainActionLoc g (H.locRH (j + 1) c) j c.1 (locComp_mem H hk c) hk cs (locRH_rem (j + 1) c)
        o x' hv := by
  classical
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  -- a node of scale `i + 1` that is a variable of the piece lies over `Ω^c_{i+1}` of the piece
  have hread : ∀ y : BlockAt S n M K (i + 1), nd ⟨i + 1, y⟩ →
      BlockSub (S := S) (n := n) (M := M) (K := K) (i + 1) y
        (varSet (H.localHistory M K (i + 1 + 1) c) (i + 1) .large) →
      blockCube S n M K (i + 1) y ∉ ((H.locRH (i + 1 + 1) c).step i).Omega := by
    intro y hy hb
    refine node_cube_not_mem_locOmega nd hnd hjm hk c hy ?_
    have hb2 : BlockSub (S := S) (n := n) (M := M) (K := K) (i + 1) y
        (fineSet (S := S) (n := n) M K (i + 1 + 1) (c.1 : Set (Torus S.d (n (i + 1 + 1))))) :=
      fun x0 hx0 => (hb x0 hx0).1.2
    exact (blockSub_fineSet_succ_iff H.F.hnn hk _ y).1 hb2
  -- the two configurations agree on every block that is not a node variable read by the piece
  have hagree : ∀ q (y : BlockAt S n M K q), (q = i + 1 → nd ⟨q, y⟩ →
      BlockSub (S := S) (n := n) (M := M) (K := K) q y
        (varSet (H.localHistory M K (i + 1 + 1) c) q .large) → False) →
      subVarField N x q y = subVarField N x' q y := by
    intro q y hq
    by_cases hnq : nd ⟨q, y⟩
    · have h0 : ∀ x'' : NewCfg N (H.localHistory M K (i + 1 + 1) c) (i + 1),
          subVarField N x'' q y = 0 := by
        intro x''
        unfold subVarField
        split_ifs with hc
        · exfalso
          obtain ⟨hj, hb, hmem⟩ := hc
          exact hq hmem hnq hb
        · rfl
      rw [h0 x, h0 x']
    · exact hxx q y hnq
  have hms : subMultiscaleField N (H.localHistory M K (i + 1 + 1) c) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) c) (i + 1 + 1)) x o =
      subMultiscaleField N (H.localHistory M K (i + 1 + 1) c) (i + 1 + 1)
      (Vblk R (H.localHistory M K (i + 1 + 1) c) (i + 1 + 1)) x' o := by
    funext q y
    unfold subMultiscaleField
    by_cases hq : q < i + 1 + 1
    · simp only [hq, ↓reduceIte]
      split_ifs with hc
      · refine hagree q y (fun hqe hy hb => ?_)
        subst hqe
        rcases hc with h0 | hO
        · omega
        · apply hread y hy hb
          obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := M) (by omega) y
          rcases hO x0 hx0 with h1 | h1
          · rw [blockCube_eq_cubeMap H.F.hnn (by omega) hx0]
            exact h1.1
          · exact absurd (hb x0 hx0).1 h1
      · rfl
    · simp only [hq, ↓reduceIte]
      split_ifs with h1 h2
      · subst h1; rfl
      · rfl
      · rfl
  have hdat : ∀ z ∈ dataSites (locGen g (H.locRH (i + 1 + 1) c) (i + 1) c.1 (locComp_mem H hk c) hk),
      z ∉ fineK1 g.M1 g.c (n (i + 1 + 1)) S.L (i + 1) ((H.locRH (i + 1 + 1) c).step (i + 1)).Omega →
      subVarField N x (i + 1) (torusCast (histScale_eq g.hM (H.locRH (i + 1 + 1) c).F.hnn
          (Nat.le_succ (i + 1)) hk)
          (jBlock S.d S.L (g.M1 * (g.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1) z)) =
        subVarField N x' (i + 1) (torusCast (histScale_eq g.hM (H.locRH (i + 1 + 1) c).F.hnn
          (Nat.le_succ (i + 1)) hk)
          (jBlock S.d S.L (g.M1 * (g.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1) z)) := by
    intro z hz hzO
    refine hagree _ _ (fun _ hy hb => hread _ hy hb ?_)
    rw [Fluctuation.blockCube_torusCast_le g H.F.hnn (Nat.le_succ (i + 1)) hk z]
    exact locGen_dataSite_cube_mem_Omega g (H.locRH (i + 1 + 1) c) i c.1 (locComp_mem H hk c) hk
      (locRH_rem _ c) hz hzO
  have hD := locData_congr_psi g (H.locRH (i + 1 + 1) c) (i + 1) c.1 (locComp_mem H hk c) hk o x x'
    hv hdat
  have hB := locBg_congr_psi g (H.locRH (i + 1 + 1) c) (i + 1) c.1 (locComp_mem H hk c) hk cs o x
    x' hv hdat
  unfold mainActionLoc locPhi
  rw [hD, hB]
  erw [hms]
  rfl

/-- **The main action of a piece at two window configurations** (S1 with `mainActionLoc_congr`):
it takes the same value at `(o, x)` and `(o', x')` when the outputs agree off the Gaussian blocks
of the piece and the new variables agree off the nodes of the window. -/
theorem mainActionLoc_congr_window (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ}
    {Z : H.Comp (m' + 1)} (nd : (Σ s, BlockAt S n M K s) → Prop)
    (hnd : ∀ j (y : BlockAt S n M K (j + 1)), nd ⟨j + 1, y⟩ ↔ (k1 ≤ j ∧ j ≤ m' ∧
      ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j))
    {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m') (hk : j + 1 ≤ K) (c : H.Comp (j + 1))
    (o o' : OutT N R (H.localHistory M K (j + 1) c) (j + 1))
    (x x' : NewCfg N (H.localHistory M K (j + 1) c) j) (hv : EuclideanSpace ℝ (Fin N))
    (hoo : ∀ y : Vblk R (H.localHistory M K (j + 1) c) (j + 1),
      y.1 ∉ gaussBlocks (H.localHistory M K (j + 1) c) j → o y = o' y)
    (hxx : ∀ q (y : BlockAt S n M K q), ¬ nd ⟨q, y⟩ → subVarField N x q y = subVarField N x' q y) :
    mainActionLoc g (H.locRH (j + 1) c) j c.1 (locComp_mem H hk c) hk cs (locRH_rem (j + 1) c)
        o x hv =
      mainActionLoc g (H.locRH (j + 1) c) j c.1 (locComp_mem H hk c) hk cs (locRH_rem (j + 1) c)
        o' x' hv :=
  (mainActionLoc_congr g cs hk c o o' hoo x hv).trans
    (mainActionLoc_congr_nodes g cs nd hnd hj1 hjm hk c o' x x' hv hxx)

end Window

end Balaban.LargeField
