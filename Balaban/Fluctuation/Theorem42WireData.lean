/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireLayers
public import Balaban.Background.Def5
import Balaban.LargeField.Operators.CompBound
import Balaban.Background.Minimizer

/-!
# The local data of the large-field step on `X_{Z'}` (LFR Definition II.5.4, FLUCTUATION §4.2)

Data identification for `mainActionLoc`, for `k ≥ 1`, on the sites of `X_{Z'} = Z^c_k ∩ Z'`:

* `blockCube_torusCast_le`: the cube of the history-torus block of a level-`(k+1)` block;
* `locData_Ψ_top`, `locData_Ψ_k`: the lifted datum `Ψ` of the local background on `X_{Z'}` is the
  multiscale field `ψ` of `psiLevel` on the blocks of its layer;
* `Xfine_blk`: `X_{Z'}` is a union of blocks of each layer of `G^{Z'}_{k+1}` it meets;
* `cubeActionStar_eq_actionG_local`: the star cube action of `X` is `A_G(X; ψ, φ) + ¼ ∑_{st(X)}|∂φ|²`
  when `Ψ` and `ψ` agree only on the sites of `X` (a local form of `cubeActionStar_eq_actionG`);
* `bgFieldC_im_zero`: the complex background of real data in `𝒟` is real.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.Background RegionHistory

set_option linter.unusedSectionVars false

section Cast

theorem torusCast_val_wire {d m m' : ℕ} (h : m = m') (y : Torus d m) (i : Fin d) :
    ((torusCast h y) i).val = (y i).val := by
  subst h
  rfl

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L]

/-- Generalization of `blockCube_torusCast` to blocks of any scale `i ≤ q`. -/
theorem blockCube_torusCast_le (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1))
    {q i : ℕ} (hiq : i ≤ q) (hqK : q ≤ K)
    (x : Torus S.d (g.M1 * (g.c * n q) * S.L ^ q)) :
    blockCube S n M K i (torusCast (histScale_eq g.hM hnn hiq hqK)
        (jBlock S.d S.L (g.M1 * (g.c * n q)) q i x)) =
      blockMap (S.L ^ i * (g.c * g.M1)) (n i) x := by
  funext j
  unfold blockCube blockMap blockCoord
  congr 1
  rw [torusCast_val_wire]
  have hℓ : g.M1 * (g.c * n q) * S.L ^ q = S.L ^ i * (g.M1 * (g.c * n q) * S.L ^ (q - i)) :=
    side_eq hiq
  have h1 : (jBlock S.d S.L (g.M1 * (g.c * n q)) q i x j).val = (x j).val / S.L ^ i := by
    unfold jBlock
    exact blockCoord_val hℓ (x j)
  rw [h1, Nat.div_div_eq_div_mul]
  exact congrArg (fun m => (x j).val / (S.L ^ i * m)) g.hM

end Cast

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hrem : ∀ j, Hl.rem j = ∅)

theorem locData_Ψ_top (hk1 : 1 ≤ k) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    {z} (hz : z ∈ Xfine g Hl k Zc)
    (hOm : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) z ∈ (Hl.step k).Omega) (i : Fin N) :
    (locData g Hl k Zc hZc hk o xc hv).Ψ z i =
      ((psiLevel g Hl k hk
        (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
          (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) xc o) (k + 1)
        (blkMap S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z) i : ℝ) : ℂ) := by
  classical
  have hzΩ : z ∈ (locGen g Hl k Zc hZc hk).Ω 1 :=
    (locGen g Hl k Zc hZc hk).Ω_antitone le_rfl (by omega) (by omega)
      ((locGen_Ω_top_iff g Hl k Zc hZc hk hz).2 hOm)
  unfold locData
  rw [liftMixed_Ψ _ _ _ _ _ _ ((mem_dataSites _).2 (Or.inl hzΩ))]
  have hzOm : z ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega := by
    rw [mem_fineK1]; exact hOm
  unfold mixedLift
  simp only [hzOm, ↓reduceIte]
  unfold blockLift psiLevel
  simp only [le_refl, ↓reduceDIte]
  unfold subMultiscaleField
  simp only [lt_irrefl, ↓reduceIte, ↓reduceDIte]
  have hB : BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1)
      (torusCast (histScale_eq g.hM Hl.F.hnn (le_refl (k + 1)) hk)
        (blkMap S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z))
      (lhOmega (locHist Hl M K (k + 1) Zc) (k + 1) (k + 1)) := by
    have hcube : blockCube S n M K (k + 1) (torusCast (histScale_eq g.hM Hl.F.hnn (le_refl (k + 1)) hk)
        (blkMap S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z)) =
        blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) z :=
      blockCube_torusCast_le g Hl.F.hnn (le_refl (k + 1)) hk z
    have h1 : BlockSub (S := S) (n := n) (M := M) (K := K) (k + 1)
        (torusCast (histScale_eq g.hM Hl.F.hnn (le_refl (k + 1)) hk)
          (blkMap S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (k + 1) z))
        (fineSet (S := S) (n := n) M K (k + 1) (Hl.step k).Omega ∩
          fineSet (S := S) (n := n) M K (k + 1) (Zc : Set (Torus S.d (n (k + 1))))) := by
      refine (blockSub_inter _ _ _ _).2 ⟨?_, ?_⟩
      · rw [blockSub_fineSet_iff Hl.F.hnn hk, hcube]; exact hOm
      · rw [blockSub_fineSet_iff Hl.F.hnn hk, hcube]
        exact (Xfine_mem g Hl k Zc hz).1
    exact fun x' hx' => Or.inl (h1 x' hx')
  simp only [hB, or_true, ↓reduceIte]
  rfl

include hrem in
theorem locData_Ψ_k (hk1 : 1 ≤ k) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (xc : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N))
    {z} (hz : z ∈ Xfine g Hl k Zc)
    (hOm : blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) z ∉ (Hl.step k).Omega) (i : Fin N) :
    (locData g Hl k Zc hZc hk o xc hv).Ψ z i =
      ((psiLevel g Hl k hk
        (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
          (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) xc o) k
        (blkMap S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k z) i : ℝ) : ℂ) := by
  classical
  have hzΩ : z ∈ (locGen g Hl k Zc hZc hk).Ω 1 :=
    (locGen g Hl k Zc hZc hk).Ω_antitone le_rfl hk1 (by omega) (locGen_Ω_k g Hl k Zc hZc hk hk1 hz)
  unfold locData
  rw [liftMixed_Ψ _ _ _ _ _ _ ((mem_dataSites _).2 (Or.inl hzΩ))]
  have hzOm : z ∉ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega := by
    rw [mem_fineK1]; exact hOm
  unfold mixedLift
  simp only [hzOm, ↓reduceIte]
  unfold blockLift psiLevel
  simp only [Nat.le_succ k, ↓reduceDIte]
  unfold subMultiscaleField
  simp only [Nat.lt_succ_self k, ↓reduceIte]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hcube : blockCube S n M K (m + 1) (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ (m + 1)) hk)
      (blkMap S.d S.L (g.M1 * (g.c * n (m + 1 + 1))) (m + 1 + 1) (m + 1) z)) =
      blockMap (S.L ^ (m + 1) * (g.c * g.M1)) (n (m + 1)) z :=
    blockCube_torusCast_le g Hl.F.hnn (Nat.le_succ (m + 1)) hk z
  have hB : BlockSub (S := S) (n := n) (M := M) (K := K) (m + 1)
      (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ (m + 1)) hk)
        (blkMap S.d S.L (g.M1 * (g.c * n (m + 1 + 1))) (m + 1 + 1) (m + 1) z))
      (lhOmega (locHist Hl M K (m + 1 + 1) Zc) (m + 1 + 1) (m + 1)) := by
    have h1 : BlockSub (S := S) (n := n) (M := M) (K := K) (m + 1)
        (torusCast (histScale_eq g.hM Hl.F.hnn (Nat.le_succ (m + 1)) hk)
          (blkMap S.d S.L (g.M1 * (g.c * n (m + 1 + 1))) (m + 1 + 1) (m + 1) z))
        (fineSet (S := S) (n := n) M K (m + 1) (Hl.step m).Omega ∩
          fineSet (S := S) (n := n) M K (m + 1 + 1) (Zc : Set (Torus S.d (n (m + 1 + 1))))) := by
      refine (blockSub_inter _ _ _ _).2 ⟨?_, ?_⟩
      · rw [blockSub_fineSet_iff Hl.F.hnn (by omega), hcube]
        by_contra hc
        exact (Xfine_mem g Hl (m + 1) Zc hz).2
          ((Hl.toSeq hk hrem).OmegaAt_compl_subset_Z m hc)
      · rw [blockSub_fineSet_succ_iff Hl.F.hnn hk, hcube]
        have h2 := (Xfine_mem g Hl (m + 1) Zc hz).1
        rw [← blockMap_k_succ (Hl.F.hnn (m + 1) (by omega))] at h2
        exact h2
    exact fun x' hx' => Or.inl (h1 x' hx')
  simp only [hB, or_true, ↓reduceIte]
  rfl

theorem Xfine_blk (hk1 : 1 ≤ k) {z} (hz : z ∈ Xfine g Hl k Zc) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k + 1) (hzl : z ∈ (locGen g Hl k Zc hZc hk).layer j)
    {y} (hy : y ∈ (locGen g Hl k Zc hZc hk).blk j z) : y ∈ Xfine g Hl k Zc := by
  classical
  have hb : jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) j y =
      jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) j z := GeneratingSet.mem_blk.1 hy
  have hb1 := jBlock_eq_of_le hjk le_rfl hb
  have hcu1 : fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1) y =
      fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) (k + 1) z := by
    rw [fineCubeIdx_eq_comp le_rfl, fineCubeIdx_eq_comp le_rfl, hb1]
  have hzx := Xfine_mem g Hl k Zc hz
  have hyU : y ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (Zc : Set (Torus S.d (n (k + 1)))) := by
    have hzU : z ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (Zc : Set (Torus S.d (n (k + 1)))) := by
      rw [mem_fineK1]; exact hzx.1
    exact (isCubeUnion_fineK1 _ y z hcu1).2 hzU
  unfold Xfine
  rw [Finset.mem_sdiff]
  refine ⟨hyU, ?_⟩
  rw [mem_fineK]
  rcases (layer_mem_iff_of_top _ (locGen_Ω_k g Hl k Zc hZc hk hk1 hz) hj1 hjk).1 hzl with
    ⟨hjk', -⟩ | ⟨hjk', hzt⟩
  · have hcu : fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) k y =
        fineCubeIdx g.M1 (g.c * n (k + 1)) S.L (k + 1) k z := by
      have hb' : jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k y =
          jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) k z :=
        Eq.mp (congrArg (fun t => jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) t y =
          jBlock S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) t z) hjk') hb
      rw [fineCubeIdx_eq_comp (by omega), fineCubeIdx_eq_comp (by omega), hb']
    have := isCubeUnion_fineK (M1 := g.M1) (c := g.c) (n1 := n (k + 1)) (L := S.L) (k := k)
      (Hl.F.hnn k (by omega)) (Hl.step k).Z y z hcu
    rw [mem_fineK, mem_fineK] at this
    rw [this]; exact hzx.2
  · subst hjk'
    have hzO := (locGen_Ω_top_iff g Hl k Zc hZc hk hz).1 hzt
    have hzO' : z ∈ fineK1 g.M1 g.c (n (k + 1)) S.L k (Hl.step k).Omega := by
      rw [mem_fineK1]; exact hzO
    have hyO := (isCubeUnion_fineK1 _ y z hcu1).2 hzO'
    rw [mem_fineK1] at hyO
    rw [← blockMap_k_succ (Hl.F.hnn k (by omega))] at hyO
    exact (Hl.step k).not_mem_Z_of_mem_Omega (by have := NeZero.ne S.L; omega) (Hl.F.hnn k (by omega)) hyO

end Step

section Local

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

open Classical in
/-- **Local form of `cubeActionStar_eq_actionG`**: only the identification of `Ψ` with `ψ` on the
sites of `X` is needed (real data). -/
theorem cubeActionStar_eq_actionG_local (hd : 2 ≤ d) (X : Finset (Site d L N₀ k))
    (hXΩ : X ⊆ G.Ω 1)
    (hXblk : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ X, x ∈ G.layer n → ∀ y ∈ G.blk n x, y ∈ X)
    (ν : ℝ) (D : BgData G N) (hreal : D.IsReal) (φ : Site d L N₀ k → EuclideanSpace ℝ (Fin N))
    (ψ : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (hout : ∀ x, x ∉ G.Ω 1 → ∀ i, D.Ψ x i = ((φ x i : ℝ) : ℂ))
    (hΨ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ X, x ∈ G.layer n → ∀ i,
      D.Ψ x i = ((ψ n (blkMap d L N₀ k n x) i : ℝ) : ℂ))
    (hh : ∀ x ∈ X, ∀ i, D.h x i = ((hv i : ℝ) : ℂ)) :
    cubeActionStar G a ν X D.Ψ D.h (toFieldC G φ) =
      ((actionG G a ν hv X ψ φ + 1 / 4 * starBondE X φ : ℝ) : ℂ) := by
  obtain ⟨ψ', hdef⟩ : ∃ ψ' : (m : ℕ) → Blk d L N₀ k m → EuclideanSpace ℝ (Fin N), ∀ m y, ψ' m y =
      if h : ∃ x ∈ G.layer m, blkMap d L N₀ k m x = y then
        WithLp.toLp 2 fun i => (D.Ψ h.choose i).re
      else ψ m y := ⟨_, fun _ _ => rfl⟩
  have hψ'ψ : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ X, x ∈ G.layer n →
      ψ' n (blkMap d L N₀ k n x) = ψ n (blkMap d L N₀ k n x) := by
    intro n hn1 hnk x hxX hxl
    have hex : ∃ x' ∈ G.layer n, blkMap d L N₀ k n x' = blkMap d L N₀ k n x := ⟨x, hxl, rfl⟩
    rw [hdef]; simp only [hex, ↓reduceDIte]
    obtain ⟨hc, hcb⟩ := hex.choose_spec
    have hcb' : jBlock d L N₀ k n hex.choose = jBlock d L N₀ k n x := hcb
    have hcX : hex.choose ∈ X :=
      hXblk n hn1 hnk x hxX hxl _ (GeneratingSet.mem_blk.2 hcb')
    ext i
    have h1 := hΨ n hn1 hnk _ hcX hc i
    rw [hcb] at h1
    show (D.Ψ hex.choose i).re = ψ n (blkMap d L N₀ k n x) i
    have := congrArg Complex.re h1
    simpa using this
  have hΨ' : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ i,
      D.Ψ x i = ((ψ' n (blkMap d L N₀ k n x) i : ℝ) : ℂ) := by
    intro n hn1 hnk x hxl i
    have hex : ∃ x' ∈ G.layer n, blkMap d L N₀ k n x' = blkMap d L N₀ k n x := ⟨x, hxl, rfl⟩
    rw [hdef]; simp only [hex, ↓reduceDIte]
    obtain ⟨hc, hcb⟩ := hex.choose_spec
    have hcb' : jBlock d L N₀ k n hex.choose = jBlock d L N₀ k n x := hcb
    have hxc : D.Ψ x = D.Ψ hex.choose :=
      D.Ψ_layerConst n hn1 hnk hex.choose hc x (GeneratingSet.mem_blk.2 hcb'.symm)
    rw [hxc]
    show D.Ψ hex.choose i = (((D.Ψ hex.choose i).re : ℝ) : ℂ)
    apply Complex.ext <;> simp [(hreal hex.choose i).1]
  have key := cubeActionStar_eq_actionG (a := a) hd X hXΩ hXblk ν D φ ψ' hv hout hΨ' hh
  have hact : actionG G a ν hv X ψ' φ = actionG G a ν hv X ψ φ := by
    unfold actionG
    congr 3
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnk⟩ := Finset.mem_Icc.1 hn
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    simp only [lam, show n ≠ 0 by omega, ↓reduceIte, Finset.mem_inter] at hx
    rw [hψ'ψ n hn1 hnk x hx.2 hx.1]
  rw [key, hact]

end Local

section Real

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν : ℝ}

/-- **The complex background of real data in `𝒟` is real**: the conjugate of the small solution is
a small solution (`isSmallSolution_conj`), and the small solution is unique (`theorem72`). -/
theorem bgFieldC_im_zero (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) (hreal : D.IsReal)
    (p : G.Ω 1 × Fin N) : (bgFieldC G a ν (bgC0 d L N) D p).im = 0 := by
  obtain ⟨hU, hS, -⟩ := theorem72 H hD
  have hc := isSmallSolution_conj D hreal hS
  have e := hU.unique (y₁ := (fun q => (starRingEnd ℂ) (bgFieldC G a ν (bgC0 d L N) D q),
    fun x => (starRingEnd ℂ) (bgMultC G a ν (bgC0 d L N) D x)))
    (y₂ := (bgFieldC G a ν (bgC0 d L N) D, bgMultC G a ν (bgC0 d L N) D)) hc hS
  have e1 := congrFun (congrArg Prod.fst e) p
  exact Complex.conj_eq_iff_im.1 e1

end Real

end Balaban.Fluctuation
