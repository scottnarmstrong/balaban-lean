/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.SmallFactorChi
public import Balaban.LargeField.R.ChiBridgeHist
public import Balaban.LargeField.Operators.QuietIndep
public import Balaban.LargeField.R.HgeoDischarge
public import Balaban.LargeField.R.ZeroDomainD
public import Balaban.LargeField.R.RRemovedKernel

/-!
# Locality of the characteristic functions of the removed kernel (Lemma III.1.5, III.8.4 (i))

The premises `hind`, `hf`, `hdom` of the identities of `RRemovedKernel.lean` say that an object
takes the same value at two outputs `o, o'` that agree off `Z₀`
(`(remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2`).  Here:

* `outField_eq_of_split_snd`: such outputs give the same field `ψ_k` on every block outside `Z₀`;
* `chiTilde_congr`, `chiProd_congr_of_off`, `chiS_congr`, `chiS_congr_zzero`, `chiZero_congr`,
  `chiDD_congr`: the congruence of the characteristic functions for fields that agree off `Z₀`,
  under the geometric hypotheses "the blocks of `Z₀` lie in the fine set `Z_0`" and "the sites of
  `□^{∼3}` of the cubes of the product avoid `Z_0`" (read sets of `chiK`, `chiK_stencil`);
* `zzero_subset_gaussBlocks`: the blocks of `Z₀` are Gaussian blocks `Ω^c_{k+1} ∩ Z'`.

The domain, the exponent and the identity instances are in `RRemovedLocalityPre.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

section OutField

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ) (Z0 : Set (BlockAt S n M K k))

/-- Outputs that agree off `Z₀` give the same field `ψ_k` on every block outside `Z₀`. -/
theorem outField_eq_of_split_snd {o o' : OutT N R a k}
    (h : (remZeroSplit a k Z0 o).2 = (remZeroSplit a k Z0 o').2) {y : BlockAt S n M K k}
    (hy : y ∉ Z0) : outField N o y = outField N o' y := by
  classical
  unfold outField
  by_cases hV : y ∈ Vblk R a k
  · simp only [hV, ↓reduceDIte]
    have := congrFun h ⟨y, hV, hy⟩
    simpa [remZeroSplit_apply, restrictOutPart] using this
  · simp only [hV, ↓reduceDIte]

end OutField

section Chi

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (a : LocalHistory S n M K) (k : ℕ)

/-- **`χ̃_k` does not read `ψ_k` on `Z₀`**: if `ψ, ψ'` agree on the blocks outside `Z₀` and every
block of `Z₀` lies in the fine set `Z0f` (`Z₀` is a set of `k`-blocks whose sites lie in the fine
set `Z_0` removed in `tildeRegion`), then `χ̃_k ψ = χ̃_k ψ'`. -/
theorem chiTilde_congr (hkK : k ≤ K) (Z0 : Set (BlockAt S n M K k))
    (Z0f : Set (Torus S.d (M * n K * S.L ^ K)))
    (hZ0 : ∀ b ∈ Z0, BlockSub (S := S) (n := n) (M := M) (K := K) k b Z0f) (δk : ℝ)
    {ψ ψ' : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)} (hψ : ∀ y, y ∉ Z0 → ψ y = ψ' y) :
    chiTilde a k Z0f δk ψ = chiTilde a k Z0f δk ψ' := by
  have hnot : ∀ y : BlockAt S n M K k,
      BlockSub (S := S) (n := n) (M := M) (K := K) k y (tildeRegion a k Z0f) → y ∉ Z0 := by
    intro y hy hyZ
    obtain ⟨x, hx⟩ := exists_site_in_block (S := S) (n := n) (M := M) hkK y
    exact (hy x hx).1.2 (hZ0 y hyZ x hx)
  refine charFn_congr ?_
  unfold ChiTildeProp PsiTildeOne PsiTildeSet
  refine and_congr ?_ ?_
  · refine forall_congr' fun y => forall_congr' fun hy => forall_congr' fun y' =>
      forall_congr' fun hy' => forall_congr' fun _ => ?_
    rw [hψ y (hnot y hy), hψ y' (hnot y' hy')]
  · refine forall_congr' fun y => forall_congr' fun hy => ?_
    rw [hψ y (hnot y hy)]


variable (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (cs : OpConsts)
  (hv : EuclideanSpace ℝ (Fin N))

/-- **A product of cube characteristic functions does not read `ψ_q` on `Z₀`**: `χ_q(□)` reads
`ψ_q` on the blocks of the cubes of `□^{∼3}` (`chiK_stencil`); if every such block (the image of
a site of `□^{∼3}` in the history torus) lies outside `Z₀`, fields that agree off `Z₀` give the
same product.  `hsep` is the geometric hypothesis: the sites of `□^{∼3}` of the cubes `□ ∈ A`
avoid the fine set `Z0f` of which the blocks of `Z₀` are subsets. -/
theorem chiProd_congr_of_off (hL : 2 ≤ S.L) (q : ℕ) (hqK : q ≤ K) (δ : ℝ)
    (A : Set (Torus S.d (n q))) (Z0 : Set (BlockAt S n M K q))
    (Z0f : Set (Torus S.d (M * n K * S.L ^ K)))
    (hZ0 : ∀ b ∈ Z0, BlockSub (S := S) (n := n) (M := M) (K := K) q b Z0f)
    (hsep : ∀ y0 ∈ cubeFin (S := S) A, ∀ x : Torus S.d (g.M1 * (g.c * n q) * S.L ^ q),
      blockMap (S.L ^ q * (g.c * g.M1)) (n q) x ∈ nbhd 3 {y0} →
        torusCast (histFine_eq g hnn hqK) x ∉ Z0f)
    {ψ ψ' : BlockAt S n M K q → EuclideanSpace ℝ (Fin N)} (hψ : ∀ y, y ∉ Z0 → ψ y = ψ' y) :
    chiProd g hnn cs hv q hqK δ A ψ = chiProd g hnn cs hv q hqK δ A ψ' := by
  unfold chiProd cubeProd
  refine Finset.prod_congr rfl fun y0 hy0 => ?_
  refine chiK_stencil _ _ _ _ hL (by have := g.hc; omega) (by simp) y0 ?_
  intro x hx
  have hb : torusCast (histScale_eq g.hM hnn (le_refl q) hqK)
      (jBlock S.d S.L (g.M1 * (g.c * n q)) q q x) ∉ Z0 := by
    intro hmem
    have hj := jBlock_torusCast (L := S.L) (N₀ := g.M1 * (g.c * n q)) (N₀' := M * n K)
      (k := q) (K := K) (j := q) le_rfl hqK (histFine_eq g hnn hqK)
      (histScale_eq g.hM hnn (le_refl q) hqK) x
    exact hsep y0 hy0 x hx (hZ0 _ hmem _ hj)
  funext j
  unfold blockCfgOf
  rw [hψ _ hb]

/-- **`χ_S` does not read `ψ_k` on `Z₀`** (Definition III.5.1 item 2). -/
theorem chiS_congr (hL : 2 ≤ S.L) (hkK : k ≤ K) (Z0DD : Set (Torus S.d (M * n K * S.L ^ K)))
    (Z0 : Set (BlockAt S n M K k)) (Z0f : Set (Torus S.d (M * n K * S.L ^ K)))
    (hZ0 : ∀ b ∈ Z0, BlockSub (S := S) (n := n) (M := M) (K := K) k b Z0f)
    (hsep : ∀ y0 ∈ cubeFin (S := S) (chiSCubes a k Z0DD),
      ∀ x : Torus S.d (g.M1 * (g.c * n k) * S.L ^ k),
        blockMap (S.L ^ k * (g.c * g.M1)) (n k) x ∈ nbhd 3 {y0} →
          torusCast (histFine_eq g hnn hkK) x ∉ Z0f)
    {ψ ψ' : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)} (hψ : ∀ y, y ∉ Z0 → ψ y = ψ' y) :
    chiS a k g hnn cs hv hkK Z0DD ψ = chiS a k g hnn cs hv hkK Z0DD ψ' :=
  chiProd_congr_of_off g hnn cs hv hL k hkK _ _ Z0 Z0f hZ0 hsep hψ

/-- **`χ^0` does not read `ψ_{k₁}` on `Z₀`** (Definition III.5.1 item 3; `Z₀` a set of
`k₁`-blocks): `ψ'_{k₁}` is `ψ_{k₁}` or the constant `ψ_0`, so it agrees off `Z₀` with `ψ'_{k₁}`
of a field that agrees with `ψ_{k₁}` off `Z₀`. -/
theorem chiZero_congr (hL : 2 ≤ S.L) (k1 : ℕ) (hk1K : k1 ≤ K) (U : Set (Torus S.d (n k1)))
    (Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (psi0 : EuclideanSpace ℝ (Fin N))
    (Z0 : Set (BlockAt S n M K k1)) (Z0f : Set (Torus S.d (M * n K * S.L ^ K)))
    (hZ0 : ∀ b ∈ Z0, BlockSub (S := S) (n := n) (M := M) (K := K) k1 b Z0f)
    (hsep : ∀ y0 ∈ cubeFin (S := S) (chiZeroCubes k1 U),
      ∀ x : Torus S.d (g.M1 * (g.c * n k1) * S.L ^ k1),
        blockMap (S.L ^ k1 * (g.c * g.M1)) (n k1) x ∈ nbhd 3 {y0} →
          torusCast (histFine_eq g hnn hk1K) x ∉ Z0f)
    {ψ ψ' : BlockAt S n M K k1 → EuclideanSpace ℝ (Fin N)} (hψ : ∀ y, y ∉ Z0 → ψ y = ψ' y) :
    chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ = chiZero g hnn cs hv k1 hk1K U Lam U3 psi0 ψ' := by
  unfold chiZero
  refine chiProd_congr_of_off g hnn cs hv hL k1 hk1K _ _ Z0 Z0f hZ0 hsep ?_
  intro y hy
  unfold psiPrime
  simp only [hψ y hy]

/-- **`χ''` reads `δψ` exactly on the blocks of `D''`**: fields `δψ` that agree on the blocks
`y` of layer `j` with `BlockSub j y (D'' ∩ layer j)` give the same value. -/
theorem chiDD_congr {ϱ : ℝ} (B : GeneratingSet S.d S.L (M * n K) K ϱ)
    (Zk1 Lam U3 : Set (Torus S.d (M * n K * S.L ^ K))) (δ1 : ℕ → ℝ)
    {dpsi dpsi' : MultiField S n M K N}
    (h : ∀ j, 1 ≤ j → j ≤ K → ∀ y : BlockAt S n M K j,
      BlockSub (S := S) (n := n) (M := M) (K := K) j y
        (ddRegion a k B Zk1 Lam U3 ∩ {x | x ∈ B.layer j}) → dpsi j y = dpsi' j y) :
    chiDD a k B Zk1 Lam U3 δ1 dpsi = chiDD a k B Zk1 Lam U3 δ1 dpsi' := by
  refine charFn_congr ?_
  unfold ChiDDProp
  refine forall_congr' fun j => forall_congr' fun h1 => forall_congr' fun h2 =>
    forall_congr' fun y => forall_congr' fun hy => ?_
  rw [h j h1 h2 y hy]

end Chi


section Geometry

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M]

/-- **`Z₀` consists of Gaussian blocks** (Lemma III.3.2 (d)): a set `Z₀` of `(k+1)`-blocks all of
whose sites lie in the fine set `Z_0` (`fineZzero`) of a component `Z'` of `Z_{k+1}` lies in
`gaussBlocks`, the blocks of `Ω^c_{k+1} ∩ Z'` of the localized history.  Operative radii
`R_j = R_base λ̂_j²`. -/
theorem zzero_subset_gaussBlocks (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) {k : ℕ} (hK : k + 1 ≤ K)
    (Z' : H.Comp (k + 1)) (Z0 : Set (BlockAt S n S.M K (k + 1)))
    (hZ0 : ∀ b ∈ Z0, BlockSub (S := S) (n := n) (M := S.M) (K := K) (k + 1) b
      (H.fineZzero (k + 1) Z')) :
    Z0 ⊆ gaussBlocks (H.localHistory S.M K (k + 1) Z') k := by
  intro b hb
  rw [gaussBlocks_iff hK Z' b]
  obtain ⟨x0, hx0⟩ := exists_site_in_block (S := S) (n := n) (M := S.M) hK b
  have hx : blockMap (S.L ^ (k + 1)) (S.M * n (k + 1)) (torusCast (H.fineTorus_eq hK) x0) ∈
      H.Zzero (k + 1) Z' := by
    rw [blockMap_torusCast]
    exact hZ0 b hb x0 hx0
  have hc := blockCube_eq_cubeMap H.F.hnn hK hx0
  have hcm := H.cubeMap_torusCast (k := k + 1) (j := k + 1) hK x0
  refine ⟨?_, ?_⟩
  · rw [hc, ← hcm]
    exact (H.Zzero_margin hR hK (by omega) Z' hx).2.2
  · rw [hc, ← hcm]
    exact H.Zzero_not_mem_Omega_top hR hK Z' hx


variable {N : ℕ} (g : Geo S n R S.M) (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))

/-- **`χ_S` does not read `ψ_k` on `Z₀`, for a component `Z` of `Z_k`** (Lemma III.5.0 (a)): the
geometric hypothesis `hsep` of `chiS_congr` is `hgeo_two_fine`, for the localized history of `Z`,
`Z''_0 =` the fine set of `ZzeroDD` and `Z_0 =` `fineZzero`; `Z₀` is a set of `k`-blocks inside
`fineZzero`. -/
theorem chiS_congr_zzero {k : ℕ} (hkK : k ≤ K) (hk : 1 ≤ k) (Z : H.Comp k)
    (Z0 : Set (BlockAt S n S.M K k))
    (hZ0 : ∀ b ∈ Z0, BlockSub (S := S) (n := n) (M := S.M) (K := K) k b (H.fineZzero k Z))
    {ψ ψ' : BlockAt S n S.M K k → EuclideanSpace ℝ (Fin N)} (hψ : ∀ y, y ∉ Z0 → ψ y = ψ' y) :
    chiS (H.localHistory S.M K k Z) k g H.F.hnn cs hv hkK
        (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψ =
      chiS (H.localHistory S.M K k Z) k g H.F.hnn cs hv hkK
        (fineSet (S := S) (n := n) S.M K k (H.ZzeroDD k Z)) ψ' := by
  refine chiS_congr _ k g H.F.hnn cs hv H.F.ok.two_le_L hkK _ Z0 (H.fineZzero k Z) hZ0 ?_ hψ
  intro y0 hy0 x hx
  exact (H.hgeo_two_fine hkK hk Z y0 hy0 _ (by rwa [← blockMap_level_eq_cubeMap H g hkK x])).2

end Geometry


end Balaban.LargeField
