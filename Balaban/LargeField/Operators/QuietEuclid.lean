module

public import Balaban.LargeField.Operators.QuietEuclidLoc

/-!
# Lemma II.5.10, lattice part, for the quiet kernel

`quietKernel_euclid`: the quiet step kernel `K^q_k(Z')` takes the same value at corresponding
configurations under a lattice symmetry `σ` (`LatTorusSym`) mapping the region history `Hl` to `Hl'`
(`RegionIso`), the component `Zc` to `Zc'`, the output `o` to `o'` (`RelOut`) and the new internal
variables `x` to `x'` (`RelVal`).  Together with `mainActionLoc_euclid` and the `O(N)` part
(`QuietSymm.lean`) this discharges the data-covariance hypothesis of `locOp_euclid_invariant` for
quiet steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

theorem LatTorusSym.ef_eq {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M]
    [NeZero S.L] (σ : LatTorusSym S n M K) : σ.ef = σ.aff.toEquiv :=
  Equiv.ext σ.ef_aff

section OmegaLevel

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (σ : LatTorusSym S n M K) (g : Geo S n R M)
  (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hk : k + 1 ≤ K)

theorem omegaLevel_euclid (W : Set (Torus S.d (n (k + 1)))) :
    omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) (σ.ec (k + 1) '' W) =
      (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1) W).map
        (σ.levAff g hnn hk).toEquiv.toEmbedding := by
  have hal := σ.levAff_aligned g hnn hk
  have hpos : 0 < S.L ^ (k + 1) * (g.c * g.M1) := by
    have := NeZero.pos S.L; have := NeZero.pos g.c; have := NeZero.pos g.M1; positivity
  unfold omegaLevel
  rw [cubePre_map hal (by ring) hpos ⟨1, by ring⟩]
  congr 1
  exact Set.image_congr (fun y _ => σ.ec_eq_geo g hnn hk hk y)

end OmegaLevel

section Quiet

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (σ : LatTorusSym S n M K) (g : Geo S n R M)
  {Hl Hl' : RegionHistory S n R k0 K} (hiso : RegionIso σ Hl Hl') (k : ℕ)
  {Zc Zc' : Finset (Torus S.d (n (k + 1)))}
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hZc' : Zc' ∈ comps (S.omega (k + 1)) (Hl'.F.Zp (k + 1))) (hk : k + 1 ≤ K)
  (hZ : (Zc' : Set (Torus S.d (n (k + 1)))) = σ.ec (k + 1) '' (Zc : Set (Torus S.d (n (k + 1)))))
  (hI : HistImage σ.toTorusSym (locHist Hl M K (k + 1) Zc) (locHist Hl' M K (k + 1) Zc'))
  {o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1)}
  {o' : OutT N R (locHist Hl' M K (k + 1) Zc') (k + 1)}
  {x : NewCfg N (locHist Hl M K (k + 1) Zc) k} {x' : NewCfg N (locHist Hl' M K (k + 1) Zc') k}
  (ho : RelOut (k := k + 1) σ.toTorusSym o o') (hx : RelVal hI hk x x')
  (hv : EuclideanSpace ℝ (Fin N)) (cs : OpConsts)
include hiso hZ ho hx

theorem quietProd1_euclid :
    cubeProd (fun y0 => chiK (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) (N := N) cs.aw
        (cs.mu k) (cs.delta k) (fun i => hv i) g.c (n k) y0)
      (cubeFin (quietA1 (locHist Hl' M K (k + 1) Zc') k))
      (blockCfgOf g Hl'.F.hnn (le_refl k) ((Nat.le_succ k).trans hk) (subVarField N x' k)) =
    cubeProd (fun y0 => chiK (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) (N := N) cs.aw
        (cs.mu k) (cs.delta k) (fun i => hv i) g.c (n k) y0)
      (cubeFin (quietA1 (locHist Hl M K (k + 1) Zc) k))
      (blockCfgOf g Hl.F.hnn (le_refl k) ((Nat.le_succ k).trans hk) (subVarField N x k)) := by
  have hnn := Hl.F.hnn
  have hsub : RelSub hI hk x x' := ⟨subCorr_newVars hI hk, hx⟩
  have hkK : k ≤ K := by omega
  unfold cubeProd
  rw [HistImage.quietA1_eq σ hI hnn hk, cubeFin_image, Finset.prod_map]
  refine Finset.prod_congr rfl (fun y0 _ => ?_)
  simp only [Equiv.coe_toEmbedding]
  rw [σ.ec_eq_geo g hnn hkK hkK y0]
  exact chiK_euclid (σ.levAff_aligned g hnn hkK) rfl _ _ _ _ y0 _ _
    (fun y => blockCfgOf_euclid σ g hnn le_rfl hkK _ _ (fun y => hsub.read_large k y) y)

theorem quietProdPrime_euclid (A A' : Set (Torus S.d (n (k + 1))))
    (hAA' : A' = σ.ec (k + 1) '' A) :
    cubeProd (fun y0 => chiPrimeNew (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N)
        (k := k) cs.aw (cs.mu (k + 1)) (cs.delta k) (cs.nu k) (fun i => hv i)
        (c := g.c) (n := n (k + 1)) (by simp) y0
        (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1)
          {z | CubeSub (S := S) (n := n) M K (k + 1) z ((locHist Hl' M K (k + 1) Zc').Omega k)})
        (omegaLevel_blockUnion (S := S) (n := n) g.M1 g.c (k + 1) _))
      (cubeFin A')
      (blockCfgOf g Hl'.F.hnn (Nat.le_succ k) hk (subVarField N x' k),
        blockCfgOf g Hl'.F.hnn le_rfl hk (fun y => cs.z (k + 1) • outField N o' y)) =
    cubeProd (fun y0 => chiPrimeNew (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N)
        (k := k) cs.aw (cs.mu (k + 1)) (cs.delta k) (cs.nu k) (fun i => hv i)
        (c := g.c) (n := n (k + 1)) (by simp) y0
        (omegaLevel (S := S) (n := n) g.M1 g.c (k + 1)
          {z | CubeSub (S := S) (n := n) M K (k + 1) z ((locHist Hl M K (k + 1) Zc).Omega k)})
        (omegaLevel_blockUnion (S := S) (n := n) g.M1 g.c (k + 1) _))
      (cubeFin A)
      (blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (subVarField N x k),
        blockCfgOf g Hl.F.hnn le_rfl hk (fun y => cs.z (k + 1) • outField N o y)) := by
  have hnn := Hl.F.hnn
  have hsub : RelSub hI hk x x' := ⟨subCorr_newVars hI hk, hx⟩
  unfold cubeProd
  rw [hAA', cubeFin_image, Finset.prod_map]
  refine Finset.prod_congr rfl (fun y0 _ => ?_)
  simp only [Equiv.coe_toEmbedding]
  rw [σ.ec_eq_geo g hnn hk hk y0]
  have hW : {z | CubeSub (S := S) (n := n) M K (k + 1) z ((locHist Hl' M K (k + 1) Zc').Omega k)} =
      σ.ec (k + 1) '' {z | CubeSub (S := S) (n := n) M K (k + 1) z
        ((locHist Hl M K (k + 1) Zc).Omega k)} := by
    have := hI.Omega k
    show {z | CubeSub (S := S) (n := n) M K (k + 1) z ((locHist Hl' M K (k + 1) Zc').Omega k)} = _
    rw [hI.Omega k]
    exact σ.cubeSet_eq hk _
  refine chiPrimeNew_euclid (σ.levAff_aligned g hnn hk) _ cs.aw (cs.mu (k + 1)) (cs.delta k)
    (cs.nu k) (fun i => hv i) y0 _ _ _ _ ?_ _ _ ?_ ?_
  · rw [hW]; exact omegaLevel_euclid σ g hnn hk _
  · intro y
    exact blockCfgOf_euclid σ g hnn (Nat.le_succ k) hk _ _ (fun y => hsub.read_large k y) y
  · intro y
    exact blockCfgOf_euclid σ g hnn le_rfl hk (fun y => cs.z (k + 1) • outField N o y)
      (fun y => cs.z (k + 1) • outField N o' y) (fun y => by simp only [ho y]) y

theorem quietProd4_euclid :
    cubeProd (fun y0 => chiNext (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N) cs.aw
        (cs.mu (k + 1)) (cs.delta (k + 1)) (fun i => hv i) g.c (n (k + 1)) k y0)
      (cubeFin (quietA4 (locHist Hl' M K (k + 1) Zc') k))
      (blockCfgOf g Hl'.F.hnn le_rfl hk (outField N o')) =
    cubeProd (fun y0 => chiNext (M1 := g.M1) (N₁ := g.c * n (k + 1)) (L := S.L) (N := N) cs.aw
        (cs.mu (k + 1)) (cs.delta (k + 1)) (fun i => hv i) g.c (n (k + 1)) k y0)
      (cubeFin (quietA4 (locHist Hl M K (k + 1) Zc) k))
      (blockCfgOf g Hl.F.hnn le_rfl hk (outField N o)) := by
  have hnn := Hl.F.hnn
  unfold cubeProd
  rw [HistImage.quietA4_eq σ hI hnn hk, cubeFin_image, Finset.prod_map]
  refine Finset.prod_congr rfl (fun y0 _ => ?_)
  simp only [Equiv.coe_toEmbedding]
  rw [σ.ec_eq_geo g hnn hk hk y0]
  exact chiK_euclid (σ.levAff_aligned g hnn hk) rfl _ _ _ _ y0 _ _
    (fun y => blockCfgOf_euclid σ g hnn le_rfl hk _ _ (fun y => ho y) y)

open Classical in
theorem quietIndicator_euclid :
    (if InUnionDomainR (locGen g Hl' k Zc' hZc' hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
        (locData g Hl' k Zc' hZc' hk o' x' hv) then (1 : ℝ) else 0) =
      (if InUnionDomainR (locGen g Hl k Zc hZc hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
        (locData g Hl k Zc hZc hk o x hv) then (1 : ℝ) else 0) := by
  classical
  refine if_congr ?_ rfl rfl
  rw [← locData_sym σ g hiso k hZc hZc' hk hZ hI ho hx hv]
  exact (locGen_latSymm σ g hiso k hZc hZc' hk hZ).inUnionDomainR_sym_iff _

section Rest

variable (hrem : ∀ j, Hl.rem j = ∅) (hrem' : ∀ j, Hl'.rem j = ∅)
include hrem hrem'

theorem quietChiNew_euclid :
    chiNew (locHist Hl' M K (k + 1) Zc') k
      (Hl'.histGen (M := M) (K' := K) le_rfl hrem' Hl'.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (fineSet (S := S) (n := n) M K (k + 1) (Zc' : Set (Torus S.d (n (k + 1)))))
      cs.delta cs.p0 cs.Cpsi
      (subMultiscaleField N (locHist Hl' M K (k + 1) Zc') (k + 1)
          (Vblk R (locHist Hl' M K (k + 1) Zc') (k + 1)) x' o',
        subFluctField N (locHist Hl' M K (k + 1) Zc') (k + 1) x') =
    chiNew (locHist Hl M K (k + 1) Zc) k
      (Hl.histGen (M := M) (K' := K) le_rfl hrem Hl.F.ok.two_le_L (fun j _ _ => g.hRlow j))
      (fineSet (S := S) (n := n) M K (k + 1) (Zc : Set (Torus S.d (n (k + 1)))))
      cs.delta cs.p0 cs.Cpsi
      (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
          (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o,
        subFluctField N (locHist Hl M K (k + 1) Zc) (k + 1) x) := by
  have hnn := Hl.F.hnn
  have hsub : RelSub hI hk x x' := ⟨subCorr_newVars hI hk, hx⟩
  refine chiNew_euclid σ hI ?_ ?_ hk cs.delta cs.p0 cs.Cpsi
    (fun j y => subMultiscaleField_euclid hk ho hsub j y)
    (fun j y => subFluctField_euclid hk hsub j y)
  · intro j
    have := flowOmega_map (Hl.toSeq le_rfl hrem) (Hl'.toSeq le_rfl hrem') hnn σ.aff σ.align ?_ j
    · rw [σ.ef_eq]; exact this
    · intro j' hj'
      cases j' with
      | zero => simp [RegionSeq.OmegaAt]
      | succ i =>
        show (Hl'.F.step i).Omega = _ '' (Hl.F.step i).Omega
        rw [hiso.omega hj']
        exact Set.image_congr (fun y _ => σ.ec_eq hnn hj' y)
  · rw [hZ, σ.fineSet_image hk]

open Classical in
/-- **Lemma II.5.10 (lattice part) for the explicit quiet kernel**: the quiet step kernel
`K^q_k(Z')` is invariant under a lattice Euclidean symmetry `σ` mapping the region history `Hl` to
`Hl'` (`RegionIso`), the component `Zc` to `Zc'`, the localized histories to each other
(`HistImage`), the output `o` to `o'` and the new internal variables `x` to `x'`; the external
direction `h = hv` is unchanged. -/
theorem quietKernel_euclid :
    quietKernel g Hl' k Zc' hZc' hk cs hrem' o' x' hv =
      quietKernel g Hl k Zc hZc hk cs hrem o x hv := by
  have hnn := Hl.F.hnn
  unfold quietKernel
  rw [gaussProd_euclid hk cs ho hx, quietProd1_euclid σ g hiso k hk hZ hI ho hx hv cs,
    quietProdPrime_euclid σ g hiso k hk hZ hI ho hx hv cs
      (quietA2 (locHist Hl M K (k + 1) Zc) k) (quietA2 (locHist Hl' M K (k + 1) Zc') k)
      (HistImage.quietA2_eq σ hI hnn hk),
    quietProdPrime_euclid σ g hiso k hk hZ hI ho hx hv cs
      (quietA3 (locHist Hl M K (k + 1) Zc) k) (quietA3 (locHist Hl' M K (k + 1) Zc') k)
      (HistImage.quietA3_eq σ hI hnn hk),
    quietProd4_euclid σ g hiso k hk hZ hI ho hx hv cs,
    quietChiNew_euclid σ g hiso k hk hZ hI ho hx cs hrem hrem',
    quietIndicator_euclid σ g hiso k hZc hZc' hk hZ hI ho hx hv cs,
    mainActionLoc_euclid σ g hiso k hZc hZc' hk hZ hI ho hx hv cs hrem hrem']

end Rest

end Quiet

end Balaban.LargeField
