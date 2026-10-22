/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFGasCfg
public import Balaban.Spine.FinalLFSplit
public import Balaban.LargeField.R.RGasCoreBlock

/-!
# The records as heavy objects of the record gas, and a history in the variables of the gas (A6-4)

A realized record `r` (cubes `Y`) owns the internal variables of its operator (`recVars`) and the
field `ψ_k` on the `k`-blocks of `Y`; its kernel also reads `ψ_k` on the blocks of the cubes at
distance `≤ r₀ = ⌊R_{k-1}⌋ + 2` of `Y` (`recBlk`, `Vblk_subset_recBlk`). Its weight in the record
gas (`recTauG`) is its kernel `K e^b` times the densities of its own variables against their
probability measures (`blkDens`, `recTau`); the densities of `ψ_k` on the collar stay with the
characteristic function of the small-field region, outside the record (Lebesgue measure on the
collar is not finite against the kernel alone). The weight reads only the variables sitting at the
sites of `dblNbhd ω_k Y` (`pDepOn_recTauG`), since `2 r₀ < ω_k` (`two_mul_collarR_lt_omega`); so
its support in the gas is `dblNbhd ω_k Y`, and two records have disjoint supports iff they are
separated (`recSep_iff_disjoint`). The block sets `recBlk` of the components of a history of the
large-field half are pairwise disjoint (`disjoint_recBlk`); off their union (`lfOmega`, the deep
region `Ω_𝔸` of P7 (4.2)) no kernel reads `ψ_k`.

**The last integral of a history in the variables of the gas**
(`lastHistInt_eq_iterated_of_integrable`): `∫ρ_𝔸 = E_ψ E_x ∏_Z (ρ_ψ(Z) τ_Z) · ρ_ψ(C_𝔸) I_𝔸`, the
expectations for the product measures of the gas, `ρ_ψ(C_𝔸)` the density on the collar, `I_𝔸`
the regional integral over `Ω_𝔸` (`lfRegInt`), under the integrability of the integrand of the
Fubini split (as for `lastHistInt_eq_regional_of_integrable`).

* `collarR`, `recBlk`, `Vblk_subset_recBlk`, `two_mul_collarR_lt_omega`, `disjoint_recBlk`;
* `blkDens`, `recTauG`, **`pDepOn_recTauG`**, `depOn_recTauG`;
* `lfOmega`, `collarDens`, `psiDens_compl_lfOmega`, **`lastHistInt_eq_iterated_of_integrable`**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  RegionHistory
open scoped ENNReal NNReal

namespace Balaban.RootFSpine

/-! ### The blocks of a record -/

section Blocks

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {k : ℕ}

/-- The collar radius `r₀ = ⌊R_{k-1}⌋ + 2` of the last step (P7 (4.2): `Ω_{k+1} = Ω'_{k+1}`). -/
noncomputable def collarR (R : ℕ → ℝ) (k : ℕ) : ℕ := ⌊R (k - 1)⌋₊ + 2

/-- **The `k`-blocks of a set of cubes and of its collar**: the blocks of the cubes at index
distance `≤ r₀` of the set. -/
def recBlk (R : ℕ → ℝ) (Y : Finset (Torus S.d (n k))) : Set (BlockAt S n M K k) :=
  {y | blockCube S n M K k y ∈ nbhd (collarR R k) (Y : Set (Torus S.d (n k)))}

/-- **The blocks read by the kernel of a component lie in the blocks of its record.** -/
theorem Vblk_subset_recBlk (H : RegionHistory S n R k0 K) (hkK : k ≤ K) (c : H.Comp k) :
    Vblk R (H.localHistory M K k c) k ⊆ recBlk (M := M) R c.1 := by
  intro y hy
  have h1 : Vcubes R (H.localHistory M K k c) k ⊆
      nbhd (collarR R k) (c.1 : Set (Torus S.d (n k))) := by
    unfold Vcubes thick collarR
    rw [nbhd_nbhd]
    exact nbhd_mono (by omega) (Zcubes_loc_sub (H := H) hkK c)
  exact h1 hy

/-- **The collar is thinner than half the separation**: `2 r₀ < ω_k` (`k ≥ 1`). -/
theorem two_mul_collarR_lt_omega (H : RegionHistory S n R k0 K) [NeZero S.M] (hk : 1 ≤ k) :
    2 * collarR R k < S.omega k := by
  have h := H.block_halo_radius_lt_omega hk
  have := Nat.pos_of_ne_zero (NeZero.ne S.L)
  unfold collarR
  omega

omit [NeZero M] [NeZero S.L] in
/-- **The blocks of separated sets of cubes are disjoint** (`2 r₀ < ω_k`). -/
theorem disjoint_recBlk (htie : 2 * collarR R k < S.omega k) {Y Y' : Finset (Torus S.d (n k))}
    (hsep : ∀ x ∈ Y, ∀ x' ∈ Y', S.omega k ≤ supDist x x') :
    Disjoint (recBlk (M := M) (K := K) R Y) (recBlk (M := M) (K := K) R Y') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨x, hx, hd⟩ := mem_nbhd.1 hy
  obtain ⟨x', hx', hd'⟩ := mem_nbhd.1 hy'
  have h1 := supDist_triangle x (blockCube S n M K k y) x'
  have h3 : supDist x (blockCube S n M K k y) = supDist (blockCube S n M K k y) x :=
    supDist_comm _ _
  have h2 := hsep x hx x' hx'
  omega

end Blocks

/-! ### The weight of a record in the variables of the gas -/

section Weight

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

/-- The cubes of the source of a realized record are those of the record. -/
theorem lfSrc_cubes (r : ↥(lfAllRecs (M := M) rep.hist k)) : (lfSrc r).2.1 = r.1.1 :=
  congrArg Prod.fst (compRec_lfSrc r)

include hkK in
/-- The blocks read by the kernel of a realized record lie in the blocks of the record. -/
theorem Vblk_lfSrc_subset_recBlk (r : ↥(lfAllRecs (M := M) rep.hist k)) :
    Vblk R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ⊆ recBlk (M := M) R r.1.1 := by
  have h := Vblk_subset_recBlk (M := M) (lfSrc r).1.H hkK (lfSrc r).2
  rwa [lfSrc_cubes] at h

/-- **The weight of a record reads the field only on the blocks read by its kernel.** -/
theorem recW_congr_psi (r : ↥(lfAllRecs (M := M) rep.hist k))
    {ψ ψ' : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)}
    (h : ∀ y ∈ Vblk R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k, ψ y = ψ' y)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (z : GCfgOn N (recVars rep hkK r)) :
    recW rep hkK r ψ hv g z = recW rep hkK r ψ' hv g z := by
  have e : outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ψ =
      outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ψ' := funext fun y => h y.1 y.2
  unfold recW
  rw [e]

/-- The variables of a realized record lie in its cubes. -/
theorem cubeMap_gSite_mem (r : ↥(lfAllRecs (M := M) rep.hist k)) {q : GVar S n M K k}
    (hq : q ∈ recVars rep hkK r) : cubeMap n S.L M K k (gSite hkK q) ∈ r.1.1 := by
  obtain ⟨p, -, rfl⟩ := hq
  have h1 : gSite hkK p.1 ∈ varSet ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) p.1.1 p.1.2.1 :=
    p.2 _ (jBlock_gSite hkK p.1)
  have h2 := varSet_localHistory_subset (M := M) (lfSrc r).1.H (lfSrc r).2 _ _ h1
  change cubeMap n S.L M K k (gSite hkK p.1) ∈ ((lfSrc r).2.1 : Set (Torus S.d (n k))) at h2
  rwa [lfSrc_cubes] at h2

open Classical in
/-- The density of Lebesgue measure on `ψ_k` against the Gaussians on the blocks of a set of
cubes. -/
noncomputable def blkDens (Y : Finset (Torus S.d (n k)))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∏ y ∈ Finset.univ.filter (fun y => blockCube S n M K k y ∈ Y), gaussInvDens N (ψ y)

/-- **The weight of a realized record in the variables of the gas**: the densities of `ψ_k` on its
blocks times its weight with the density of its internal variables (`recTau`). -/
noncomputable def recTauG (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (Φ : PCfg S n M K k N) : ℂ :=
  (blkDens r.1.1 (psiPart Φ) : ℂ) * recTau rep hkK r (psiPart Φ) hv g (gPart Φ)

/-- **The weight of a record reads only the variables sitting at the sites of `dblNbhd ω_k Y`**
(`Y` the cubes of the record; `2 r₀ < ω_k`). -/
theorem pDepOn_recTauG (htie : 2 * collarR R k < S.omega k)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    PDepOn (M := M) hkK (dblNbhd (S.omega k) r.1.1) (recTauG rep hkK r hv g) := by
  intro Φ Φ' h
  have hψ : ∀ y ∈ recBlk (M := M) (K := K) R r.1.1, psiPart Φ y = psiPart Φ' y := by
    intro y hy
    refine h (Sum.inr y) ?_
    obtain ⟨x, hx, hd⟩ := mem_nbhd.1 hy
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, ?_⟩
    have := (supDist_tDouble_le_iff x (blockCube S n M K k y) (collarR R k)).2
      (by rw [supDist_comm]; exact hd)
    change supDist (tDouble x) (tDouble (blockCube S n M K k y)) ≤ S.omega k - 1
    omega
  have hx : restrictAll (recVars rep hkK r) (gPart Φ) =
      restrictAll (recVars rep hkK r) (gPart Φ') := by
    funext q
    refine h (Sum.inl q.1) ?_
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, _, cubeMap_gSite_mem rep hkK r q.2, ?_⟩
    change supDist (tDouble (cubeMap n S.L M K k (gSite hkK q.1)))
      (tDouble (cubeMap n S.L M K k (gSite hkK q.1))) ≤ S.omega k - 1
    rw [supDist_self]
    exact Nat.zero_le _
  have hd : blkDens r.1.1 (psiPart Φ) = blkDens r.1.1 (psiPart Φ') := by
    classical
    unfold blkDens
    exact Finset.prod_congr rfl fun y hy => by
      rw [hψ y (subset_nbhd _ _ (Finset.mem_filter.1 hy).2)]
  unfold recTauG recTau
  rw [hd, hx, recW_congr_psi rep hkK r (fun y hy => hψ y (Vblk_lfSrc_subset_recBlk rep hkK r hy))]

/-- **The support of a record in the gas**: its weight, as a function of the configuration of the
sites, depends only on the sites of `dblNbhd ω_k Y`. -/
theorem depOn_recTauG (htie : 2 * collarR R k < S.omega k)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    Polymer.DepOn (dblNbhd (S.omega k) r.1.1)
      (fun Φc => recTauG rep hkK r hv g (regroup (S := S) (M := M) hkK N Φc)) :=
  depOn_comp_regroup hkK (pDepOn_recTauG rep hkK htie r hv g)

end Weight

/-! ### The last integral of a history in the variables of the gas -/

section History

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
  (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- **The deep region of a history** (`Ω_𝔸`, P7 (4.2)): the `k`-blocks outside the blocks of all
its components. -/
def lfOmega (A : LabHist S n R k0 K) : Set (BlockAt S n M K k) :=
  {y | ∀ c : PostComp A k, y ∉ recBlk (M := M) (K := K) R c.1.1}

open Classical in
/-- The density of Lebesgue measure on `ψ_k` against the Gaussians on the collar of a history: the
blocks outside the deep region and outside the cubes of the components. -/
noncomputable def collarDens (A : LabHist S n R k0 K)
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∏ y ∈ Finset.univ.filter (fun y => y ∉ lfOmega (M := M) (R := R) A ∧
    ∀ c : PostComp A k, blockCube S n M K k y ∉ c.1.1), gaussInvDens N (ψ y)

/-- **The density of `ψ_k` off the deep region is the product of the densities on the blocks of
the components and of the density on the collar.** -/
theorem psiDens_compl_lfOmega (A : LabHist S n R k0 K)
    [Fintype {y : BlockAt S n M K k // y ∉ lfOmega (R := R) A}]
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    psiDens N (fun i : {y : BlockAt S n M K k // y ∉ lfOmega (R := R) A} => ψ i.1) =
      (∏ c : PostComp A k, blkDens (N := N) (M := M) (K := K) c.1.1 ψ) *
        collarDens (N := N) A ψ := by
  classical
  have hdisj : ((Finset.univ : Finset (PostComp A k)) : Set (PostComp A k)).PairwiseDisjoint
      fun c => Finset.univ.filter (fun y => blockCube S n M K k y ∈ c.1.1) := by
    intro c _ c' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro y _ h1 h2
    exact hne (Subtype.ext (Subtype.ext (comp_eq_of_mem c.1.2 c'.1.2 h1 h2)))
  unfold psiDens blkDens collarDens
  rw [← Finset.prod_subtype (Finset.univ.filter (· ∉ lfOmega (R := R) A)) (fun y => by simp)
    (fun y => gaussInvDens N (ψ y)), ← Finset.prod_biUnion hdisj,
    ← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (· ∉ lfOmega (R := R) A))
      (fun y => ∃ c : PostComp A k, blockCube S n M K k y ∈ c.1.1)]
  congr 1
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨-, c, hc⟩
      exact ⟨c, hc⟩
    · rintro ⟨c, hc⟩
      refine ⟨fun hy => hy c (subset_nbhd _ _ hc), c, hc⟩
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists]

open Classical in
/-- **The last integral of a history of the large-field half in the variables of the gas**:
`∫ρ_𝔸 = E_ψ E_x ∏_Z (ρ_ψ(Z) τ_Z) · ρ_ψ(C_𝔸) I_𝔸(ψ|_{Ω_𝔸^c}, x)`, the expectations for the products
of the probability measures (`gaussPi`, `gProbAll`), `ρ_ψ(Z)` the density of `ψ_k` on the blocks of
the cubes of `Z` (`blkDens`), `τ_Z` the weight of the record of `Z` with the density of its internal
variables (`recTau`), `ρ_ψ(C_𝔸)` the density of `ψ_k` on the collar (`collarDens`), `I_𝔸` the
regional integral over the deep region `Ω_𝔸` (`lfRegInt`). The premise is the integrability of the
integrand of the Fubini split (`lastHistInt_eq_regional_of_integrable`). -/
theorem lastHistInt_eq_iterated_of_integrable (hN : 1 ≤ N) {A : LabHist S n R k0 K}
    (hA : A ∈ lfHist rep.hist k)
    (hint : Integrable (fun q : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) ×
        GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
          (postOp geo cs rep.SD rep.KD A C.hkK) =>
      gWeight (fun c : PostComp A k => A.H.localHistory M K k c.1) k
          (postOp geo cs rep.SD rep.KD A C.hkK) q.1 hv g q.2 *
        integrand2 (fun c : PostComp A k => A.H.localHistory M K k c.1)
          (postOp geo cs rep.SD rep.KD A C.hkK)
          (fun c => fineSet (S := S) (n := n) M K k (c.1.1 : Set (Torus S.d (n k)))) C vc rep A
          (A.H.step k).Z q.1 hv g q.2)
      (volume.prod (gMeasure (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A C.hkK)))) :
    lastHistInt C vc rep hv g A =
      ∫ ψ, ∫ Φg, (∏ c : PostComp A k, (blkDens (N := N) (M := M) (K := K) c.1.1 ψ : ℂ) *
            recTau rep C.hkK (recOfComp rep hA c) ψ hv g Φg) *
          ((collarDens (N := N) A ψ : ℂ) *
            lfRegInt C vc rep A (lfOmega (R := R) A) hv g (fun y => ψ y.1)
              ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A C.hkK c).A)
                (pairwise_disjoint_postOp rep C.hkK A)).symm (restrictAll _ Φg)))
        ∂(gProbAll S n M K k N) ∂(gaussPi N (BlockAt S n M K k)) := by
  have hrem := (mem_lfHist.1 hA).2.2
  have hΩ : ∀ c : PostComp A k, ∀ y ∈ lfOmega (R := R) A,
      y ∉ Vblk R (A.H.localHistory M K k c.1) k :=
    fun c y hy hV => hy c (Vblk_subset_recBlk (M := M) A.H C.hkK c.1 hV)
  rw [lastHistInt_eq_regional_of_integrable C vc rep A hv g hrem (lfOmega (R := R) A) hΩ hint,
    integral_volume_pi N]
  rw [show gaussPi N {y : BlockAt S n M K k // y ∉ lfOmega (R := R) A} =
      Measure.pi fun _ : {y : BlockAt S n M K k // y ∉ lfOmega (R := R) A} =>
        oneSiteGaussian (EuclideanSpace ℝ (Fin N)) from rfl,
    ← integral_comp_restrict_pi
      (fun _ : BlockAt S n M K k => oneSiteGaussian (EuclideanSpace ℝ (Fin N)))
      (· ∉ lfOmega (R := R) A)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  have hrecTau : ∀ (c : PostComp A k) (Φg : GCfgAll S n M K k N),
      recTau rep C.hkK (recOfComp rep hA c)
          (lfGlue (lfOmega (R := R) A) (fun i => ψ i.1) 0) hv g Φg =
        recTau rep C.hkK (recOfComp rep hA c) ψ hv g Φg := by
    intro c Φg
    unfold recTau
    rw [recW_congr_psi rep C.hkK (recOfComp rep hA c) (ψ' := ψ) (fun y hy => ?_)]
    have hyΩ : y ∉ lfOmega (R := R) A := fun hyΩ =>
      (show ∀ c' : PostComp A k, y ∉ recBlk (M := M) (K := K) R c'.1.1 from hyΩ) c
        (Vblk_lfSrc_subset_recBlk rep C.hkK (recOfComp rep hA c) hy)
    exact lfGlue_of_not_mem _ _ hyΩ
  dsimp only
  change (psiDens N (fun i : {y : BlockAt S n M K k // y ∉ lfOmega (R := R) A} => ψ i.1) : ℂ) *
      gOp (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A C.hkK)
        (lfGlue (lfOmega (R := R) A) (fun i => ψ i.1) 0) hv g
        (lfRegInt C vc rep A (lfOmega (R := R) A) hv g (fun i => ψ i.1)) = _
  rw [gOp_postOp_eq_integral_recTau rep C.hkK hN hA, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φg => ?_)
  dsimp only
  rw [psiDens_compl_lfOmega A ψ, Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
  simp only [hrecTau]
  ring

end History

end Balaban.RootFSpine
