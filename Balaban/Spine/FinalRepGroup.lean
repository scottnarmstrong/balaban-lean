/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LastIntegral
import Mathlib.Tactic.Ring

/-!
# The last integral grouped by the large-field region of its histories

P7 (4.1) writes the last integral `∫ ρ_k dψ_k` of a member of the class as a sum over the
large-field regions `Z_k` of the histories of (D1); P7 (4.11) then completes the term with no
large-field region to the whole torus (it is `Ξ^sf`, the integral of the small-field factor on
the whole torus) and treats the remaining terms as a gas. This file proves the exact part of that
step from the form clause (D1) of the second version (`D1Form2`), with no new definition of an
operator.

* `lastRegion A k` is the region `Z_k(𝔸)` of a history as a finite set of `k`-cubes,
  `lastHistInt` the integral over `ψ_k` of the term of (D1) of one history (`postTerm2`),
  `lastRegionWeight Z` the sum of these over the histories of the representation with region `Z`.
* `integral_eq_sum_lastRegionWeight`: for a density with the form (D1), if the terms of the
  histories are integrable in `ψ_k`, `∫ ρ dψ_k = ∑_Z lastRegionWeight Z`.
* `postTerm2_of_region_empty`: the term of a history whose region is empty is the small-field
  factor on the whole torus, `sfFactor2 C vc univ` (no component, no boundary domain).
* `lastRegionWeight_empty`: hence the weight of the empty region is the number of histories with
  an empty region times `Ξ^sf` (`sfIntegral`); it is `Ξ^sf` exactly when the representation has
  one history with empty region (`lastRegionWeight_empty_of_card_eq_one`).

These weights group the histories by the region `Z_k` of the scale `k`, not by the region
`Z_{k+1}` of the operators `𝕋'_{k+1}(Z_{k+1}, 𝔸')` of P7 (4.9), which refines it by the
fluctuation integral of the last scale (P5 (3.18)); `notes/phase1/SPINE.md`, item 4 of the
sub-inputs of `LastIntegralInput`, records why `𝕋'_{k+1}` is not defined here. -/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  RegionHistory

namespace Balaban.RootFSpine

section Empty

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- No boundary domain meets the empty region. -/
theorem bdryDoms_empty_right {d m : ℕ} [NeZero m] (Om : Set (Torus d m)) :
    bdryDoms Om (∅ : Set (Torus d m)) = ∅ := by
  classical
  ext X
  simp [mem_bdryDoms, IsBdryDom]

omit [NeZero M] [NeZero S.L] in
/-- A history with empty region `Z_k(𝔸)` has no component of `Z_k(𝔸)`. -/
theorem isEmpty_postComp_of_region_empty (A : LabHist S n R k0 K) (k : ℕ)
    (hZ : (A.H.step k).Z = ∅) : IsEmpty (PostComp A k) := by
  refine ⟨fun c => ?_⟩
  have h := A.H.comp_mem_Z c.2
  rw [hZ] at h
  obtain ⟨x, hx, -⟩ := mem_comps_iff.mp h
  simp at hx

/-- The global operator of an empty family of components is the evaluation at the unique
configuration. -/
theorem gOp_of_isEmpty {ι : Type} [Fintype ι] (a : ι → LocalHistory S n M K) (k : ℕ)
    (P : ∀ i, OpPkg N R (a i) k) [IsEmpty ι]
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (F : GCfg a k P → ℂ) :
    gOp a k P ψk hv g F = F (fun i => isEmptyElim i) := by
  unfold gOp gMeasure
  rw [Measure.pi_of_empty, integral_dirac' _ _ StronglyMeasurable.of_subsingleton_dom]
  simp [gWeight]

/-- **The term of (D1) of a history with no large-field region** (P7 (4.1), the term `Z_k = ∅`):
there is no operator and no boundary term, so it is the small-field factor on the whole torus. -/
theorem postTerm2_of_region_empty {m₁ : ℕ} {ϱ : ℝ}
    (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (rep : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K)
    (hZ : (A.H.step k).Z = ∅)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    postTerm2 C vc rep A ψk hv g = sfFactor2 C vc Set.univ ψk hv g := by
  have := isEmpty_postComp_of_region_empty A k hZ
  unfold postTerm2
  rw [gOp_of_isEmpty]
  unfold integrand2
  simp only [Rep.bdrySum, hZ, bdryDoms_empty_right, Finset.sum_empty, Complex.exp_zero, one_mul,
    Set.compl_empty]

end Empty

section Group

open Classical

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- The region `Z_k(𝔸)` of a history as a finite set of `k`-cubes. -/
noncomputable def lastRegion (A : LabHist S n R k0 K) (k : ℕ) : Finset (Torus S.d (n k)) :=
  finOf (A.H.step k).Z

omit [NeZero M] [NeZero S.L] in
theorem lastRegion_eq_empty_iff (A : LabHist S n R k0 K) (k : ℕ) :
    lastRegion A k = ∅ ↔ (A.H.step k).Z = ∅ := by
  unfold lastRegion
  constructor
  · intro h
    have := coe_finOf (A.H.step k).Z
    rw [h] at this
    simpa using this.symm
  · intro h
    rw [h]
    ext x
    simp

variable {m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
  (rep : Rep S n R k0 K M N geo cs P k) (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)

/-- **The last integral of one history**: the integral over the fields `ψ_k` of the `k`-blocks of
the term of (D1) (`postTerm2`), at the physical field `hv` and the source `g`. -/
noncomputable def lastHistInt (A : LabHist S n R k0 K) : ℂ :=
  ∫ ψk, postTerm2 C vc rep A ψk hv g

/-- **The weight of a large-field region**: the sum of the last integrals of the histories of the
representation whose region `Z_k(𝔸)` is `Z`. -/
noncomputable def lastRegionWeight (Z : Finset (Torus S.d (n k))) : ℂ :=
  ∑ A ∈ rep.hist.filter (fun A => lastRegion A k = Z), lastHistInt C vc rep hv g A

/-- **The last integral is the sum of the weights of the regions** (P7 (4.1)): exact, from (D1),
when the terms of the histories are integrable in `ψ_k`. -/
theorem integral_eq_sum_lastRegionWeight
    {ρ : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → (GIdx S n M K N → ℂ) → ℂ}
    (hD : D1Form2 C vc rep hv ρ) (hg : g ∈ l1Ball (GIdx S n M K N))
    (hint : ∀ A ∈ rep.hist, Integrable (fun ψk => postTerm2 C vc rep A ψk hv g)) :
    ∫ ψk, ρ ψk g = ∑ Z : Finset (Torus S.d (n k)), lastRegionWeight C vc rep hv g Z := by
  have h1 : ∀ ψk, ρ ψk g = ∑ A ∈ rep.hist, postTerm2 C vc rep A ψk hv g :=
    fun ψk => (hD ψk g hg).2
  simp_rw [h1]
  rw [integral_finsetSum _ hint]
  unfold lastRegionWeight lastHistInt
  exact (Finset.sum_fiberwise rep.hist (fun A => lastRegion A k) _).symm

/-- The last integral of a history with empty region is the integral of the small-field factor
on the whole torus. -/
theorem lastHistInt_of_region_empty (A : LabHist S n R k0 K) (hA : lastRegion A k = ∅) :
    lastHistInt C vc rep hv g A = ∫ ψk, sfFactor2 C vc Set.univ ψk hv g := by
  unfold lastHistInt
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψk => ?_)
  exact postTerm2_of_region_empty C vc rep A ((lastRegion_eq_empty_iff A k).1 hA) ψk hv g

/-- **The weight of the empty region** (P7 (4.11), the term `1`): the number of histories of the
representation with empty region, times the integral of the small-field factor on the whole
torus. -/
theorem lastRegionWeight_empty :
    lastRegionWeight C vc rep hv g ∅ =
      (rep.hist.filter (fun A => lastRegion A k = ∅)).card •
        ∫ ψk, sfFactor2 C vc Set.univ ψk hv g := by
  unfold lastRegionWeight
  rw [Finset.sum_congr rfl (fun A hA =>
    lastHistInt_of_region_empty C vc rep hv g A (Finset.mem_filter.1 hA).2), Finset.sum_const]

/-- If the representation has exactly one history with empty region, the weight of the empty
region is the integral of the small-field factor on the whole torus. -/
theorem lastRegionWeight_empty_of_card_eq_one
    (h1 : (rep.hist.filter (fun A => lastRegion A k = ∅)).card = 1) :
    lastRegionWeight C vc rep hv g ∅ = ∫ ψk, sfFactor2 C vc Set.univ ψk hv g := by
  rw [lastRegionWeight_empty, h1, one_smul]

end Group

section Sf

open Classical

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Balaban.SmallField.Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **The weight of the empty region at the stopping scale is `Ξ^sf`** when the representation has
exactly one history with empty region: the form of `Ξ^sf = sfIntegral` in P7 (4.11). -/
theorem lastRegionWeight_empty_eq_sfIntegral
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ) (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK]
    (g : GIdx S (sides S.L K nK) M K N → ℂ)
    (h1 : ((F.lf nK).hist.filter (fun A => lastRegion A k = ∅)).card = 1) :
    lastRegionWeight (F.ctx hM6 hkK nK) vc (F.lf nK) hv g ∅ = sfIntegral F hM6 hkK vc hv nK g :=
  lastRegionWeight_empty_of_card_eq_one _ _ _ _ _ h1

end Sf

end Balaban.RootFSpine
