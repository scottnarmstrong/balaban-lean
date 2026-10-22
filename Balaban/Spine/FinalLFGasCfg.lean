/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFDensity
public import Balaban.Spine.FinalLFDouble

/-!
# The configuration space of the record gas (A6-4)

The record gas (B2's operator gas core, `Polymer/GasOpEq.lean`, `Polymer/HoleOperator.lean`)
integrates against a product of probability measures over the sites of a geometry. Its variables
are the internal variables of scales `< k` of the histories (`GVar`) and the field `ψ_k` on the
`k`-blocks (`PVar = GVar ⊕ BlockAt k`), each with its probability reference measure (`pProb`): the
normalized sphere measure or the standard Gaussian for the internal variables (`varProb`), the
standard Gaussian for `ψ_k`, whose Lebesgue measure is the density `(2π)^{N/2} e^{‖x‖²/2}` times the
Gaussian (`volume_pi_eq_withDensity`, `integral_volume_pi`).

The sites of the gas are the points of the doubled torus `𝕋_{2n_k}` (`Spine/FinalLFDouble.lean`:
separation of records is disjointness of the `(ω - 1)`-neighbourhoods of their doubled cubes). A
variable sits at the doubled image of its cube (`pCell`): an internal variable at the cube of a
site of its block, `ψ_k(y)` at the cube of the block `y`. The configuration of the gas at a site is
the configuration of the variables sitting there (`CellCfg`, with the product measure `cellProb`),
and the configurations of all the sites are the configurations of all the variables (`regroup`,
measure preserving: `measurePreserving_regroup`). A function of the variables sitting at a set `T`
of sites (`PDepOn`) depends, as a function of the gas configuration, only on the sites of `T`
(`depOn_comp_regroup`, B2's `DepOn`).

* `gaussPi`, `psiDens`, **`volume_pi_eq_withDensity`**, `integral_volume_pi`,
  `integrable_volume_pi_iff`;
* `PVar`, `pIsSpin`, `PCfg`, `pProb`, `gPart`, `psiPart`, `measurePreserving_pSplit`,
  `integral_pProb_eq_of_integrable`;
* `gSite`, `pCell`, `CellCfg`, `cellProb`, `regroup`, **`measurePreserving_regroup`**,
  `regroup_apply`, `integral_comp_regroup`, `integrable_comp_regroup_iff`, `PDepOn`,
  **`depOn_comp_regroup`**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory
open scoped ENNReal NNReal

namespace Balaban.RootFSpine

/-! ### Lebesgue measure on fields as densities times Gaussians -/

section Gauss

variable (N : ℕ)

/-- The product of standard Gaussians on the fields `ι → ℝ^N`. -/
noncomputable def gaussPi (ι : Type*) [Fintype ι] : Measure (ι → EuclideanSpace ℝ (Fin N)) :=
  Measure.pi fun _ => oneSiteGaussian (EuclideanSpace ℝ (Fin N))

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (gaussPi N ι) := by
  unfold gaussPi; infer_instance

/-- The density of Lebesgue measure on the fields `ι → ℝ^N` against `gaussPi`:
`∏_i (2π)^{N/2} e^{‖ψ_i‖²/2}`. -/
noncomputable def psiDens {ι : Type*} [Fintype ι] (ψ : ι → EuclideanSpace ℝ (Fin N)) : ℝ :=
  ∏ i, gaussInvDens N (ψ i)

theorem psiDens_nonneg {ι : Type*} [Fintype ι] (ψ : ι → EuclideanSpace ℝ (Fin N)) :
    0 ≤ psiDens N ψ :=
  Finset.prod_nonneg fun _ _ => (gaussInvDens_pos N _).le

theorem measurable_psiDens (ι : Type*) [Fintype ι] :
    Measurable (psiDens N (ι := ι)) :=
  Finset.measurable_prod _ fun i _ => (measurable_gaussInvDens N).comp (measurable_pi_apply i)

/-- **Lebesgue measure on the fields is the density `psiDens` times the product of standard
Gaussians.** -/
theorem volume_pi_eq_withDensity (ι : Type*) [Fintype ι] :
    (volume : Measure (ι → EuclideanSpace ℝ (Fin N))) =
      (gaussPi N ι).withDensity fun ψ => ENNReal.ofReal (psiDens N ψ) := by
  have h : (fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N)))) =
      fun _ : ι => (oneSiteGaussian (EuclideanSpace ℝ (Fin N))).withDensity
        fun x => ENNReal.ofReal (gaussInvDens N x) :=
    funext fun _ => volume_eq_withDensity_gauss N
  rw [volume_pi, h]
  refine (pi_withDensity_eq (fun _ : ι => oneSiteGaussian (EuclideanSpace ℝ (Fin N)))
    (fun _ : ι => gaussInvDens N) (fun _ => measurable_gaussInvDens N)).trans ?_
  congr 1
  funext ψ
  unfold psiDens
  exact (ENNReal.ofReal_prod_of_nonneg fun _ _ => (gaussInvDens_pos N _).le).symm

/-- **The Lebesgue integral over the fields is the Gaussian expectation of the density times the
integrand.** -/
theorem integral_volume_pi (ι : Type*) [Fintype ι] (F : (ι → EuclideanSpace ℝ (Fin N)) → ℂ) :
    ∫ ψ, F ψ = ∫ ψ, (psiDens N ψ : ℂ) * F ψ ∂(gaussPi N ι) := by
  rw [volume_pi_eq_withDensity N ι]
  exact integral_withDensity_ofReal _ (measurable_psiDens N ι) (psiDens_nonneg N) F

/-- Lebesgue integrability over the fields is the Gaussian integrability of the density times the
integrand. -/
theorem integrable_volume_pi_iff (ι : Type*) [Fintype ι]
    (F : (ι → EuclideanSpace ℝ (Fin N)) → ℂ) :
    Integrable F ↔ Integrable (fun ψ => (psiDens N ψ : ℂ) * F ψ) (gaussPi N ι) := by
  rw [volume_pi_eq_withDensity N ι]
  exact integrable_withDensity_ofReal_iff _ (measurable_psiDens N ι) (psiDens_nonneg N) F

end Gauss

/-! ### The variables of the record gas -/

section Vars

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ}

/-- **The variables of the record gas**: the internal variables of scales `< k` and the field
`ψ_k` on the `k`-blocks. -/
abbrev PVar (S : Setting) (n : ℕ → ℕ) (M K k : ℕ) : Type :=
  GVar S n M K k ⊕ BlockAt S n M K k

/-- Is the variable a spin? (`ψ_k` is not.) -/
def pIsSpin : PVar S n M K k → Bool := Sum.elim gIsSpin fun _ => false

/-- The configurations of the variables of the record gas. -/
abbrev PCfg (S : Setting) (n : ℕ → ℕ) (M K k N : ℕ) : Type :=
  (q : PVar S n M K k) → VarVal N (pIsSpin q)

/-- The product of the probability reference measures of the variables of the record gas. -/
noncomputable def pProb (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K k N : ℕ) [NeZero M]
    [NeZero S.L] : Measure (PCfg S n M K k N) :=
  Measure.pi fun q => varProb N (pIsSpin q)

instance : IsFiniteMeasure (pProb S n M K k N) := by
  unfold pProb; infer_instance

/-- The internal variables of a configuration of the record gas. -/
def gPart (Φ : PCfg S n M K k N) : GCfgAll S n M K k N := fun q => Φ (Sum.inl q)

/-- The field `ψ_k` of a configuration of the record gas. -/
def psiPart (Φ : PCfg S n M K k N) : BlockAt S n M K k → EuclideanSpace ℝ (Fin N) :=
  fun y => Φ (Sum.inr y)

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem measurable_gPart :
    Measurable (gPart (S := S) (n := n) (M := M) (K := K) (k := k) (N := N)) :=
  Measurable.of_eval fun q => measurable_pi_apply (Sum.inl q)

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem measurable_psiPart :
    Measurable (psiPart (S := S) (n := n) (M := M) (K := K) (k := k) (N := N)) :=
  Measurable.of_eval fun y => measurable_pi_apply (Sum.inr y)

/-- **The configurations of the record gas are the pairs (internal variables, `ψ_k`)**, with the
product of `gProbAll` and `gaussPi`. -/
theorem measurePreserving_pSplit :
    MeasurePreserving (fun Φ : PCfg S n M K k N => (gPart Φ, psiPart Φ)) (pProb S n M K k N)
      ((gProbAll S n M K k N).prod (gaussPi N (BlockAt S n M K k))) :=
  measurePreserving_sumPiEquivProdPi (fun q : PVar S n M K k => varProb N (pIsSpin q))

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The splitting of a configuration of the gas into internal variables and `ψ_k` is a measurable
embedding. -/
theorem measurableEmbedding_pSplit :
    MeasurableEmbedding (fun Φ : PCfg S n M K k N => (gPart Φ, psiPart Φ)) :=
  (MeasurableEquiv.sumPiEquivProdPi
    (fun q : PVar S n M K k => VarVal N (pIsSpin q))).measurableEmbedding

/-- **Fubini on the configurations of the record gas**: the expectation of an integrable function of
the internal variables and of `ψ_k` is the Gaussian expectation in `ψ_k` of its expectation in the
internal variables. -/
theorem integral_pProb_eq_of_integrable
    (F : GCfgAll S n M K k N → (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℂ)
    (hF : Integrable (fun Φ : PCfg S n M K k N => F (gPart Φ) (psiPart Φ)) (pProb S n M K k N)) :
    ∫ Φ, F (gPart Φ) (psiPart Φ) ∂(pProb S n M K k N) =
      ∫ ψ, ∫ Φg, F Φg ψ ∂(gProbAll S n M K k N) ∂(gaussPi N (BlockAt S n M K k)) := by
  have h := measurePreserving_pSplit (S := S) (n := n) (M := M) (K := K) (k := k) (N := N)
  have hF' : Integrable (fun p => F p.1 p.2)
      ((gProbAll S n M K k N).prod (gaussPi N (BlockAt S n M K k))) :=
    (h.integrable_comp_emb measurableEmbedding_pSplit).1 hF
  exact (h.integral_comp measurableEmbedding_pSplit (fun p => F p.1 p.2)).trans
    (integral_prod_symm (fun p => F p.1 p.2) hF')

end Vars

/-! ### The sites of the record gas -/

section Cells

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ}

/-- A site of the block of an internal variable. -/
noncomputable def gSite (hkK : k ≤ K) (q : GVar S n M K k) : Torus S.d (M * n K * S.L ^ K) :=
  (exists_site_in_block (S := S) (n := n) (M := M) (K := K) (j := q.1)
    (by have := q.1.2; omega) q.2.2).choose

theorem jBlock_gSite (hkK : k ≤ K) (q : GVar S n M K k) :
    Multiscale.jBlock S.d S.L (M * n K) K q.1 (gSite hkK q) = q.2.2 :=
  (exists_site_in_block (S := S) (n := n) (M := M) (K := K) (j := q.1)
    (by have := q.1.2; omega) q.2.2).choose_spec

/-- **The site of the record gas of a variable**: the doubled image of its cube of `𝕋_k` (for an
internal variable, the cube of a site of its block; for `ψ_k(y)`, the cube of the block `y`). -/
noncomputable def pCell (hkK : k ≤ K) : PVar S n M K k → Torus S.d (2 * n k) :=
  Sum.elim (fun q => tDouble (cubeMap n S.L M K k (gSite hkK q)))
    fun y => tDouble (blockCube S n M K k y)

/-- The configurations of the variables sitting at a site of the record gas. -/
abbrev CellCfg (hkK : k ≤ K) (N : ℕ) (b : Torus S.d (2 * n k)) : Type :=
  (q : {q : PVar S n M K k // pCell hkK q = b}) → VarVal N (pIsSpin q.1)

/-- The product of the probability reference measures of the variables sitting at a site. -/
noncomputable def cellProb (hkK : k ≤ K) (N : ℕ) (b : Torus S.d (2 * n k)) :
    Measure (CellCfg (S := S) (M := M) hkK N b) :=
  Measure.pi fun q => varProb N (pIsSpin q.1)

instance (hkK : k ≤ K) (b : Torus S.d (2 * n k)) :
    IsFiniteMeasure (cellProb (S := S) (M := M) hkK N b) := by
  unfold cellProb; infer_instance

/-- For `1 ≤ N`, the measure of a site is a probability measure. -/
theorem isProbabilityMeasure_cellProb (hN : 1 ≤ N) (hkK : k ≤ K) (b : Torus S.d (2 * n k)) :
    IsProbabilityMeasure (cellProb (S := S) (M := M) hkK N b) := by
  have := isProbabilityMeasure_varProb hN
  unfold cellProb; infer_instance

/-- **The configurations of all the sites are the configurations of all the variables.** -/
noncomputable def regroup (hkK : k ≤ K) (N : ℕ) :
    ((b : Torus S.d (2 * n k)) → CellCfg (S := S) (M := M) hkK N b) ≃ᵐ PCfg S n M K k N :=
  (MeasurableEquiv.piCurry fun (b : Torus S.d (2 * n k))
      (q : {q : PVar S n M K k // pCell hkK q = b}) => VarVal N (pIsSpin q.1)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun q : PVar S n M K k => VarVal N (pIsSpin q))
      (Equiv.sigmaFiberEquiv (pCell hkK)))

theorem regroup_apply (hkK : k ≤ K)
    (Φc : (b : Torus S.d (2 * n k)) → CellCfg (S := S) (M := M) hkK N b) (q : PVar S n M K k) :
    regroup hkK N Φc q = Φc (pCell hkK q) ⟨q, rfl⟩ := by
  rfl

/-- **The regrouping carries the product of the measures of the sites to the product of the
measures of the variables.** -/
theorem measurePreserving_regroup (hkK : k ≤ K) :
    MeasurePreserving (regroup (S := S) (M := M) hkK N)
      (Measure.pi fun b => cellProb (S := S) (M := M) hkK N b) (pProb S n M K k N) := by
  have h1 := (PiTools.measurePreserving_piCurry
    (fun (b : Torus S.d (2 * n k)) (q : {q : PVar S n M K k // pCell hkK q = b}) =>
      VarVal N (pIsSpin q.1))
    (fun b q => varProb N (pIsSpin q.1))).symm
  have h2 := measurePreserving_piCongrLeft (fun q : PVar S n M K k => varProb N (pIsSpin q))
    (Equiv.sigmaFiberEquiv (pCell hkK))
  exact h2.comp h1

/-- **Integrals over the configurations of the sites are integrals over the configurations of the
variables.** -/
theorem integral_comp_regroup (hkK : k ≤ K) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : PCfg S n M K k N → E) :
    ∫ Φc, F (regroup (S := S) (M := M) hkK N Φc) ∂(Measure.pi fun b =>
      cellProb (S := S) (M := M) hkK N b) = ∫ Φ, F Φ ∂(pProb S n M K k N) :=
  (measurePreserving_regroup hkK).integral_comp' F

/-- Integrability over the configurations of the sites is integrability over the configurations of
the variables. -/
theorem integrable_comp_regroup_iff (hkK : k ≤ K) {E : Type*} [NormedAddCommGroup E]
    (F : PCfg S n M K k N → E) :
    Integrable (fun Φc => F (regroup (S := S) (M := M) hkK N Φc)) (Measure.pi fun b =>
      cellProb (S := S) (M := M) hkK N b) ↔ Integrable F (pProb S n M K k N) :=
  (measurePreserving_regroup hkK).integrable_comp_emb (regroup hkK N).measurableEmbedding

/-- A function of the configurations of the variables depends only on the variables sitting at the
sites of `T`. -/
def PDepOn (hkK : k ≤ K) (T : Finset (Torus S.d (2 * n k))) (F : PCfg S n M K k N → ℂ) : Prop :=
  ∀ Φ Φ' : PCfg S n M K k N, (∀ q, pCell hkK q ∈ T → Φ q = Φ' q) → F Φ = F Φ'

/-- **A function of the variables sitting at the sites of `T` depends, as a function of the
configuration of the sites, only on the sites of `T`.** -/
theorem depOn_comp_regroup (hkK : k ≤ K) {T : Finset (Torus S.d (2 * n k))}
    {F : PCfg S n M K k N → ℂ} (hF : PDepOn hkK T F) :
    Polymer.DepOn T (fun Φc => F (regroup (S := S) (M := M) hkK N Φc)) := by
  intro Φc Φc' h
  refine hF _ _ fun q hq => ?_
  rw [regroup_apply, regroup_apply, h _ hq]

end Cells

end Balaban.RootFSpine
