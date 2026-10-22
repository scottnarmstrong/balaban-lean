/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFProduct
public import Balaban.LargeField.Base.KF0CutoffSplit
public import Balaban.LargeField.Base.PiLintegral
public import Balaban.Polymer.Mayer

/-!
# The reference measures as densities times probability measures (A6-4)

The polymer gas of the records (B2's operator gas core, `Polymer/GasOpEq.lean`) integrates against a
product of probability measures. The reference measure of one internal variable (`varMeasure`: the
surface measure of the unit sphere for a spin, Lebesgue measure on `ℝ^N` otherwise) is a density
times a probability measure (`varMeasure_eq_withDensity`): the normalized surface measure with the
constant density `|S^{N-1}|`, and the standard Gaussian with the density
`(2π)^{N/2} e^{‖x‖²/2}`. The spin case needs `1 ≤ N` (for `N = 0` the sphere is empty).

The density of a configuration of a set of global variables is the product of the densities of its
variables (`gDens`, `gcfgMeasure_eq_withDensity`), and it factors over a disjoint union
(`gDens_iUnion`). On the configurations of all the global variables (`GCfgAll`, with the product
`gProbAll` of the probability measures), integrating a function of the variables of `U` is
integrating it against the product on `U` (`integral_restrictAll`, `integrable_restrictAll_iff`).

So the operator of a history of the large-field half is the expectation, for `gProbAll`, of the
product over its components of the weights of their records with their densities (`recTau`), each a
function of the variables of its record (`depOn_recTau`): `gOp_postOp_eq_integral_recTau`.

* `varProb`, `varDens`, **`varMeasure_eq_withDensity`**, `isProbabilityMeasure_varProb`;
* `gcfgProb`, `gDens`, **`gcfgMeasure_eq_withDensity`**, `integral_gcfgMeasure`,
  `integrable_gcfgMeasure_iff`, `prod_iUnion_eq`, `gDens_iUnion`;
* `GCfgAll`, `gProbAll`, `restrictAll`, **`integral_restrictAll`**, `integrable_restrictAll_iff`;
* `recTau`, `depOn_recTau`, **`gOp_postOp_eq_integral_recTau`**.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory
open scoped ENNReal NNReal

namespace Balaban.RootFSpine

/-! ### One variable -/

section One

variable (N : ℕ)

/-- The total surface measure `|S^{N-1}|` of the unit sphere of `ℝ^N`. -/
noncomputable def sphereMass : ℝ≥0∞ :=
  (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ

theorem sphereMass_ne_top : sphereMass N ≠ ∞ := measure_ne_top _ _

variable {N} in
theorem sphereMass_ne_zero (hN : 1 ≤ N) : sphereMass N ≠ 0 := by
  intro h
  unfold sphereMass at h
  rw [Measure.measure_univ_eq_zero, Measure.toSphere_eq_zero_iff_finrank,
    finrank_euclideanSpace_fin] at h
  omega

/-- **The probability reference measure of one variable**: the normalized surface measure of the
unit sphere for a spin, the standard Gaussian on `ℝ^N` otherwise. -/
noncomputable def varProb : (b : Bool) → Measure (VarVal N b)
  | true => (sphereMass N)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere
  | false => oneSiteGaussian (EuclideanSpace ℝ (Fin N))

/-- **The density of the reference measure of one variable against its probability measure**:
`|S^{N-1}|` for a spin, `(2π)^{N/2} e^{‖x‖²/2}` on `ℝ^N`. -/
noncomputable def varDens : (b : Bool) → VarVal N b → ℝ
  | true => fun _ => (sphereMass N).toReal
  | false => fun x => (2 * Real.pi) ^ ((N : ℝ) / 2) *
      Real.exp ((1 / 2) * ‖(show EuclideanSpace ℝ (Fin N) from x)‖ ^ 2)

instance (b : Bool) : IsFiniteMeasure (varProb N b) := by
  cases b with
  | true =>
    refine ⟨?_⟩
    change (sphereMass N)⁻¹ * (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ < ∞
    change (sphereMass N)⁻¹ * sphereMass N < ∞
    by_cases h0 : sphereMass N = 0
    · rw [h0, mul_zero]; exact ENNReal.zero_lt_top
    · rw [ENNReal.inv_mul_cancel h0 (sphereMass_ne_top N)]; exact ENNReal.one_lt_top
  | false =>
    change IsFiniteMeasure (oneSiteGaussian (EuclideanSpace ℝ (Fin N)))
    infer_instance

variable {N} in
/-- For `1 ≤ N`, the reference probability measure of a variable is a probability measure. -/
theorem isProbabilityMeasure_varProb (hN : 1 ≤ N) (b : Bool) :
    IsProbabilityMeasure (varProb N b) := by
  cases b with
  | true =>
    refine ⟨?_⟩
    change (sphereMass N)⁻¹ * (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ = 1
    change (sphereMass N)⁻¹ * sphereMass N = 1
    exact ENNReal.inv_mul_cancel (sphereMass_ne_zero hN) (sphereMass_ne_top N)
  | false =>
    change IsProbabilityMeasure (oneSiteGaussian (EuclideanSpace ℝ (Fin N)))
    infer_instance

theorem varDens_nonneg (b : Bool) (v : VarVal N b) : 0 ≤ varDens N b v := by
  cases b with
  | true => exact ENNReal.toReal_nonneg
  | false => change 0 ≤ (2 * Real.pi) ^ ((N : ℝ) / 2) * Real.exp _; positivity

variable {N} in
theorem varDens_pos (hN : 1 ≤ N) (b : Bool) (v : VarVal N b) : 0 < varDens N b v := by
  cases b with
  | true => exact ENNReal.toReal_pos (sphereMass_ne_zero hN) (sphereMass_ne_top N)
  | false => change 0 < (2 * Real.pi) ^ ((N : ℝ) / 2) * Real.exp _; positivity

theorem measurable_varDens (b : Bool) : Measurable (varDens N b) := by
  cases b with
  | true => exact measurable_const
  | false =>
    change Measurable fun x : EuclideanSpace ℝ (Fin N) =>
      (2 * Real.pi) ^ ((N : ℝ) / 2) * Real.exp ((1 / 2) * ‖x‖ ^ 2)
    fun_prop

variable {N} in
/-- **The reference measure of a variable is its density times its probability measure.** -/
theorem varMeasure_eq_withDensity (hN : 1 ≤ N) (b : Bool) :
    varMeasure N b = (varProb N b).withDensity fun v => ENNReal.ofReal (varDens N b v) := by
  cases b with
  | true =>
    change (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere =
      ((sphereMass N)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere).withDensity
        fun _ => ENNReal.ofReal (sphereMass N).toReal
    rw [withDensity_const, ENNReal.ofReal_toReal (sphereMass_ne_top N), smul_smul,
      ENNReal.mul_inv_cancel (sphereMass_ne_zero hN) (sphereMass_ne_top N), one_smul]
  | false =>
    change (volume : Measure (EuclideanSpace ℝ (Fin N))) =
      (oneSiteGaussian (EuclideanSpace ℝ (Fin N))).withDensity fun x =>
        ENNReal.ofReal ((2 * Real.pi) ^ ((N : ℝ) / 2) * Real.exp ((1 / 2) * ‖x‖ ^ 2))
    unfold oneSiteGaussian
    rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
    conv_lhs => rw [← withDensity_one (μ := (volume : Measure (EuclideanSpace ℝ (Fin N))))]
    congr 1
    funext x
    rw [Pi.mul_apply, Pi.one_apply, ← ENNReal.ofReal_mul (by positivity), finrank_euclideanSpace_fin]
    rw [show (2 * Real.pi) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / 2) * ‖x‖ ^ 2) *
        ((2 * Real.pi) ^ ((N : ℝ) / 2) * Real.exp ((1 / 2) * ‖x‖ ^ 2)) =
        ((2 * Real.pi) ^ (-(N : ℝ) / 2) * (2 * Real.pi) ^ ((N : ℝ) / 2)) *
          (Real.exp (-(1 / 2) * ‖x‖ ^ 2) * Real.exp ((1 / 2) * ‖x‖ ^ 2)) by ring,
      ← Real.rpow_add (by positivity), ← Real.exp_add]
    rw [show -(N : ℝ) / 2 + (N : ℝ) / 2 = 0 by ring,
      show -(1 / 2) * ‖x‖ ^ 2 + (1 / 2) * ‖x‖ ^ 2 = 0 by ring]
    simp

end One

/-! ### Configurations of a set of global variables -/

section Cfg

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ}

/-- The product of the probability reference measures on the configurations of a set of global
variables. -/
noncomputable def gcfgProb (N : ℕ) (U : Set (GVar S n M K k)) : Measure (GCfgOn N U) :=
  Measure.pi fun q => varProb N (gIsSpin q.1)

instance (U : Set (GVar S n M K k)) : IsFiniteMeasure (gcfgProb N U) := by
  unfold gcfgProb; infer_instance

/-- For `1 ≤ N`, the product of the probability reference measures is a probability measure. -/
theorem isProbabilityMeasure_gcfgProb (hN : 1 ≤ N) (U : Set (GVar S n M K k)) :
    IsProbabilityMeasure (gcfgProb N U) := by
  have := isProbabilityMeasure_varProb hN
  unfold gcfgProb; infer_instance

/-- The density of a configuration of a set of global variables: the product of the densities of
its variables. -/
noncomputable def gDens (N : ℕ) (U : Set (GVar S n M K k)) (z : GCfgOn N U) : ℝ :=
  ∏ q, varDens N (gIsSpin q.1) (z q)

theorem gDens_nonneg (U : Set (GVar S n M K k)) (z : GCfgOn N U) : 0 ≤ gDens N U z :=
  Finset.prod_nonneg fun _ _ => varDens_nonneg N _ _

theorem measurable_gDens (U : Set (GVar S n M K k)) : Measurable (gDens N U) :=
  Finset.measurable_prod _ fun q _ => (measurable_varDens N _).comp (measurable_pi_apply q)

/-- **The reference measure of a set of global variables is its density times the product of the
probability measures.** -/
theorem gcfgMeasure_eq_withDensity (hN : 1 ≤ N) (U : Set (GVar S n M K k)) :
    gcfgMeasure N U = (gcfgProb N U).withDensity fun z => ENNReal.ofReal (gDens N U z) := by
  have h : (fun q : ↥U => varMeasure N (gIsSpin q.1)) =
      fun q : ↥U => (varProb N (gIsSpin q.1)).withDensity
        fun v => ENNReal.ofReal (varDens N (gIsSpin q.1) v) :=
    funext fun q => varMeasure_eq_withDensity hN _
  unfold gcfgMeasure gcfgProb
  rw [h]
  refine (pi_withDensity_eq (fun q : ↥U => varProb N (gIsSpin q.1))
    (fun q : ↥U => varDens N (gIsSpin q.1)) (fun q => measurable_varDens N _)).trans ?_
  congr 1
  funext z
  unfold gDens
  rw [ENNReal.ofReal_prod_of_nonneg fun q _ => varDens_nonneg N _ _]

/-- **The integral against the reference measure is the expectation of the density times the
integrand.** -/
theorem integral_gcfgMeasure (hN : 1 ≤ N) (U : Set (GVar S n M K k)) (F : GCfgOn N U → ℂ) :
    ∫ z, F z ∂(gcfgMeasure N U) = ∫ z, (gDens N U z : ℂ) * F z ∂(gcfgProb N U) := by
  rw [gcfgMeasure_eq_withDensity hN]
  have hf : Measurable fun z => (gDens N U z).toNNReal :=
    (measurable_gDens U).real_toNNReal
  change ∫ z, F z ∂((gcfgProb N U).withDensity fun z => ((gDens N U z).toNNReal : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  change ((gDens N U z).toNNReal : ℝ) • F z = _
  rw [Real.coe_toNNReal _ (gDens_nonneg U z), Complex.real_smul]

/-- Integrability against the reference measure is integrability of the density times the
integrand against the product of the probability measures. -/
theorem integrable_gcfgMeasure_iff (hN : 1 ≤ N) (U : Set (GVar S n M K k)) (F : GCfgOn N U → ℂ) :
    Integrable F (gcfgMeasure N U) ↔
      Integrable (fun z => (gDens N U z : ℂ) * F z) (gcfgProb N U) := by
  rw [gcfgMeasure_eq_withDensity hN]
  have hf : Measurable fun z => (gDens N U z).toNNReal :=
    (measurable_gDens U).real_toNNReal
  change Integrable F ((gcfgProb N U).withDensity fun z => ((gDens N U z).toNNReal : ℝ≥0∞)) ↔ _
  rw [integrable_withDensity_iff_integrable_smul hf]
  refine integrable_congr (Filter.Eventually.of_forall fun z => ?_)
  change ((gDens N U z).toNNReal : ℝ) • F z = _
  rw [Real.coe_toNNReal _ (gDens_nonneg U z), Complex.real_smul]

/-- A product over a disjoint union of sets of global variables is the product of the products over
the sets. -/
theorem prod_iUnion_eq {ι : Type*} [Fintype ι] {β : Type*} [CommMonoid β]
    {U : ι → Set (GVar S n M K k)} (hdisj : Pairwise (Function.onFun Disjoint U))
    (g : ↥(⋃ i, U i) → β) :
    ∏ q, g q = ∏ i, ∏ q : ↥(U i), g ⟨q.1, Set.subset_iUnion U i q.2⟩ := by
  calc ∏ q, g q = ∏ x : (Σ i, ↥(U i)), g ⟨x.2.1, Set.subset_iUnion U x.1 x.2.2⟩ :=
        Fintype.prod_equiv (Set.unionEqSigmaOfDisjoint hdisj) _ _ fun x =>
          congrArg g (Subtype.ext (Set.coe_snd_unionEqSigmaOfDisjoint hdisj x).symm)
    _ = _ := Fintype.prod_sigma _

/-- **The density of a configuration of a disjoint union is the product of the densities of its
restrictions.** -/
theorem gDens_iUnion {ι : Type*} [Fintype ι] {U : ι → Set (GVar S n M K k)}
    (hdisj : Pairwise (Function.onFun Disjoint U)) (z : GCfgOn N (⋃ i, U i)) :
    gDens N (⋃ i, U i) z = ∏ i, gDens N (U i) (restrictOn (Set.subset_iUnion U i) z) :=
  prod_iUnion_eq hdisj fun q => varDens N (gIsSpin q.1) (z q)

end Cfg

/-! ### Configurations of all the global variables -/

section All

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {N k : ℕ}

noncomputable instance : Fintype (GVar S n M K k) := by
  haveI : Finite (GVar S n M K k) := by unfold GVar; infer_instance
  exact Fintype.ofFinite _

/-- The configurations of all the global variables of scale `< k`. -/
abbrev GCfgAll (S : Setting) (n : ℕ → ℕ) (M K k N : ℕ) : Type :=
  (q : GVar S n M K k) → VarVal N (gIsSpin q)

/-- The product of the probability reference measures on the configurations of all the global
variables. -/
noncomputable def gProbAll (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (M K k N : ℕ) [NeZero M]
    [NeZero S.L] : Measure (GCfgAll S n M K k N) :=
  Measure.pi fun q => varProb N (gIsSpin q)

/-- The restriction of a configuration of all the global variables to a set of them. -/
def restrictAll (U : Set (GVar S n M K k)) (Φ : GCfgAll S n M K k N) : GCfgOn N U :=
  fun q => Φ q.1

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem measurable_restrictAll (U : Set (GVar S n M K k)) :
    Measurable (restrictAll (N := N) U) :=
  Measurable.of_eval fun q => measurable_pi_apply q.1

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem restrictOn_restrictAll {U W : Set (GVar S n M K k)} (h : U ⊆ W)
    (Φ : GCfgAll S n M K k N) : restrictOn h (restrictAll W Φ) = restrictAll U Φ := rfl

/-- The restriction to `U`, followed by the restriction to the complement, is measure preserving
onto the product of the probability measures on `U` and on its complement. -/
theorem measurePreserving_piEquivPiSubtypeProd_gProbAll (U : Set (GVar S n M K k))
    [DecidablePred (· ∈ U)] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun q : GVar S n M K k => VarVal N (gIsSpin q))
        (· ∈ U))
      (gProbAll S n M K k N)
      ((gcfgProb N U).prod (Measure.pi fun q : {q // q ∉ U} => varProb N (gIsSpin q.1))) := by
  have h := measurePreserving_piEquivPiSubtypeProd
    (fun q : GVar S n M K k => varProb N (gIsSpin q)) (· ∈ U)
  unfold gcfgProb gProbAll
  convert h using 3

/-- **The expectation of a function of the variables of `U`** for the product of the probability
measures on all the global variables is its expectation on `U`. -/
theorem integral_restrictAll (hN : 1 ≤ N) (U : Set (GVar S n M K k)) (G : GCfgOn N U → ℂ) :
    ∫ Φ, G (restrictAll U Φ) ∂(gProbAll S n M K k N) = ∫ z, G z ∂(gcfgProb N U) := by
  classical
  have := isProbabilityMeasure_varProb hN
  have h := measurePreserving_piEquivPiSubtypeProd_gProbAll (N := N) U
  have e : (fun Φ => G (restrictAll U Φ)) = (fun p => G p.1) ∘
      MeasurableEquiv.piEquivPiSubtypeProd (fun q : GVar S n M K k => VarVal N (gIsSpin q))
        (· ∈ U) := rfl
  rw [e, Function.comp_def, h.integral_comp' (fun p => G p.1), integral_fun_fst, probReal_univ,
    one_smul]

/-- Integrability of a function of the variables of `U` for the product of the probability measures
on all the global variables is its integrability on `U`. -/
theorem integrable_restrictAll_iff (hN : 1 ≤ N) (U : Set (GVar S n M K k)) (G : GCfgOn N U → ℂ) :
    Integrable (fun Φ => G (restrictAll U Φ)) (gProbAll S n M K k N) ↔
      Integrable G (gcfgProb N U) := by
  classical
  have := isProbabilityMeasure_varProb hN
  have h := measurePreserving_piEquivPiSubtypeProd_gProbAll (N := N) U
  have e : (fun Φ => G (restrictAll U Φ)) = (fun p => G p.1) ∘
      MeasurableEquiv.piEquivPiSubtypeProd (fun q : GVar S n M K k => VarVal N (gIsSpin q))
        (· ∈ U) := rfl
  rw [e, h.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  exact Integrable.comp_fst_iff (IsProbabilityMeasure.ne_zero _)

end All

/-! ### The operator of a history as an expectation over the records -/

section Records

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

/-- **The weight of a realized record with its density**, as a function of the configuration of all
the global variables: `ρ(z_r) K_r e^{b_r}(z_r)`, `z_r` the configuration of the variables of the
record. -/
noncomputable def recTau (r : ↥(lfAllRecs (M := M) rep.hist k))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (Φ : GCfgAll S n M K k N) : ℂ :=
  (gDens N (recVars rep hkK r) (restrictAll _ Φ) : ℂ) *
    recW rep hkK r ψk hv g (restrictAll _ Φ)

/-- The weight of a record with its density depends only on the variables of the record. -/
theorem depOn_recTau (r : ↥(lfAllRecs (M := M) rep.hist k))
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    Polymer.DepOn (recVars rep hkK r).toFinset (recTau rep hkK r ψk hv g) := by
  intro Φ Φ' h
  have e : restrictAll (recVars rep hkK r) Φ = restrictAll (recVars rep hkK r) Φ' :=
    funext fun q => h q.1 (Set.mem_toFinset.2 q.2)
  unfold recTau
  rw [e]

theorem gDens_restrictAll_congr {U U' : Set (GVar S n M K k)} (h : U = U')
    (Φ : GCfgAll S n M K k N) : gDens N U (restrictAll U Φ) = gDens N U' (restrictAll U' Φ) := by
  subst h; rfl

/-- **The operator of a history of the large-field half is the expectation of the product of the
weights of its records with their densities** for the product `gProbAll` of the probability
measures on all the global variables (`1 ≤ N`). -/
theorem gOp_postOp_eq_integral_recTau (hN : 1 ≤ N) {A : LabHist S n R k0 K}
    (hA : A ∈ lfHist rep.hist k) (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ)
    (F : GCfg (fun c : PostComp A k => A.H.localHistory M K k c.1) k
      (postOp geo cs rep.SD rep.KD A hkK) → ℂ) :
    gOp (fun c : PostComp A k => A.H.localHistory M K k c.1) k
        (postOp geo cs rep.SD rep.KD A hkK) ψk hv g F =
      ∫ Φ, (∏ c : PostComp A k, recTau rep hkK (recOfComp rep hA c) ψk hv g Φ) *
          F ((famEquiv (fun c => (postOp geo cs rep.SD rep.KD A hkK c).A)
            (pairwise_disjoint_postOp rep hkK A)).symm (restrictAll _ Φ))
        ∂(gProbAll S n M K k N) := by
  rw [gOp_postOp_eq_prod_recW rep hkK hA, integral_gcfgMeasure hN, ← integral_restrictAll hN]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  have hD : (gDens N (⋃ c : PostComp A k, gImage (postOp geo cs rep.SD rep.KD A hkK c).A)
        (restrictAll _ Φ) : ℂ) =
      ∏ c : PostComp A k, (gDens N (recVars rep hkK (recOfComp rep hA c)) (restrictAll _ Φ) : ℂ) := by
    rw [gDens_iUnion (pairwise_disjoint_postOp rep hkK A), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun c _ => ?_
    exact congrArg (fun x : ℝ => (x : ℂ))
      (gDens_restrictAll_congr (gImage_postOp_eq rep hkK c (recOfComp rep hA c) rfl) Φ)
  dsimp only
  rw [hD]
  unfold recTau
  rw [Finset.prod_mul_distrib, mul_assoc]
  simp only [restrictOn_restrictAll]

end Records

end Balaban.RootFSpine
