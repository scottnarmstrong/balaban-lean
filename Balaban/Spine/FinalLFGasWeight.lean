/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalLFGasHist

/-!
# The expectation of the weight of a record (A6-4)

The heavy weights of the record gas are integrable, with the bound (1.26) of their kernels: for a
realized record `r` (source `(𝔸, Z)`, exponent `κ = κ_k(Z, 𝔸 ∩ Z)`) and a source `g` in the unit
`ℓ¹` ball, `E |τ_r| ≤ e^{-κ}` (`lintegral_enorm_recTauG_le`). The expectation is for the product of
the probability measures of the gas; the densities of the variables of `r` turn it into the
integral of `|K e^b|` against Lebesgue measure on `ψ_k` on the blocks of `Z` and the reference
measure of the internal variables, which is the left side of (1.26) at the parameters `ψ_k` on the
collar blocks read by the kernel; these parameters are averaged against their Gaussians.

* `enorm_w`: `‖K e^b‖ₑ = K e^{Re b}`;
* `lintegral_comp_restrict_pi`: integrating a function of some coordinates against a product of
  probability measures;
* `lintegral_inner_recW`: the inner expectation in the internal variables;
* `parOf`, `outOf_eq_mergeOut`, `measurable_mergeOut_parOf`, `blkDens_eq_psiDens_ZBlk`,
  `lintegral_outer_le`: the outer expectation in `ψ_k` and (1.26);
* `measurable_recTauG`, **`lintegral_enorm_recTauG_le`**, `integrable_recTauG`,
  `integral_norm_recTauG_le`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory
open scoped ENNReal NNReal

namespace Balaban.RootFSpine

/-- The norm of the complex weight of a kernel is the nonnegative weight. -/
theorem LFKernel.enorm_w {O X H ι : Type*} [MeasurableSpace O] [MeasurableSpace X] [Fintype ι]
    (T : LFKernel O X H ι) (o : O) (x : X) (h : H) (g : ι → ℂ) :
    ‖T.w o x h g‖ₑ = T.absW o x h g := by
  unfold LFKernel.w LFKernel.absW
  rw [← ofReal_norm, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_of_nonneg (T.K_nonneg o x h)]

/-- **Integrating a measurable function of some of the coordinates against a product of
probability measures** (lower integral) is integrating it against the product over those
coordinates. -/
theorem lintegral_comp_restrict_pi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] [Fintype (Subtype p)] (G : (∀ i : Subtype p, X i) → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ x, G (fun i => x i.1) ∂(Measure.pi μ) =
      ∫⁻ y, G y ∂(Measure.pi fun i : Subtype p => μ i) := by
  have h : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p) (Measure.pi μ)
      ((Measure.pi fun i : Subtype p => μ i).prod (Measure.pi fun i : {i // ¬ p i} => μ i)) := by
    convert measurePreserving_piEquivPiSubtypeProd μ p using 3
  have e : (fun x : ∀ i, X i => G (fun i => x i.1)) =
      (fun q => G q.1) ∘ MeasurableEquiv.piEquivPiSubtypeProd X p := rfl
  rw [e, Function.comp_def, h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (fun q => G q.1), lintegral_prod (fun q => G q.1) (hG.comp measurable_fst).aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]

section Weight

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

/-- The weight of a realized record as a function of the field and of the configuration of its
variables is measurable. -/
theorem measurable_recW (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    Measurable fun p : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) ×
        GCfgOn N (recVars rep hkK r) => recW rep hkK r p.1 hv g p.2 := by
  have hT := (recPkg rep hkK r).T
  have hK := (recPkg rep hkK r).T.measurable_K hv
  have hb := (recPkg rep hkK r).T.measurable_b hv g
  have hm : Measurable fun p : (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) ×
      GCfgOn N (recVars rep hkK r) =>
      (outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k p.1,
        (subCfgEquiv (recPkg rep hkK r).A).symm p.2) := by
    refine Measurable.prodMk ?_ ((subCfgEquiv (recPkg rep hkK r).A).symm.measurable.comp
      measurable_snd)
    exact Measurable.of_eval fun y => (measurable_pi_apply y.1).comp measurable_fst
  unfold recW LFKernel.w
  exact ((Complex.measurable_ofReal.comp (hK.comp hm)).mul
    (Complex.measurable_exp.comp (hb.comp hm)))

/-- **The inner expectation of the weight of a record in the internal variables**: against the
product of the probability measures on all the internal variables, `ρ |K e^b|` integrates to the
integral of `K e^{Re b}` against the reference measure of the variables of the record. -/
theorem lintegral_inner_recW (hN : 1 ≤ N) (r : ↥(lfAllRecs (M := M) rep.hist k))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    ∫⁻ Φg, ENNReal.ofReal (gDens N (recVars rep hkK r) (restrictAll _ Φg)) *
        ‖recW rep hkK r ψ hv g (restrictAll _ Φg)‖ₑ ∂(gProbAll S n M K k N) =
      ∫⁻ x, (recPkg rep hkK r).T.absW
          (outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ψ) x hv g
        ∂(subMeasure N ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k (recPkg rep hkK r).A) := by
  classical
  have := isProbabilityMeasure_varProb hN
  have hW : Measurable fun z : GCfgOn N (recVars rep hkK r) => ‖recW rep hkK r ψ hv g z‖ₑ :=
    ((measurable_recW rep hkK r hv g).comp (measurable_const.prodMk measurable_id)).enorm
  have hD : Measurable fun z : GCfgOn N (recVars rep hkK r) =>
      ENNReal.ofReal (gDens N (recVars rep hkK r) z) :=
    ENNReal.measurable_ofReal.comp (measurable_gDens _)
  refine (lintegral_comp_restrict_pi (fun q : GVar S n M K k => varProb N (gIsSpin q))
    (· ∈ recVars rep hkK r) (fun z => ENNReal.ofReal (gDens N (recVars rep hkK r) z) *
      ‖recW rep hkK r ψ hv g z‖ₑ) (hD.mul hW)).trans ?_
  change ∫⁻ z, ENNReal.ofReal (gDens N (recVars rep hkK r) z) * ‖recW rep hkK r ψ hv g z‖ₑ
      ∂(gcfgProb N (recVars rep hkK r)) = _
  refine (lintegral_withDensity_eq_lintegral_mul _ hD hW).symm.trans ?_
  rw [← gcfgMeasure_eq_withDensity hN]
  have hmp := (measurePreserving_subCfgEquiv (N := N) (recPkg rep hkK r).A)
  refine (hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (fun z => ‖recW rep hkK r ψ hv g z‖ₑ)).symm.trans (lintegral_congr fun x => ?_)
  unfold recW
  rw [MeasurableEquiv.symm_apply_apply, LFKernel.enorm_w]

end Weight


/-! ### The outer expectation in `ψ_k` and the bound (1.26) -/

section Outer

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k : ℕ} (a : LocalHistory S n M K)

/-- The parameters of (1.26) read off a field on the blocks outside `V ∩ Z`. -/
def parOf (ψR : {y : BlockAt S n M K k // ¬ (y ∈ Vblk R a k ∧ ZBlk a k y)} →
    EuclideanSpace ℝ (Fin N)) : OutPar N R a k :=
  fun y => ψR ⟨y.1, fun h => y.2.2 h.2⟩

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The output field read by the kernel is the merge of its values on the blocks of `Z` and of the
parameters. -/
theorem outOf_eq_mergeOut (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    outOf R a k ψ = mergeOut a k (fun y => ψ y.1) (parOf a fun y => ψ y.1) := by
  classical
  funext y
  unfold mergeOut outOf parOf
  by_cases h : ZBlk a k y.1 <;> simp [h]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The merge of the values on `Z` and of the parameters read off the other blocks is measurable
jointly. -/
theorem measurable_mergeOut_parOf :
    Measurable fun q : OutZ N R a k ×
        ({y : BlockAt S n M K k // ¬ (y ∈ Vblk R a k ∧ ZBlk a k y)} → EuclideanSpace ℝ (Fin N)) =>
      mergeOut a k q.1 (parOf a q.2) := by
  classical
  refine measurable_pi_iff.mpr fun y => ?_
  unfold mergeOut parOf
  by_cases h : ZBlk a k y.1
  · simp only [h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_snd

end Outer

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k) (hkK : k ≤ K)

theorem measurable_blkDens (Y : Finset (Torus S.d (n k))) :
    Measurable (blkDens (N := N) (M := M) (K := K) Y) := by
  classical
  unfold blkDens
  exact Finset.measurable_prod _ fun y _ => (measurable_gaussInvDens N).comp (measurable_pi_apply y)

theorem blkDens_nonneg (Y : Finset (Torus S.d (n k)))
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : 0 ≤ blkDens Y ψ := by
  classical
  unfold blkDens
  exact Finset.prod_nonneg fun _ _ => (gaussInvDens_pos N _).le

include hkK in
/-- **The density on the blocks of a record is the density on the blocks of `Z` of its kernel.** -/
theorem blkDens_eq_psiDens_ZBlk (r : ↥(lfAllRecs (M := M) rep.hist k))
    [DecidablePred fun y : BlockAt S n M K k =>
      y ∈ Vblk R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ∧
        ZBlk ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k y]
    (ψ : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    blkDens r.1.1 ψ = psiDens N (fun y : {y : BlockAt S n M K k //
      y ∈ Vblk R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ∧
        ZBlk ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k y} => ψ y.1) := by
  classical
  unfold blkDens psiDens
  refine Finset.prod_subtype _ (fun y => ?_) (fun y => gaussInvDens N (ψ y))
  rw [Finset.mem_filter, ← lfSrc_cubes rep r]
  have h1 := ZBlk_self_iff (H := (lfSrc r).1.H) hkK (lfSrc r).2 y
  constructor
  · rintro ⟨-, hy⟩
    have hZ := h1.2 hy
    exact ⟨ZBlk_mem_Vblk hkK (lfSrc r).2 y hZ, hZ⟩
  · rintro ⟨-, hZ⟩
    exact ⟨Finset.mem_univ _, h1.1 hZ⟩

/-- **The outer expectation in `ψ_k` and the bound (1.26)**: the density of `ψ_k` on the blocks
of the record turns the Gaussian expectation into Lebesgue measure on the blocks of `Z`; for every
value of the parameters (the collar blocks read by the kernel) the integral is at most `e^{-κ}`. -/
theorem lintegral_outer_le (hD5 : D5Bound (k + 1) hkK rep) (r : ↥(lfAllRecs (M := M) rep.hist k))
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    ∫⁻ ψ, ENNReal.ofReal (blkDens r.1.1 ψ) *
        ∫⁻ x, (recPkg rep hkK r).T.absW
          (outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ψ) x hv g
        ∂(subMeasure N ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k (recPkg rep hkK r).A)
        ∂(gaussPi N (BlockAt S n M K k)) ≤
      ENNReal.ofReal (Real.exp (-(rep.kappaH (lfSrc r).1 k (lfSrc r).2))) := by
  classical
  set a := (lfSrc r).1.H.localHistory M K k (lfSrc r).2 with ha
  set T := (recPkg rep hkK r).T
  set μx := subMeasure N a k (recPkg rep hkK r).A
  set κ := rep.kappaH (lfSrc r).1 k (lfSrc r).2
  set p : BlockAt S n M K k → Prop := fun y => y ∈ Vblk R a k ∧ ZBlk a k y with hp
  set G : OutT N R a k → ℝ≥0∞ := fun o => ∫⁻ x, T.absW o x hv g ∂μx with hGdef
  have hG : Measurable G := (T.measurable_absW hv g).lintegral_prod_right'
  set F' : OutZ N R a k × ({y // ¬ p y} → EuclideanSpace ℝ (Fin N)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (psiDens N q.1) * G (mergeOut a k q.1 (parOf a q.2)) with hF'def
  have hF' : Measurable F' :=
    (ENNReal.measurable_ofReal.comp ((measurable_psiDens N _).comp measurable_fst)).mul
      (hG.comp (measurable_mergeOut_parOf a))
  have e : (fun ψ => ENNReal.ofReal (blkDens r.1.1 ψ) * G (outOf R a k ψ)) =
      F' ∘ MeasurableEquiv.piEquivPiSubtypeProd (fun _ : BlockAt S n M K k =>
        EuclideanSpace ℝ (Fin N)) p := by
    funext ψ
    simp only [hF'def, Function.comp_apply]
    rw [blkDens_eq_psiDens_ZBlk rep hkK r ψ, outOf_eq_mergeOut a ψ]
    rfl
  have hmp : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : BlockAt S n M K k =>
        EuclideanSpace ℝ (Fin N)) p)
      (Measure.pi fun _ : BlockAt S n M K k => oneSiteGaussian (EuclideanSpace ℝ (Fin N)))
      ((Measure.pi fun _ : Subtype p => oneSiteGaussian (EuclideanSpace ℝ (Fin N))).prod
        (Measure.pi fun _ : {y // ¬ p y} => oneSiteGaussian (EuclideanSpace ℝ (Fin N)))) := by
    convert measurePreserving_piEquivPiSubtypeProd
      (fun _ : BlockAt S n M K k => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) p using 3
  have hK := pkgBound_lfSrc rep hkK hD5 r hv g hg
  change ∫⁻ ψ, ENNReal.ofReal (blkDens r.1.1 ψ) * G (outOf R a k ψ)
      ∂(Measure.pi fun _ : BlockAt S n M K k => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) ≤ _
  calc ∫⁻ ψ, ENNReal.ofReal (blkDens r.1.1 ψ) * G (outOf R a k ψ)
        ∂(Measure.pi fun _ : BlockAt S n M K k => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) =
      ∫⁻ ψ, F' (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : BlockAt S n M K k =>
          EuclideanSpace ℝ (Fin N)) p ψ)
        ∂(Measure.pi fun _ : BlockAt S n M K k => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) :=
        lintegral_congr fun ψ => congrFun e ψ
    _ = ∫⁻ q, F' q ∂((Measure.pi fun _ : Subtype p =>
          oneSiteGaussian (EuclideanSpace ℝ (Fin N))).prod
          (Measure.pi fun _ : {y // ¬ p y} => oneSiteGaussian (EuclideanSpace ℝ (Fin N)))) :=
        hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) F'
    _ = ∫⁻ ψR, ∫⁻ oz, F' (oz, ψR)
        ∂(Measure.pi fun _ : Subtype p => oneSiteGaussian (EuclideanSpace ℝ (Fin N)))
        ∂(Measure.pi fun _ : {y // ¬ p y} => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) :=
        lintegral_prod_symm _ hF'.aemeasurable
    _ ≤ ∫⁻ _ψR, ENNReal.ofReal (Real.exp (-κ))
        ∂(Measure.pi fun _ : {y // ¬ p y} => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) := by
        refine lintegral_mono fun ψR => ?_
        have hm : Measurable fun oz : OutZ N R a k => G (mergeOut a k oz (parOf a ψR)) :=
          hG.comp (measurable_mergeOut a k _)
        have hvol : (volume : Measure (OutZ N R a k)) =
            outPartMeasure N (Vblk R a k) (ZBlk a k) := by
          unfold outPartMeasure
          rw [volume_pi]
        have h1 : ∫⁻ oz, F' (oz, ψR)
            ∂(Measure.pi fun _ : Subtype p => oneSiteGaussian (EuclideanSpace ℝ (Fin N))) =
            ∫⁻ oz, G (mergeOut a k oz (parOf a ψR)) ∂(volume : Measure (OutZ N R a k)) := by
          rw [volume_pi_eq_withDensity N (Subtype p),
            lintegral_withDensity_eq_lintegral_mul _ (f := fun ψ => ENNReal.ofReal (psiDens N ψ))
              (ENNReal.measurable_ofReal.comp (measurable_psiDens N _)) hm]
          rfl
        rw [h1, hvol]
        exact hK (parOf a ψR)
    _ = ENNReal.ofReal (Real.exp (-κ)) := by
        rw [lintegral_const, measure_univ, mul_one]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
theorem enorm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ₑ = ENNReal.ofReal x := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx]

/-- The weight of a record in the variables of the gas is measurable. -/
theorem measurable_recTauG (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) : Measurable (recTauG rep hkK r hv g) := by
  have h1 : Measurable fun Φ : PCfg S n M K k N =>
      recW rep hkK r (psiPart Φ) hv g (restrictAll _ (gPart Φ)) :=
    (measurable_recW rep hkK r hv g).comp
      (measurable_psiPart.prodMk ((measurable_restrictAll _).comp measurable_gPart))
  unfold recTauG recTau
  exact (Complex.measurable_ofReal.comp ((measurable_blkDens _).comp measurable_psiPart)).mul
    ((Complex.measurable_ofReal.comp
      ((measurable_gDens _).comp ((measurable_restrictAll _).comp measurable_gPart))).mul h1)

/-- **The expectation of the weight of a record**: for a source `g` in the unit `ℓ¹` ball,
`E |τ_r| ≤ e^{-κ}`, `κ = κ_k(Z, 𝔸 ∩ Z)` at the source `(𝔸, Z)` of `r` (the bound (1.26) of
`D5Bound`). -/
theorem lintegral_enorm_recTauG_le (hN : 1 ≤ N) (hD5 : D5Bound (k + 1) hkK rep)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    ∫⁻ Φ, ‖recTauG rep hkK r hv g Φ‖ₑ ∂(pProb S n M K k N) ≤
      ENNReal.ofReal (Real.exp (-(rep.kappaH (lfSrc r).1 k (lfSrc r).2))) := by
  have := isProbabilityMeasure_varProb hN
  set I : GCfgAll S n M K k N × (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (gDens N (recVars rep hkK r) (restrictAll _ q.1)) *
      ‖recW rep hkK r q.2 hv g (restrictAll _ q.1)‖ₑ with hIdef
  have hI : Measurable I :=
    (ENNReal.measurable_ofReal.comp
      ((measurable_gDens _).comp ((measurable_restrictAll _).comp measurable_fst))).mul
      ((measurable_recW rep hkK r hv g).comp
        (measurable_snd.prodMk ((measurable_restrictAll _).comp measurable_fst))).enorm
  set F2 : GCfgAll S n M K k N × (BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (blkDens r.1.1 q.2) * I q with hF2def
  have hF2 : Measurable F2 :=
    (ENNReal.measurable_ofReal.comp ((measurable_blkDens _).comp measurable_snd)).mul hI
  have e : (fun Φ => ‖recTauG rep hkK r hv g Φ‖ₑ) = fun Φ => F2 (gPart Φ, psiPart Φ) := by
    funext Φ
    unfold recTauG recTau
    rw [enorm_mul, enorm_mul, enorm_ofReal_of_nonneg (blkDens_nonneg _ _),
      enorm_ofReal_of_nonneg (gDens_nonneg _ _)]
  rw [e, (measurePreserving_pSplit (S := S) (n := n) (M := M) (K := K) (k := k)
    (N := N)).lintegral_comp hF2, lintegral_prod_symm _ hF2.aemeasurable]
  calc ∫⁻ ψ, ∫⁻ Φg, F2 (Φg, ψ) ∂(gProbAll S n M K k N) ∂(gaussPi N (BlockAt S n M K k)) =
      ∫⁻ ψ, ENNReal.ofReal (blkDens r.1.1 ψ) *
        ∫⁻ x, (recPkg rep hkK r).T.absW
          (outOf R ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k ψ) x hv g
        ∂(subMeasure N ((lfSrc r).1.H.localHistory M K k (lfSrc r).2) k (recPkg rep hkK r).A)
        ∂(gaussPi N (BlockAt S n M K k)) := by
        refine lintegral_congr fun ψ => ?_
        simp only [hF2def]
        rw [lintegral_const_mul _
          (show Measurable fun Φg => I (Φg, ψ) from
            hI.comp (measurable_id.prodMk measurable_const))]
        congr 1
        exact lintegral_inner_recW rep hkK hN r ψ hv g
    _ ≤ _ := lintegral_outer_le rep hkK hD5 r hv g hg

/-- **The weights of the records are integrable**, with `∫ |τ_r| ≤ e^{-κ}`. -/
theorem integrable_recTauG (hN : 1 ≤ N) (hD5 : D5Bound (k + 1) hkK rep)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    Integrable (recTauG rep hkK r hv g) (pProb S n M K k N) :=
  ⟨(measurable_recTauG rep hkK r hv g).aestronglyMeasurable,
    (lintegral_enorm_recTauG_le rep hkK hN hD5 r hv g hg).trans_lt ENNReal.ofReal_lt_top⟩

/-- The integral of the norm of the weight of a record is at most `e^{-κ}`. -/
theorem integral_norm_recTauG_le (hN : 1 ≤ N) (hD5 : D5Bound (k + 1) hkK rep)
    (r : ↥(lfAllRecs (M := M) rep.hist k)) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    ∫ Φ, ‖recTauG rep hkK r hv g Φ‖ ∂(pProb S n M K k N) ≤
      Real.exp (-(rep.kappaH (lfSrc r).1 k (lfSrc r).2)) := by
  rw [integral_norm_eq_lintegral_enorm (measurable_recTauG rep hkK r hv g).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
    (lintegral_enorm_recTauG_le rep hkK hN hD5 r hv g hg)

end Bound

end Balaban.RootFSpine
