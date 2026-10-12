/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexSmall
public import Balaban.Fluctuation.StepComplexThm31
public import Balaban.Fluctuation.StepLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized energies of the complex step add up (FLUCTUATION.md §2.5; P4 (2.56)-(2.60))

The complex form of `StepLocal`, for the holomorphic objects of `StepComplexOut`:

* `ClassRegularLocC`: the exponent `Φ₁ = Phi1C` (a function of the complex shift `ψ'`) is
  complex-`C¹` on an open set containing the segments `s ψ'(ψ̂)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`,
  `ψ' = shiftUC ψ̂` (the analyticity (H.2) of `ℰ_k` and of the interaction on the domain of the
  composed data);
* `sum_E1locC`: `∑_z ℰ₁^{(k+1)}(z) = ℰ₁^{(k+1)}`, `sum_E0locC`: `∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}`
  for `E1locC`, `E0locC`, under `ClassRegularLocC` and `StepNonvanishingC`, at every (complex)
  block datum;
* `hatOf`, `shiftDomC`, `dataUC_inUnionDomainC_of_shiftDomC`, `analyticAt_bgC_shift`,
  `analyticAt_VkC_shift`: on the complex chart the complex old spin `ψ^{(k)}(θ) + ψ'` lies in the
  domain `𝒟(𝔹_k)` of the small solution for every complex shift `ψ'` whose hat variable
  `β_k^{1/2} C^{(k)-1/2} ψ'` is below `p⁺`; on this open set the small solution `φ_k(ψ)` and the
  interaction `V^{(k)}(ψ')` are analytic functions of `ψ'` (FLUCTUATION Lemma 2.3 (d));
* `classRegularLocC_zeroClass` (rule 10): hence `ClassRegularLocC` holds for the class with zero
  old terms at every block datum of the complex chart (real or not), `β > 0`, `p₁ < p⁺`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The exponent as a function of the complex shift -/

theorem WoneC_eq_Phi1C (s : ℝ) (x : S.E) :
    S.WoneC C s x = S.Phi1C C ((s : ℂ) • S.shiftUC x) := rfl

theorem continuous_shiftUC : Continuous S.shiftUC := by
  have h : S.shiftUC = fun x => S.psiAtC 1 x - S.psi0C :=
    funext fun x => (S.psiAtC_one_sub x).symm
  rw [h]
  exact (S.contDiff_psiAtC.continuous.comp (Continuous.prodMk_right 1)).sub continuous_const

theorem continuous_maskUC (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Continuous (S.maskUC z) := by
  classical
  refine continuous_pi fun q => ?_
  by_cases h : q.1 ∈ S.blockU z
  · simp only [maskUC, h, ↓reduceIte]; exact continuous_apply q
  · simp only [maskUC, h, ↓reduceIte]; exact continuous_const

/-- The blocks `B_{k+1}(z)` partition the unit lattice: the restrictions of a complex field add up
to the field. -/
theorem sum_maskUC (v : S.EC) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.maskUC z v = v := by
  classical
  funext q
  rw [Finset.sum_apply]
  simp only [maskUC, blockU, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_eq_single (unitBlock1 (q.1 : UnitTorus d L N₁ m₁ k))]
  · simp
  · intro z _ hz
    have : ¬ (unitBlock1 (q.1 : UnitTorus d L N₁ m₁ k) = z) := fun h => hz h.symm
    simp [this]
  · simp

theorem partFun_WoneC_eq (g : Fld d L N₁ m₁ (k + 1) N) (s : ℝ) :
    S.ZstC C g s 0 = partFun S.nuFl (S.WoneC C) s := by
  unfold ZstC partFun₂ partFun
  simp [S.WtwoC_zero C g]

/-- **Regularity of the class of the complex step in the block directions** (`ClassRegularLoc` for
the complex step; the analyticity (H.2) of `ℰ_k` and of the interaction `V^{(k)}` on the domain of
the composed data): the exponent `Φ₁(ψ') = -β_k V^{(k)}(ψ') + δℰ_k(ψ')` of the complex step
(`Phi1C`, a function of the complex shift `ψ'`) is complex-`C¹` on an open set containing the
segments `s ψ'(ψ̂)`, `s ∈ [0,1]`, `‖ψ̂‖ ≤ p₁`, `ψ'(ψ̂) = β_k^{-1/2} C^{(k)1/2}(θ) ψ̂` (`shiftUC`).
This is the hypothesis of `sum_E1locC`. -/
structure ClassRegularLocC : Prop where
  phi1 : ∃ O : Set S.EC, IsOpen O ∧ ContDiffOn ℂ 1 (S.Phi1C C) O ∧
    ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • S.shiftUC x ∈ O

section Local

variable {C} {O : Set S.EC} (hO : IsOpen O) (hcd : ContDiffOn ℂ 1 (S.Phi1C C) O)
  (hmem : ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) • S.shiftUC x ∈ O)

theorem continuous_ray_shiftUC :
    Continuous (fun q : ℝ × S.E => (q.1 : ℂ) • S.shiftUC q.2) :=
  (Complex.continuous_ofReal.comp continuous_fst).smul (S.continuous_shiftUC.comp continuous_snd)

include hcd hmem in
theorem continuousOn_Phi1C_ray :
    ContinuousOn (fun q : ℝ × S.E => S.Phi1C C ((q.1 : ℂ) • S.shiftUC q.2))
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
  refine hcd.continuousOn.comp S.continuous_ray_shiftUC.continuousOn ?_
  rintro ⟨s, x⟩ ⟨hs, hx⟩
  exact hmem x (by simpa using hx) s hs

include hO hcd hmem in
theorem continuousOn_fderivC_ray (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ContinuousOn (fun q : ℝ × S.E =>
      (fderiv ℂ (S.Phi1C C) ((q.1 : ℂ) • S.shiftUC q.2)) (S.maskUC z (S.shiftUC q.2)))
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
  have hf : ContinuousOn (fderiv ℂ (S.Phi1C C)) O :=
    hcd.continuousOn_fderiv_of_isOpen hO le_rfl
  have h1 : ContinuousOn (fun q : ℝ × S.E => fderiv ℂ (S.Phi1C C) ((q.1 : ℂ) • S.shiftUC q.2))
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : S.E) S.p₁) := by
    refine hf.comp S.continuous_ray_shiftUC.continuousOn ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact hmem x (by simpa using hx) s hs
  refine h1.clm_apply ?_
  exact (((S.continuous_maskUC z).comp S.continuous_shiftUC).comp continuous_snd).continuousOn

include hO hcd hmem in
theorem hasDerivAt_WoneC_ray {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ => S.WoneC C r x)
      ((fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.shiftUC x)) s := by
  have hd : DifferentiableAt ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x) :=
    (hcd.differentiableOn (by norm_num)).differentiableAt (hO.mem_nhds (hmem x hx s hs))
  have hp : HasDerivAt (fun τ : ℂ => τ • S.shiftUC x) (S.shiftUC x) (s : ℂ) := by
    simpa using (hasDerivAt_id (s : ℂ)).smul_const (S.shiftUC x)
  exact (hd.hasFDerivAt.comp_hasDerivAt (s : ℂ) hp).comp_ofReal

end Local

/-! ### The localized energies add up -/

/-- **`∑_z ℰ₁^{(k+1)}(z) = ℰ₁^{(k+1)}` for the complex step** (P4 (2.56)-(2.60); the complex form
of `sum_E1loc`), at every (complex) block datum: the blocks `B_{k+1}(z)` partition the unit
lattice, the complex derivative of `Φ₁ = Phi1C` is linear in the direction, and the expectations
in `μ_{s,0}` are continuous on `[0,1]`.  Premises: `ClassRegularLocC` and the nonvanishing of
`Z_{s,0}` (`StepNonvanishingC`). -/
theorem sum_E1locC (hp₁ : 0 < S.p₁) (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularLocC C)
    (hnv : S.StepNonvanishingC C g) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E1locC C z = S.E1C C := by
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  have : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  set B : Set S.E := Metric.closedBall (0 : S.E) S.p₁ with hBdef
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hB : ∀ᵐ x ∂S.nuFl, x ∈ B := S.ae_mem_closedBall hp₁
  -- the integrands
  set fz : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℝ → S.E → ℂ :=
    fun z s x => (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x))
    with hfz
  have hWc : ContinuousOn (fun q : ℝ × S.E => S.WoneC C q.1 q.2) (Icc (0 : ℝ) 1 ×ˢ B) :=
    S.continuousOn_Phi1C_ray hcd hmem
  have hEc : ContinuousOn (fun q : ℝ × S.E => Complex.exp (S.WoneC C q.1 q.2))
      (Icc (0 : ℝ) 1 ×ˢ B) := Complex.continuous_exp.comp_continuousOn hWc
  have hFc : ∀ z, ContinuousOn
      (fun q : ℝ × S.E => fz z q.1 q.2 * Complex.exp (S.WoneC C q.1 q.2))
      (Icc (0 : ℝ) 1 ×ˢ B) := fun z =>
    (S.continuousOn_fderivC_ray hO hcd hmem z).mul hEc
  -- denominators
  have hZ : ∀ s ∈ Icc (0 : ℝ) 1, partFun S.nuFl (S.WoneC C) s ≠ 0 := fun s hs => by
    rw [← S.partFun_WoneC_eq C g]; exact hnv.seg1 s hs
  have hZc : ContinuousOn (partFun S.nuFl (S.WoneC C)) (Icc (0 : ℝ) 1) :=
    continuousOn_integral_param hBc hBm hB (F := fun s x => Complex.exp (S.WoneC C s x)) hEc
  -- the averages are continuous
  have havg : ∀ z, ContinuousOn (fun s => avgFun S.nuFl (S.WoneC C) (fz z s) s)
      (Icc (0 : ℝ) 1) :=
    fun z => (continuousOn_integral_param hBc hBm hB (hFc z)).div hZc hZ
  -- sum identity at each `s`
  have hint : ∀ z, ∀ s ∈ Icc (0 : ℝ) 1,
      Integrable (fun x => fz z s x * Complex.exp (S.WoneC C s x)) S.nuFl := fun z s hs =>
    integrable_of_continuousOn hBc hB
      ((hFc z).comp (f := fun x => (s, x)) (by fun_prop) (fun x hx => ⟨hs, hx⟩))
  have hsum : ∀ s ∈ Icc (0 : ℝ) 1,
      ∑ z, avgFun S.nuFl (S.WoneC C) (fz z s) s =
        avgFun S.nuFl (S.WoneC C) (fun x => deriv (fun r => S.WoneC C r x) s) s := by
    intro s hs
    unfold avgFun
    rw [← Finset.sum_div, ← integral_finsetSum _ (fun z _ => hint z s hs)]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hB] with x hx
    rw [← Finset.sum_mul]
    congr 1
    rw [(S.hasDerivAt_WoneC_ray hO hcd hmem (mem_closedBall_zero_iff.1 hx) hs).deriv]
    simp only [hfz]
    rw [← map_sum, S.sum_maskUC]
  unfold E1locC E1C
  rw [← intervalIntegral.integral_finsetSum]
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact hsum s hs
  · intro z _
    exact (havg z).intervalIntegrable_of_Icc zero_le_one

/-- **`∑_z ℰ₀^{(k+1)}(z) = ℰ₀^{(k+1)}` for the complex step** (P4 (2.56); the complex form of
`sum_E0loc`), at every (complex) block datum: the trace parts add up to the analytic
`½ log det C^{(k)}` (`sum_trace_E0locC`), the rest is `sum_E1locC`. -/
theorem sum_E0locC (hp₁ : 0 < S.p₁) (g : Fld d L N₁ m₁ (k + 1) N) (hc : S.ClassRegularLocC C)
    (hnv : S.StepNonvanishingC C g) :
    ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))), S.E0locC C z = S.E0C C :=
  sum_E0locC_of_sum_E1locC S C (S.sum_E1locC C hp₁ g hc hnv)

/-! ### The hat variable of a complex shift -/

/-- The hat variable `ψ̂ = β_k^{1/2} C^{(k)-1/2}(θ) ψ'` of a complex shift `ψ'` of the unit lattice
(the inverse of the substitution (2.7) at a complex datum, with the inverse matrix of
`covSqrtC`). -/
noncomputable def hatOf (y : S.EC) : S.EC :=
  (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))⁻¹ • (S.covSqrtC⁻¹ *ᵥ y)

/-- The complex shifts `ψ'` whose hat variable is below `p⁺` in every coordinate: an open set of
`(ℂ^N)^{T^{(k)}_1}` containing the shifts `s ψ'(ψ̂)` of the path (`s ∈ [0,1]`, `‖ψ̂‖ < p⁺`). -/
def shiftDomC (pp : ℝ) : Set S.EC := {y | ∀ p, ‖S.hatOf y p‖ < pp}

theorem continuous_hatOf : Continuous S.hatOf := by
  have h : Continuous (fun y : S.EC => S.covSqrtC⁻¹ *ᵥ y) := by
    refine continuous_pi fun p => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun r _ =>
      continuous_const.mul (continuous_apply r : Continuous fun y : S.EC => y r)
  exact h.const_smul (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))⁻¹

theorem isOpen_shiftDomC (pp : ℝ) : IsOpen (S.shiftDomC pp) := by
  have : S.shiftDomC pp = ⋂ p, {y : S.EC | ‖S.hatOf y p‖ < pp} := by
    ext y; simp [shiftDomC]
  rw [this]
  exact isOpen_iInter_of_finite fun p =>
    isOpen_lt (continuous_norm.comp ((continuous_apply p).comp S.continuous_hatOf))
      continuous_const

theorem shiftUC_eq_smul_mulVec (x : S.E) :
    S.shiftUC x = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.covSqrtC *ᵥ yhat x) := rfl

/-- On the ray, each coordinate of the hat variable is bounded by `|s| ‖ψ̂‖`. -/
theorem norm_smul_yhat_le_mul (s : ℝ) (x : S.E) (p : S.U × Fin N) :
    ‖((s : ℂ) • yhat x) p‖ ≤ |s| * ‖x‖ := by
  have h1 : ‖((x p.1 p.2 : ℝ) : ℂ)‖ ≤ ‖x‖ := by
    rw [Complex.norm_real]
    exact (PiLp.norm_apply_le (x p.1) p.2).trans (norm_le_pi_norm x p.1)
  show ‖(s : ℂ) * ((x p.1 p.2 : ℝ) : ℂ)‖ ≤ |s| * ‖x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

section HatInverse

variable (hdet : IsUnit S.covSqrtC.det) (hcc : ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0)

include hdet hcc in
/-- The substitution (2.7) of the hat variable of a shift returns the shift, when `C^{(k)1/2}` is
invertible. -/
theorem smul_mulVec_hatOf (y : S.EC) :
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.covSqrtC *ᵥ S.hatOf y) = y := by
  unfold hatOf
  rw [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hcc, one_smul, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

include hdet hcc in
/-- The hat variable of the shift `s ψ'(ψ̂)` of the path is `s ψ̂`. -/
theorem hatOf_smul_shiftUC (s : ℝ) (x : S.E) :
    S.hatOf ((s : ℂ) • S.shiftUC x) = (s : ℂ) • yhat x := by
  unfold hatOf
  rw [S.shiftUC_eq_smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec, smul_smul, smul_smul, mul_right_comm,
    inv_mul_cancel₀ hcc, one_mul]

include hdet hcc in
/-- The shifts of the path lie in `shiftDomC p⁺` for `|s| ‖ψ̂‖ < p⁺`. -/
theorem smul_shiftUC_mem_shiftDomC {pp : ℝ} {s : ℝ} {x : S.E} (h : |s| * ‖x‖ < pp) :
    (s : ℂ) • S.shiftUC x ∈ S.shiftDomC pp := fun p => by
  rw [S.hatOf_smul_shiftUC hdet hcc]
  exact lt_of_le_of_lt (S.norm_smul_yhat_le_mul s x p) h

end HatInverse

/-! ### On the complex chart: the small solution and the interaction as functions of the shift -/

section Chart

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 < S.β) {pp : ℝ} (hpp : 0 < pp)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hβ in
theorem betaU_rpow_ne_zero : ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact_mod_cast (Real.rpow_pos_of_pos (S.betaU_pos' hL hβ) _).ne'

include hC hMX hdm hα hsm hD in
/-- `C^{(k)1/2}` of the complex step is invertible on the complex chart. -/
theorem isUnit_det_covSqrtC : IsUnit S.covSqrtC.det := by
  rw [S.det_covSqrtC_of_chart hC hMX hdm hα hsm hD]
  exact (Complex.exp_ne_zero _).isUnit

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The complex old spin `ψ^{(k)}(θ) + ψ'` lies in the domain `𝒟(𝔹_k)` of the small solution for
every complex shift `ψ'` of `shiftDomC p⁺`** (FLUCTUATION Lemma 2.3 (d), for a complex block datum
of the chart and a complex shift; `hreal_level`). -/
theorem dataUC_inUnionDomainC_of_shiftDomC {y : S.EC} (hy : y ∈ S.shiftDomC pp) :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psi0C + y)) := by
  refine inUnionDomainC_of_tangent_hatLift hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR hMX hdm hα
    hsm _ hpp.le (by rwa [S.norm_betaU_rpow hβ.le]) (ψh := S.hatOf y) (fun p => (hy p).le) hD
    (fun z i => by rw [S.dataUC_h, S.hh₀]) ?_
  rw [S.compTangent_dataUC, add_sub_cancel_left, S.hatLift_eq_liftC,
    S.smul_mulVec_hatOf (S.isUnit_det_covSqrtC hC hMX hdm hα hsm hD) (S.betaU_rpow_ne_zero hβ)]

/-- The raw data of the complex old spin `ψ^{(k)}(θ) + ψ'` are analytic (affine) in the shift. -/
theorem analyticAt_rawUC_shift (y₀ : S.EC) :
    AnalyticAt ℂ (fun y : S.EC => S.rawUC (S.psi0C + y)) y₀ := by
  unfold rawUC
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun z => analyticAt_pi_iff.2 fun i => ?_)
    analyticAt_const
  simp only [liftC_apply, Pi.add_apply]
  exact analyticAt_const.add
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ)
      (unitPt S.hG' z, i)).analyticAt y₀)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The small solution `(φ_k(ψ), α_k(ψ))` of the complex old spin `ψ = ψ^{(k)}(θ) + ψ'` is an
analytic function of the complex shift `ψ'` on `shiftDomC p⁺`** (Theorem 7.2, analyticity,
composed with the affine map `ψ' ↦ (ψ, h)`): one function of `ψ'`, analytic on the open set
`shiftDomC p⁺`, returns `(bgFieldC, bgMultC)` of `dataUC (ψ^{(k)} + ψ')` there. -/
theorem exists_analytic_bgC_shift :
    ∃ F : S.EC → ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ),
      AnalyticOnNhd ℂ F (S.shiftDomC pp) ∧ ∀ y ∈ S.shiftDomC pp,
        F y = (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + y)),
          bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (S.dataUC (S.psi0C + y))) := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν)
    (N := N) hC.HBp
  refine ⟨fun y => F (S.rawUC (S.psi0C + y)), fun y hy => ?_, fun y hy => ?_⟩
  · have hdom := S.dataUC_inUnionDomainC_of_shiftDomC hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
      hδ₁ hD hy
    have hFat : AnalyticAt ℂ F (S.rawUC (S.psi0C + y)) :=
      hF _ ⟨S.dataUC (S.psi0C + y), hdom, (S.dataUC_raw _).symm⟩
    exact AnalyticAt.comp (f := fun y : S.EC => S.rawUC (S.psi0C + y)) hFat
      (S.analyticAt_rawUC_shift y)
  · have hdom := S.dataUC_inUnionDomainC_of_shiftDomC hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
      hδ₁ hD hy
    have hFq := hFe (S.dataUC (S.psi0C + y)) hdom
    rw [S.dataUC_raw] at hFq
    exact hFq

include hC ha₁ hc7 hD in
/-- On the complex chart `H_k` and the constraint form `φ_{k+1} · G_k φ_{k+1}` at the complex
background of the block datum are invertible (`base_standing`). -/
theorem isUnit_opHk_bgC :
    IsUnit (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')) ∧
    IsUnit (constraintForm
      (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D'))⁻¹
      (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))) := by
  have hD'2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D' :=
    (isDecBg_one_of_xiCData hC hD).2.mono (hc7.trans (thm73C3_le_thm73C2 d L N))
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ S.hG S.hG' (le_refl (k + 1)) hC.HBp hC.HBp S.D'
    hD'2
  have hΦ' : restrictField (stepG d L N₁ m₁ k ϱ) Φ =
      fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') := funext fun x => funext fun i => hΦ x i
  refine ⟨dirichletOperator_isUnit (stepG d L N₁ m₁ k ϱ) St.pos St.mass St.weights _ St.alpha, ?_⟩
  rw [← hΦ']
  exact constraintForm_isUnit St

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **The interaction `V^{(k)}(ψ')` of the complex step is an analytic function of the complex
shift `ψ'` on `shiftDomC p⁺`** (FLUCTUATION Lemma 2.3 (d): `V^{(k)}` is analytic in
`(ψ', φ_{k+1}, α_{k+1})`, with the analytic small solution `φ_k(ψ)`), for a block datum of the
complex chart. -/
theorem analyticAt_VkC_shift {y₀ : S.EC} (hy₀ : y₀ ∈ S.shiftDomC pp) :
    AnalyticAt ℂ (fun y : S.EC => S.VkC (S.psi0C + y)) y₀ := by
  obtain ⟨F, hFan, hF⟩ := S.exists_analytic_bgC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp
    hδ₁ hD
  obtain ⟨hH, hM⟩ := S.isUnit_opHk_bgC hC ha₁ hc7 hD
  have hFat := hFan y₀ hy₀
  have hmodel := analyticAt_interactionV (q₀ := y₀) (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (αF := fun _ : S.EC => bgMultC S.G' S.a S.ν (bgC0 d L N) S.D')
    (φF := fun _ : S.EC => bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')
    (ψF := fun y : S.EC => liftC S.hG' y)
    (φ'F := fun y : S.EC => (F y).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D'))
    (fun _ => analyticAt_const) (fun _ => analyticAt_const)
    (fun z i => by
      simp only [liftC_apply]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ)
        (unitPt S.hG' z, i)).analyticAt y₀)
    (fun r => (analyticAt_pi_iff.1 (analyticAt_fst.comp hFat) r).sub analyticAt_const) hH hM
  refine hmodel.congr ?_
  filter_upwards [(S.isOpen_shiftDomC pp).mem_nhds hy₀] with y hy
  unfold VkC
  rw [S.compTangent_dataUC, add_sub_cancel_left, hF y hy]

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD in
/-- **`ClassRegularLocC` holds for the class with zero old terms on the complex chart** (rule 10;
real or nonreal block datum, `β > 0`, `p₁ < p⁺`): `Φ₁ = -β_k V^{(k)}` is analytic on the open set
`shiftDomC p⁺`, which contains the segments of the path. -/
theorem classRegularLocC_zeroClass (hlt : S.p₁ < pp) :
    S.ClassRegularLocC (zeroClass d L N₁ m₁ k N ϱ) := by
  have hdet := S.isUnit_det_covSqrtC hC hMX hdm hα hsm hD
  have hcc := S.betaU_rpow_ne_zero hβ
  refine ⟨S.shiftDomC pp, S.isOpen_shiftDomC pp, ?_, fun x hx s hs => ?_⟩
  · have hΦ : S.Phi1C (zeroClass d L N₁ m₁ k N ϱ) =
        fun y => -(S.β : ℂ) * S.VkC (S.psi0C + y) := by
      funext y
      unfold Phi1C
      rw [dEC_zeroClass, add_zero]
    rw [hΦ]
    have han : AnalyticOnNhd ℂ (fun y : S.EC => -(S.β : ℂ) * S.VkC (S.psi0C + y))
        (S.shiftDomC pp) := fun y hy =>
      analyticAt_const.mul
        (S.analyticAt_VkC_shift hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ hD hy)
    exact han.contDiffOn_of_completeSpace
  · refine S.smul_shiftUC_mem_shiftDomC hdet hcc ?_
    have hs' : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    calc |s| * ‖x‖ ≤ 1 * S.p₁ := mul_le_mul hs' hx (norm_nonneg _) zero_le_one
      _ < pp := by rw [one_mul]; exact hlt

end Chart

end StepSetting

end Balaban.Fluctuation
