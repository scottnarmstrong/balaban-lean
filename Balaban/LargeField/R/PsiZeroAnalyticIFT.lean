/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroAbstract
public import Balaban.Analysis.Contraction
import Mathlib

/-!
# Analytic zero of the gradient near a real nondegenerate critical point

Abstract complexification step behind the analyticity of `ψ⁰_k` (Lemma III.3.3).  Let `Fc` be a complex-valued function
of `(u, p) ∈ ℂ^ι × P_ℂ` that is complex-analytic at a real point `(u₀, p₀)` and real-valued on real points near it
(the real parameters embedded by `jP : P_ℝ → P_ℂ`).  If the real function `Fre = Re (Fc ∘ embedding)` has a critical
point `u₀` in `u` at `p₀` with positive definite Hessian, then (`analytic_zero_of_real_critical`) the complex zero
`ξ(q)` of `∂_u Fc(u₀ + ·, q)` near `0` exists for `q` in a ball about `jP p₀`, is complex-analytic in `q`, and for
real `q = jP p` it is real, a real critical point of `Fre(·, p)`.  The proof is the analytic contraction
`exists_analytic_zero` with the Newton-type map `ξ ↦ ξ - A⁻¹ ∇ Fc` (`A` the complex Hessian at the base point, which
is injective because the real Hessian is positive definite), and the real fixed point is the limit of the real
iterates.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Metric Filter Topology

namespace Balaban.LargeField.RealCrit

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC]

/-- The embedding `ℝ^ι → ℂ^ι` of real vectors. -/
noncomputable def jEL : EuclideanSpace ℝ ι →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (EuclideanSpace.proj j)

theorem jEL_apply (u : EuclideanSpace ℝ ι) (j : ι) : jEL u j = (u j : ℂ) := rfl

/-- the embedding of real pairs -/
noncomputable def kP (jP : PR →L[ℝ] PC) : EuclideanSpace ℝ ι × PR →L[ℝ] (ι → ℂ) × PC :=
  jEL.prodMap jP

theorem kP_apply (jP : PR →L[ℝ] PC) (u : EuclideanSpace ℝ ι) (p : PR) :
    kP jP (u, p) = (jEL u, jP p) := rfl

/-- the real part of `Fc` on real points -/
noncomputable def Fre (jP : PR →L[ℝ] PC) (Fc : (ι → ℂ) × PC → ℂ) : EuclideanSpace ℝ ι × PR → ℝ :=
  fun z => (Fc (kP jP z)).re

variable (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

theorem contDiffAt_Fre {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z)) (n : ℕ) :
    ContDiffAt ℝ n (Fre jP Fc) z := by
  have h1 : ContDiffAt ℝ n Fc (kP jP z) := (h.contDiffAt (n := n)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ n (fun w => Fc (kP jP w)) z := by
    exact ContDiffAt.comp (g := Fc) (f := kP (ι := ι) jP) z h1 (ContDiff.contDiffAt (ContinuousLinearMap.contDiff (kP (ι := ι) jP)))
  exact Complex.reCLM.contDiff.contDiffAt.comp z h2

/-- the complex derivative at a real point restricted to real directions is the real derivative -/
theorem fderiv_Fre_eq {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z))
    (him : ∀ᶠ w in 𝓝 z, (Fc (kP jP w)).im = 0) (v : EuclideanSpace ℝ ι × PR) :
    ((fderiv ℝ (Fre jP Fc) z v : ℝ) : ℂ) = fderiv ℂ Fc (kP jP z) (kP jP v) := by
  have h1 : DifferentiableAt ℂ Fc (kP jP z) := h.differentiableAt
  have hD : HasFDerivAt (fun w => Fc (kP jP w))
      (((fderiv ℂ Fc (kP jP z)).restrictScalars ℝ).comp (kP jP)) z :=
    (h1.hasFDerivAt.restrictScalars ℝ).comp z (kP jP).hasFDerivAt
  have hR : DifferentiableAt ℝ (Fre jP Fc) z :=
    ((contDiffAt_Fre jP h 1).differentiableAt (by norm_num))
  have hR' : HasFDerivAt (fun w => ((Fre jP Fc w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (Fre jP Fc) z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hR.hasFDerivAt
  have hev : (fun w => ((Fre jP Fc w : ℝ) : ℂ)) =ᶠ[𝓝 z] fun w => Fc (kP jP w) := by
    filter_upwards [him] with w hw
    exact (Complex.ext (by simp [Fre]) (by simpa [Fre] using hw.symm))
  have := (hev.hasFDerivAt_iff.mp hR')
  have e := this.unique hD
  have := congrArg (fun f => f v) e
  simpa using this

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] {Fc : (ι → ℂ) × PC → ℂ}

/-- the complex gradient `g z j = ∂_{u_j} Fc z` -/
noncomputable def gradC (Fc : (ι → ℂ) × PC → ℂ) : (ι → ℂ) × PC → (ι → ℂ) :=
  fun z j => fderiv ℂ Fc z (Pi.single j 1, 0)

theorem analyticAt_gradC {z : (ι → ℂ) × PC} (h : AnalyticAt ℂ Fc z) : AnalyticAt ℂ (gradC Fc) z := by
  refine AnalyticAt.pi fun j => ?_
  exact ((ContinuousLinearMap.apply ℂ ℂ ((Pi.single j 1 : ι → ℂ), (0 : PC))).analyticAt _).comp (AnalyticAt.fderiv h)

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

theorem kP_zero_right (x : EuclideanSpace ℝ ι) :
    kP jP (x, 0) = (jEL x, 0) := by simp [kP_apply]

theorem jEL_single (j : ι) : jEL (EuclideanSpace.single j (1:ℝ)) = Pi.single j (1 : ℂ) := by
  funext l
  by_cases h : l = j
  · subst h; simp [jEL_apply]
  · simp [jEL_apply, h]

theorem gradC_real {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z))
    (him : ∀ᶠ w in 𝓝 z, (Fc (kP jP w)).im = 0) (j : ι) :
    gradC Fc (kP jP z) j =
      ((fderiv ℝ (Fre jP Fc) z (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ) := by
  have := fderiv_Fre_eq jP h him (EuclideanSpace.single j (1:ℝ), 0)
  rw [this, kP_zero_right, jEL_single]
  rfl

/-- The complex Hessian at a real point restricted to real vectors is the real Hessian. -/
theorem hessian_real {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z))
    (him : ∀ᶠ w in 𝓝 z, (Fc (kP jP w)).im = 0) (x : EuclideanSpace ℝ ι) (j : ι) :
    (fderiv ℂ (gradC Fc) (kP jP z) (jEL x, 0)) j =
      ((fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (x, 0) (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ) := by
  have hk : Continuous (kP (ι := ι) jP) := (kP (ι := ι) jP).continuous
  have hAn : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ Fc (kP jP w) :=
    hk.continuousAt.eventually h.eventually_analyticAt
  have hboth : (fun w => gradC Fc (kP jP w) j) =ᶠ[𝓝 z]
      fun w => ((fderiv ℝ (Fre jP Fc) w (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ) := by
    filter_upwards [hAn, him.eventually_nhds] with w hw hw2
    exact gradC_real jP hw hw2 j
  -- derivative of the left side
  have hg : DifferentiableAt ℂ (gradC Fc) (kP jP z) := (analyticAt_gradC h).differentiableAt
  have hL : HasFDerivAt (fun w => gradC Fc (kP jP w))
      (((fderiv ℂ (gradC Fc) (kP jP z)).restrictScalars ℝ).comp (kP jP)) z :=
    (hg.hasFDerivAt.restrictScalars ℝ).comp z (kP jP).hasFDerivAt
  have hLj : HasFDerivAt (fun w => gradC Fc (kP jP w) j)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j).comp
        (((fderiv ℂ (gradC Fc) (kP jP z)).restrictScalars ℝ).comp (kP jP))) z :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j).hasFDerivAt.comp z hL
  -- derivative of the right side
  have hF2 : ContDiffAt ℝ 2 (Fre jP Fc) z := contDiffAt_Fre jP h 2
  have hF1 : ContDiffAt ℝ 1 (fderiv ℝ (Fre jP Fc)) z :=
    hF2.fderiv_right (by norm_num)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ (Fre jP Fc)) z := hF1.differentiableAt (by norm_num)
  have hR : HasFDerivAt (fun w => fderiv ℝ (Fre jP Fc) w (EuclideanSpace.single j (1:ℝ), 0))
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1:ℝ), (0 : PR))).comp
        (fderiv ℝ (fderiv ℝ (Fre jP Fc)) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1:ℝ), (0 : PR))).hasFDerivAt.comp z
      hD1.hasFDerivAt
  have hR' : HasFDerivAt (fun w => ((fderiv ℝ (Fre jP Fc) w (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1:ℝ), (0 : PR))).comp
        (fderiv ℝ (fderiv ℝ (Fre jP Fc)) z))) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hR
  have hLj' := hboth.hasFDerivAt_iff.mp hLj
  have e := hLj'.unique hR'
  have := congrArg (fun f => f (x, 0)) e
  simpa [kP_zero_right] using this

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

/-- real part of a complex vector -/
noncomputable def reE (z : ι → ℂ) : EuclideanSpace ℝ ι := WithLp.toLp 2 fun j => (z j).re
noncomputable def imE (z : ι → ℂ) : EuclideanSpace ℝ ι := WithLp.toLp 2 fun j => (z j).im

theorem decomp (z : ι → ℂ) : z = jEL (reE z) + Complex.I • jEL (imE z) := by
  funext j
  simp [jEL_apply, reE, imE, Complex.ext_iff]

/-- the complex derivative of the gradient at a base point, in complex directions of the first factor -/
noncomputable def hessC (jP : PR →L[ℝ] PC) (Fc : (ι → ℂ) × PC → ℂ) (z : EuclideanSpace ℝ ι × PR) :
    (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  (fderiv ℂ (gradC Fc) (kP jP z)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) PC)

theorem hessC_real {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z))
    (him : ∀ᶠ w in 𝓝 z, (Fc (kP jP w)).im = 0) (x : EuclideanSpace ℝ ι) (j : ι) :
    hessC jP Fc z (jEL x) j =
      ((fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (x, 0) (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ) :=
  hessian_real jP h him x j

theorem clm_expand (f : EuclideanSpace ℝ ι →L[ℝ] ℝ) (v : EuclideanSpace ℝ ι) :
    f v = ∑ j, v j * f (EuclideanSpace.single j 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr v]
  simp [map_sum]

theorem hessC_injective {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z))
    (him : ∀ᶠ w in 𝓝 z, (Fc (kP jP w)).im = 0) {c : ℝ} (hc : 0 < c)
    (hpos : ∀ v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0) (v, 0)) :
    Function.Injective (hessC jP Fc z) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  set a := reE w
  set b := imE w
  have hq : ∀ v : EuclideanSpace ℝ ι, (∀ j, fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0)
      (EuclideanSpace.single j (1:ℝ), 0) = 0) → v = 0 := by
    intro v hv
    have hcl : fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0) (v, 0) = 0 := by
      let ℓ : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
        (fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0)).comp (ContinuousLinearMap.inl ℝ _ PR)
      have : ℓ v = ∑ j, v j * ℓ (EuclideanSpace.single j 1) := clm_expand ℓ v
      have h0 : ∀ j, ℓ (EuclideanSpace.single j 1) = 0 := fun j => hv j
      simpa [ℓ, h0] using this
    have := hpos v
    rw [hcl] at this
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hdec : w = jEL a + Complex.I • jEL b := decomp w
  have hAw : hessC jP Fc z w = hessC jP Fc z (jEL a) + Complex.I • hessC jP Fc z (jEL b) := by
    conv_lhs => rw [hdec]
    simp
  have hj : ∀ j, ((fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (a, 0) (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (b, 0) (EuclideanSpace.single j (1:ℝ), 0) : ℝ) : ℂ) = 0 := by
    intro j
    have := congrFun hAw j
    rw [hw] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [hessC_real jP h him a j, hessC_real jP h him b j] at this
    exact this.symm
  have ha : a = 0 := hq a fun j => by
    have := hj j
    have h1 := congrArg Complex.re this
    simpa using h1
  have hb : b = 0 := hq b fun j => by
    have := hj j
    have h1 := congrArg Complex.im this
    simpa using h1
  rw [hdec, ha, hb]; simp

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

theorem exists_inv {z : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z))
    (him : ∀ᶠ w in 𝓝 z, (Fc (kP jP w)).im = 0) {c : ℝ} (hc : 0 < c)
    (hpos : ∀ v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0) (v, 0)) :
    ∃ B : (ι → ℂ) →L[ℂ] (ι → ℂ), (∀ y, hessC jP Fc z (B y) = y) ∧ (∀ y, B (hessC jP Fc z y) = y) ∧
      Function.Injective B ∧ ∀ y : EuclideanSpace ℝ ι, ∃ x : EuclideanSpace ℝ ι, B (jEL y) = jEL x := by
  have hinj := hessC_injective jP h him hc hpos
  let e : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) := LinearEquiv.ofInjectiveEndo (hessC jP Fc z).toLinearMap hinj
  let ec : (ι → ℂ) ≃L[ℂ] (ι → ℂ) := e.toContinuousLinearEquiv
  have he : ∀ y, hessC jP Fc z (ec.symm y) = y := fun y => ec.apply_symm_apply y
  have he' : ∀ y, ec.symm (hessC jP Fc z y) = y := fun y => ec.symm_apply_apply y
  refine ⟨(ec.symm : (ι → ℂ) →L[ℂ] (ι → ℂ)), he, he', ec.symm.injective, fun y => ?_⟩
  set w := ec.symm (jEL y) with hw
  have hAw : hessC jP Fc z w = jEL y := he _
  set a := reE w
  set b := imE w
  have hdec : w = jEL a + Complex.I • jEL b := decomp w
  have hAw2 : hessC jP Fc z w = hessC jP Fc z (jEL a) + Complex.I • hessC jP Fc z (jEL b) := by
    conv_lhs => rw [hdec]
    simp
  have hq : ∀ v : EuclideanSpace ℝ ι, (∀ j, fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0)
      (EuclideanSpace.single j (1:ℝ), 0) = 0) → v = 0 := by
    intro v hv
    have hcl : fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0) (v, 0) = 0 := by
      let ℓ : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
        (fderiv ℝ (fderiv ℝ (Fre jP Fc)) z (v, 0)).comp (ContinuousLinearMap.inl ℝ _ PR)
      have : ℓ v = ∑ j, v j * ℓ (EuclideanSpace.single j 1) := clm_expand ℓ v
      have h0 : ∀ j, ℓ (EuclideanSpace.single j 1) = 0 := fun j => hv j
      simpa [ℓ, h0] using this
    have := hpos v
    rw [hcl] at this
    have h2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  have hb : b = 0 := hq b fun j => by
    have := congrFun hAw j
    rw [hAw2] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [hessC_real jP h him a j, hessC_real jP h him b j, jEL_apply] at this
    have h1 := congrArg Complex.im this
    simpa using h1
  refine ⟨a, ?_⟩
  show w = jEL a
  rw [hdec, hb]; simp

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

theorem norm_le_card_mul (x : EuclideanSpace ℝ ι) : ‖x‖ ≤ (Fintype.card ι : ℝ) * ‖jEL x‖ := by
  have h1 : x = ∑ j, x j • EuclideanSpace.single j (1:ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr x]
    simp
  calc ‖x‖ = ‖∑ j, x j • EuclideanSpace.single j (1:ℝ)‖ := by rw [← h1]
    _ ≤ ∑ j, ‖x j • EuclideanSpace.single j (1:ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : ι, ‖jEL x‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul]
        simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
        have : ‖jEL x j‖ ≤ ‖jEL x‖ := norm_le_pi_norm (jEL x) j
        simpa [jEL_apply] using this
    _ = (Fintype.card ι : ℝ) * ‖jEL x‖ := by simp

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

theorem mem_ball_prod {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {w w0 : E × F} {δ : ℝ}
    (h1 : ‖w.1 - w0.1‖ < δ) (h2 : ‖w.2 - w0.2‖ < δ) : w ∈ ball w0 δ := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨by rwa [dist_eq_norm], by rwa [dist_eq_norm]⟩

theorem norm_inl_le (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] : ‖ContinuousLinearMap.inl ℂ E F‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)

/-- the contraction estimate near the base point -/
theorem exists_hess_nbhd {w0 : (ι → ℂ) × PC} (hg : AnalyticAt ℂ (gradC Fc) w0)
    (B : (ι → ℂ) →L[ℂ] (ι → ℂ))
    (hBA : ∀ y, B ((fderiv ℂ (gradC Fc) w0).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) PC) y) = y) :
    ∃ δ > 0, ∀ w ∈ ball w0 δ,
      ‖ContinuousLinearMap.id ℂ (ι → ℂ) - B.comp ((fderiv ℂ (gradC Fc) w).comp
        (ContinuousLinearMap.inl ℂ (ι → ℂ) PC))‖ ≤ 1 / 2 := by
  have hc : ContinuousAt (fderiv ℂ (gradC Fc)) w0 := (AnalyticAt.fderiv hg).continuousAt
  have hpos : 0 < 1 / (2 * (‖B‖ + 1)) := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hc _ hpos
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hd := hball (mem_ball.mp hw)
  rw [dist_eq_norm] at hd
  have e : ContinuousLinearMap.id ℂ (ι → ℂ) - B.comp ((fderiv ℂ (gradC Fc) w).comp
        (ContinuousLinearMap.inl ℂ (ι → ℂ) PC)) = B.comp (((fderiv ℂ (gradC Fc) w0) - fderiv ℂ (gradC Fc) w).comp
        (ContinuousLinearMap.inl ℂ (ι → ℂ) PC)) := by
    ext y
    have := hBA y
    simp only [sub_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.id_apply, map_sub] at this ⊢
    rw [this]
  rw [e]
  calc ‖B.comp (((fderiv ℂ (gradC Fc) w0) - fderiv ℂ (gradC Fc) w).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) PC))‖
      ≤ ‖B‖ * ‖((fderiv ℂ (gradC Fc) w0) - fderiv ℂ (gradC Fc) w).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) PC)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖ * (‖(fderiv ℂ (gradC Fc) w0) - fderiv ℂ (gradC Fc) w‖ * 1) := by
        gcongr
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
          gcongr; exact norm_inl_le _ _)
    _ ≤ 1 / 2 := by
        rw [mul_one, norm_sub_rev]
        have h1 : ‖B‖ * ‖fderiv ℂ (gradC Fc) w - fderiv ℂ (gradC Fc) w0‖ ≤ ‖B‖ * (1 / (2 * (‖B‖ + 1))) := by
          gcongr
        have h2 : ‖B‖ * (1 / (2 * (‖B‖ + 1))) ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [norm_nonneg B]
        linarith

end Balaban.LargeField.RealCrit

namespace Balaban.LargeField.RealCrit
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {PR : Type*} [NormedAddCommGroup PR] [NormedSpace ℝ PR]
  {PC : Type*} [NormedAddCommGroup PC] [NormedSpace ℂ PC] (jP : PR →L[ℝ] PC) {Fc : (ι → ℂ) × PC → ℂ}

theorem analytic_zero_of_real_critical
    {z0 : EuclideanSpace ℝ ι × PR} (h : AnalyticAt ℂ Fc (kP jP z0))
    (him : ∀ᶠ w in 𝓝 z0, (Fc (kP jP w)).im = 0) (hjP : ∀ p, ‖jP p‖ = ‖p‖)
    (hcrit : ∀ v : EuclideanSpace ℝ ι, fderiv ℝ (Fre jP Fc) z0 (v, 0) = 0)
    {c : ℝ} (hc : 0 < c)
    (hpos : ∀ v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (Fre jP Fc)) z0 (v, 0) (v, 0))
    {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ ρ > 0, ∃ r > 0, ∃ ξ : PC → (ι → ℂ),
      AnalyticOnNhd ℂ ξ (ball (jP z0.2) ρ) ∧ ξ (jP z0.2) = 0 ∧
      (∀ q ∈ ball (jP z0.2) ρ, ‖ξ q‖ ≤ r ∧ gradC Fc (jEL z0.1 + ξ q, q) = 0) ∧
      (∀ p : PR, ‖p - z0.2‖ < ρ → ∃ x : EuclideanSpace ℝ ι, ξ (jP p) = jEL x ∧ ‖x‖ ≤ r0 ∧
          ∀ v, fderiv ℝ (Fre jP Fc) (z0.1 + x, p) (v, 0) = 0) := by
  obtain ⟨u0, p0⟩ := z0
  obtain ⟨B, hBA, hAB, hBinj, hBreal⟩ := exists_inv jP h him hc hpos
  set w0 : (ι → ℂ) × PC := kP jP (u0, p0) with hw0
  have hgrad0 : gradC Fc w0 = 0 := by
    funext j
    rw [hw0, gradC_real jP h him j, hcrit]; simp
  -- neighbourhoods
  obtain ⟨R0, hR0, hRb⟩ : ∃ R0 > 0, ∀ w ∈ ball (u0, p0) R0, AnalyticAt ℂ Fc (kP jP w) ∧
      ∀ᶠ w' in 𝓝 w, (Fc (kP jP w')).im = 0 := by
    have h1 : ∀ᶠ w in 𝓝 (u0, p0), AnalyticAt ℂ Fc (kP jP w) ∧ ∀ᶠ w' in 𝓝 w, (Fc (kP jP w')).im = 0 := by
      filter_upwards [(kP (ι := ι) jP).continuous.continuousAt.eventually h.eventually_analyticAt,
        him.eventually_nhds] with w h1 h2 using ⟨h1, h2⟩
    obtain ⟨R0, hR0, hb⟩ := Metric.eventually_nhds_iff_ball.mp h1
    exact ⟨R0, hR0, hb⟩
  obtain ⟨R1, hR1, hR1b⟩ : ∃ R1 > 0, ∀ w ∈ ball w0 R1, AnalyticAt ℂ Fc w := by
    obtain ⟨R1, hR1, hb⟩ := Metric.eventually_nhds_iff_ball.mp h.eventually_analyticAt
    exact ⟨R1, hR1, hb⟩
  have hgA : AnalyticAt ℂ (gradC Fc) w0 := analyticAt_gradC h
  have hBA' : ∀ y, B ((fderiv ℂ (gradC Fc) w0).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) PC) y) = y := hAB
  obtain ⟨δ1, hδ1, hM⟩ := exists_hess_nbhd hgA B hBA'
  set δ2 : ℝ := min δ1 R1 with hδ2
  have hδ2pos : 0 < δ2 := lt_min hδ1 hR1
  have hKpos : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  set K : ℝ := (Fintype.card ι : ℝ) + 1 with hK
  set r : ℝ := min (r0 / K) (min (R0 / (2 * K)) (δ2 / 2)) with hr
  have hrpos : 0 < r := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hr1 : r ≤ r0 / K := min_le_left _ _
  have hr2 : r ≤ R0 / (2 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ δ2 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hKr : K * r ≤ R0 / 2 := by
    calc K * r ≤ K * (R0 / (2 * K)) := by gcongr
      _ = R0 / 2 := by field_simp
  have hKr0 : K * r ≤ r0 := by
    calc K * r ≤ K * (r0 / K) := by gcongr
      _ = r0 := by field_simp
  have hcardK : (Fintype.card ι : ℝ) ≤ K := by rw [hK]; linarith
  -- the parameter radius
  have hφc : ContinuousAt (fun q : PC => B (gradC Fc (jEL u0, q))) (jP p0) := by
    have h1 : ContinuousAt (gradC Fc) (jEL u0, jP p0) := hgA.continuousAt
    have h2 : ContinuousAt (fun q : PC => (jEL u0, q)) (jP p0) := (continuous_const.prodMk continuous_id).continuousAt
    exact B.continuous.continuousAt.comp (h1.comp h2)
  have hφ0 : B (gradC Fc (jEL u0, jP p0)) = 0 := by
    have : gradC Fc (jEL u0, jP p0) = 0 := hgrad0
    rw [this, map_zero]
  obtain ⟨ρ1, hρ1, hρ1b⟩ := Metric.continuousAt_iff.mp hφc (r / 2) (by positivity)
  set ρ : ℝ := min ρ1 (min (δ2 / 2) (R0 / 2)) with hρ
  have hρpos : 0 < ρ := lt_min hρ1 (lt_min (by positivity) (by positivity))
  have hρ1' : ρ ≤ ρ1 := min_le_left _ _
  have hρ2 : ρ ≤ δ2 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ R0 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hw0' : w0 = (jEL u0, jP p0) := rfl
  have hpt : ∀ (ξ : ι → ℂ) (q : PC), ‖ξ‖ ≤ r → q ∈ ball (jP p0) ρ →
      (jEL u0 + ξ, q) ∈ ball w0 δ2 := by
    intro ξ q hξ hq
    apply mem_ball_prod
    · rw [hw0']; simp only [add_sub_cancel_left]; linarith
    · rw [hw0']; have := mem_ball.mp hq; rw [dist_eq_norm] at this; simp only; linarith
  have hanal : ∀ (ξ : ι → ℂ) (q : PC), ‖ξ‖ ≤ r → q ∈ ball (jP p0) ρ →
      AnalyticAt ℂ (gradC Fc) (jEL u0 + ξ, q) := fun ξ q hξ hq =>
    analyticAt_gradC (hR1b _ (ball_subset_ball (min_le_right _ _) (hpt ξ q hξ hq)))
  set gg : (ι → ℂ) × PC → (ι → ℂ) := fun x => gradC Fc (jEL u0 + x.1, x.2) with hgg
  have hggA : AnalyticOnNhd ℂ gg (closedBall (0 : ι → ℂ) r ×ˢ ball (jP p0) ρ) := by
    intro x hx
    have h1 := hanal x.1 x.2 (mem_closedBall_zero_iff.mp hx.1) hx.2
    have h2 : AnalyticAt ℂ (fun y : (ι → ℂ) × PC => (jEL u0 + y.1, y.2)) x :=
      AnalyticAt.prod (f := fun y : (ι → ℂ) × PC => jEL u0 + y.1) (g := fun y : (ι → ℂ) × PC => y.2)
        (analyticAt_const.add analyticAt_fst) analyticAt_snd
    exact AnalyticAt.comp (g := gradC Fc) (f := fun y : (ι → ℂ) × PC => (jEL u0 + y.1, y.2)) h1 h2
  -- derivative in the first variable
  have hder : ∀ (ξ : ι → ℂ) (q : PC), ‖ξ‖ ≤ r → q ∈ ball (jP p0) ρ →
      HasFDerivAt (fun ξ' : ι → ℂ => ξ' - B (gradC Fc (jEL u0 + ξ', q)))
        (ContinuousLinearMap.id ℂ (ι → ℂ) - B.comp ((fderiv ℂ (gradC Fc) (jEL u0 + ξ, q)).comp
          (ContinuousLinearMap.inl ℂ (ι → ℂ) PC))) ξ := by
    intro ξ q hξ hq
    have h1 := (hanal ξ q hξ hq).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun ξ' : ι → ℂ => ((jEL u0 + ξ', q) : (ι → ℂ) × PC))
        (ContinuousLinearMap.inl ℂ (ι → ℂ) PC) ξ := by
      have h2a : HasFDerivAt (fun ξ' : ι → ℂ => jEL u0 + ξ') (ContinuousLinearMap.id ℂ (ι → ℂ)) ξ :=
        (hasFDerivAt_id (𝕜 := ℂ) ξ).const_add (jEL u0)
      have := h2a.prodMk (hasFDerivAt_const (𝕜 := ℂ) q ξ)
      convert this using 1
      ext y <;> simp
    have h3 : HasFDerivAt (fun ξ' : ι → ℂ => gradC Fc (jEL u0 + ξ', q))
        ((fderiv ℂ (gradC Fc) (jEL u0 + ξ, q)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) PC)) ξ :=
      HasFDerivAt.comp (g := gradC Fc) (f := fun ξ' : ι → ℂ => ((jEL u0 + ξ', q) : (ι → ℂ) × PC)) ξ h1 h2
    exact (hasFDerivAt_id ξ).sub (HasFDerivAt.comp (g := B) (f := fun ξ' : ι → ℂ => gradC Fc (jEL u0 + ξ', q)) ξ
      B.hasFDerivAt h3)
  have hmv : ∀ q ∈ ball (jP p0) ρ, ∀ ξ ∈ closedBall (0 : ι → ℂ) r, ∀ ξ' ∈ closedBall (0 : ι → ℂ) r,
      ‖(ξ - B (gg (ξ, q))) - (ξ' - B (gg (ξ', q)))‖ ≤ 1 / 2 * ‖ξ - ξ'‖ := by
    intro q hq ξ hξ ξ' hξ'
    have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (𝕜 := ℝ) (f := fun ξ' : ι → ℂ => ξ' - B (gradC Fc (jEL u0 + ξ', q)))
      (f' := fun ξ => (ContinuousLinearMap.id ℂ (ι → ℂ) - B.comp ((fderiv ℂ (gradC Fc) (jEL u0 + ξ, q)).comp
          (ContinuousLinearMap.inl ℂ (ι → ℂ) PC))).restrictScalars ℝ)
      (s := closedBall (0 : ι → ℂ) r) (C := 1 / 2)
      (fun x hx => ((hder x q (mem_closedBall_zero_iff.mp hx) hq).restrictScalars ℝ).hasFDerivWithinAt)
      (fun x hx => by
        rw [ContinuousLinearMap.norm_restrictScalars]
        exact hM _ (ball_subset_ball (min_le_left _ _) (hpt x q (mem_closedBall_zero_iff.mp hx) hq)))
      (convex_closedBall _ _) hξ' hξ
    simpa [hgg, norm_sub_rev] using key
  have hmaps : ∀ q ∈ ball (jP p0) ρ, ∀ ξ ∈ closedBall (0 : ι → ℂ) r,
      ξ - B (gg (ξ, q)) ∈ closedBall (0 : ι → ℂ) r := by
    intro q hq ξ hξ
    have h0 : (0 : ι → ℂ) ∈ closedBall (0 : ι → ℂ) r := mem_closedBall_self hrpos.le
    have h1 := hmv q hq ξ hξ 0 h0
    have h2 : ‖B (gradC Fc (jEL u0, q))‖ < r / 2 := by
      have := hρ1b (by rw [mem_ball] at hq; exact lt_of_lt_of_le hq hρ1')
      rw [hφ0, dist_eq_norm, sub_zero] at this
      exact this
    have h3 : gg (0, q) = gradC Fc (jEL u0, q) := by simp [hgg]
    rw [mem_closedBall_zero_iff] at hξ ⊢
    have e2 : ‖0 - B (gg (0, q))‖ = ‖B (gradC Fc (jEL u0, q))‖ := by rw [zero_sub, norm_neg, h3]
    have e3 : ‖ξ - B (gg (ξ, q))‖ ≤ ‖(ξ - B (gg (ξ, q))) - (0 - B (gg (0, q)))‖ + ‖0 - B (gg (0, q))‖ := by
      calc ‖ξ - B (gg (ξ, q))‖ = ‖((ξ - B (gg (ξ, q))) - (0 - B (gg (0, q)))) + (0 - B (gg (0, q)))‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [sub_zero] at h1
    linarith
  obtain ⟨ξs, hξs, hξA⟩ := exists_analytic_zero (g := gg) B hBinj (P := ball (jP p0) ρ)
    Metric.isOpen_ball hrpos.le (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) < 1)
    hggA hmaps (fun q hq ξ hξ ξ' hξ' => hmv q hq ξ hξ ξ' hξ')
  have hballp : ∀ p : PR, ‖p - p0‖ < ρ → jP p ∈ ball (jP p0) ρ := fun p hp => by
    rw [mem_ball, dist_eq_norm, ← map_sub, hjP]; exact hp
  refine ⟨ρ, hρpos, r, hrpos, ξs, hξA, ?_, ?_, ?_⟩
  · have h0 : (0 : ι → ℂ) ∈ closedBall (0 : ι → ℂ) r := mem_closedBall_self hrpos.le
    have hz : gg (0, jP p0) = 0 := by
      have : gg (0, jP p0) = gradC Fc w0 := by simp [hgg, hw0']
      rw [this, hgrad0]
    exact ((hξs (jP p0) (mem_ball_self hρpos)).2.2 0 h0 hz).symm
  · intro q hq
    exact ⟨mem_closedBall_zero_iff.mp (hξs q hq).1, (hξs q hq).2.1⟩
  · intro p hp
    have hq := hballp p hp
    -- real points are in the good ball
    have hgood : ∀ x : EuclideanSpace ℝ ι, ‖jEL x‖ ≤ r → (u0 + x, p) ∈ ball (u0, p0) R0 := by
      intro x hx
      apply mem_ball_prod
      · simp only [add_sub_cancel_left]
        have := norm_le_card_mul x
        have h2 : (Fintype.card ι : ℝ) * ‖jEL x‖ ≤ K * r := by gcongr
        linarith
      · simp only; linarith
    have hgrad : ∀ x : EuclideanSpace ℝ ι, ‖jEL x‖ ≤ r →
        gg (jEL x, jP p) = jEL (WithLp.toLp 2 fun j => fderiv ℝ (Fre jP Fc) (u0 + x, p)
          (EuclideanSpace.single j (1:ℝ), 0)) := by
      intro x hx
      obtain ⟨hA, him'⟩ := hRb _ (hgood x hx)
      funext j
      have := gradC_real jP hA him' j
      simp only [hgg, kP_apply, map_add] at this ⊢
      rw [this]; rfl
    have hSreal : ∀ x : EuclideanSpace ℝ ι, ‖jEL x‖ ≤ r →
        ∃ x', jEL x - B (gg (jEL x, jP p)) = jEL x' := by
      intro x hx
      obtain ⟨x2, hx2⟩ := hBreal (WithLp.toLp 2 fun j => fderiv ℝ (Fre jP Fc) (u0 + x, p)
          (EuclideanSpace.single j (1:ℝ), 0))
      refine ⟨x - x2, ?_⟩
      rw [hgrad x hx, hx2, map_sub]
    obtain ⟨ξf, hξfmem, hfix, -, hiter⟩ := Balaban.Analysis.exists_unique_fixedPoint_closedBall
      (S := fun ξ => ξ - B (gg (ξ, jP p))) hrpos.le (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1/2 : ℝ) < 1)
      (fun ξ hξ => hmaps (jP p) hq ξ hξ) (fun ξ hξ ξ' hξ' => hmv (jP p) hq ξ hξ ξ' hξ')
    have hreal_iter : ∀ n : ℕ, ∃ x : EuclideanSpace ℝ ι,
        (fun ξ => ξ - B (gg (ξ, jP p)))^[n] 0 = jEL x := by
      intro n
      induction n with
      | zero => exact ⟨0, by simp⟩
      | succ n ih =>
        obtain ⟨x, hx⟩ := ih
        have hn := (hiter n).1
        rw [hx] at hn
        obtain ⟨x', hx'⟩ := hSreal x (mem_closedBall_zero_iff.mp hn)
        refine ⟨x', ?_⟩
        rw [Function.iterate_succ_apply', hx]
        exact hx'
    have hclosed : IsClosed (Set.range (jEL (ι := ι))) := by
      have : LinearMap.ker (jEL (ι := ι) : EuclideanSpace ℝ ι →ₗ[ℝ] (ι → ℂ)) = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro x hx
        ext j
        have := congrFun hx j
        simpa [jEL_apply] using this
      exact (LinearMap.isClosedEmbedding_of_injective this).isClosed_range
    have htend : Filter.Tendsto (fun n : ℕ => (fun ξ => ξ - B (gg (ξ, jP p)))^[n] 0) Filter.atTop (𝓝 ξf) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hiter n).2) ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).mul_const r
      simpa using this
    obtain ⟨xf, hxf⟩ : ξf ∈ Set.range (jEL (ι := ι)) :=
      hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall fun n => by
        obtain ⟨x, hx⟩ := hreal_iter n; exact ⟨x, hx.symm⟩)
    have hggz : gg (ξf, jP p) = 0 := by
      have : B (gg (ξf, jP p)) = 0 := by
        have := hfix
        beta_reduce at this
        exact sub_eq_self.mp this
      exact hBinj (by rw [this, map_zero])
    have hxfr : ‖jEL xf‖ ≤ r := by rw [hxf]; exact mem_closedBall_zero_iff.mp hξfmem
    have hξseq : ξs (jP p) = jEL xf := by
      rw [hxf]
      exact ((hξs (jP p) hq).2.2 ξf hξfmem hggz).symm
    refine ⟨xf, hξseq, ?_, ?_⟩
    · have := norm_le_card_mul xf
      have h2 : (Fintype.card ι : ℝ) * ‖jEL xf‖ ≤ K * r := by gcongr
      linarith
    · intro v
      obtain ⟨hA, him'⟩ := hRb _ (hgood xf hxfr)
      have hz0 : gradC Fc (kP jP (u0 + xf, p)) = 0 := by
        have : gg (ξf, jP p) = gradC Fc (kP jP (u0 + xf, p)) := by
          simp only [hgg, kP_apply, map_add, hxf]
        rw [← this]; exact hggz
      have hj : ∀ j, fderiv ℝ (Fre jP Fc) (u0 + xf, p) (EuclideanSpace.single j (1:ℝ), 0) = 0 := by
        intro j
        have := congrFun hz0 j
        rw [gradC_real jP hA him' j, Pi.zero_apply] at this
        exact_mod_cast this
      let ℓ : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
        (fderiv ℝ (Fre jP Fc) (u0 + xf, p)).comp (ContinuousLinearMap.inl ℝ _ PR)
      have := clm_expand ℓ v
      simpa [ℓ, hj] using this

end Balaban.LargeField.RealCrit
