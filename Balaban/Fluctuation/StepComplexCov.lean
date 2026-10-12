/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOut
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The covariance of the step at a complex block datum (FLUCTUATION.md §2.4, Lemma 2.4 (c))

The Gaussian part of Proposition 2.6 at a real datum uses that `C^{(k)1/2}` is the positive square
root of the positive definite `𝒜⁻¹` (`covSqrt_T_mul`, `abs_det_K`).  At a complex datum `𝒜 = covAC`
is not Hermitian; it is complex symmetric, `(x + 𝒜)` is invertible for `x ≥ 0` (`ResOK`), and
`C^{(k)1/2} = sqrtMat 𝒜`, `𝕃 = logMat 𝒜` are the principal square root and logarithm
(`DecoupledCovPrincipal`).  This file proves the two facts the complex step needs:

* matrices: `sqrtMat_transpose`, `sqrtMat_eq_exp_logMat` (`sqrtMat A = exp (-½ logMat A)`),
  `det_sqrtMat` (`det (sqrtMat A) = exp (-½ tr (logMat A))`), `sqrtMat_transpose_mul`
  (`(sqrtMat A)ᵀ A (sqrtMat A) = 1` for a symmetric `A`), for every `A` with `ResOK A`, by
  `principal_identity` (analytic continuation in the matrix from the positive definite ones);
* `covOp_transpose`: `𝒜ᵀ = 𝒜` for every (complex) background;
* `StepSetting.covSqrtC_T_mul` (`C^{1/2 ᵀ} 𝒜 C^{1/2} = 1`), `StepSetting.det_covSqrtC`
  (`det C^{(k)1/2} = exp (½ log det C^{(k)})` with the analytic `halfLogDetCC`), under the pointwise
  premises of Theorem I-4c at the complex background;
* `xData_zero_of_xiCData`, `StepSetting.covData_of_chart`: these premises hold on the complex chart
  of RAY-CHART §1 (`FlCore`, `XiCData`, the margins of the covariance chart).
-/

@[expose] public section

namespace Balaban.Localization

open scoped Matrix.Norms.L2Operator ComplexOrder
open Matrix MeasureTheory Set Balaban.Multiscale

section Principal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The resolvent square root commutes with the transpose. -/
theorem sqrtMat_transpose (A : Matrix ι ι ℂ) : (sqrtMat A)ᵀ = sqrtMat Aᵀ := by
  have h : ∀ x : ℝ, ((x : ℂ) • (1 : Matrix ι ι ℂ) + Aᵀ)⁻¹ =
      (((x : ℂ) • (1 : Matrix ι ι ℂ) + A)⁻¹)ᵀ := by
    intro x
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_add, Matrix.transpose_smul,
      Matrix.transpose_one]
  unfold sqrtMat
  rw [Matrix.transpose_smul]
  congr 1
  ext p q
  simp only [Matrix.transpose_apply, intMat, Matrix.smul_apply, h]

/-- For a positive definite matrix, `A^{-1/2} = exp (-½ log A)`. -/
theorem sqrtMat_eq_exp_of_posDef {A : Matrix ι ι ℂ} (hP : A.PosDef) :
    sqrtMat A = NormedSpace.exp ((-(1 / 2) : ℂ) • logMat A) := by
  have hH := hP.isHermitian
  have hs : sqrtMat A = invSqrtMat hP := resolvent_sqrt_eq hP
  rw [hs, logMat_posDef hP]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hUU
  have hunit : IsUnit U := IsUnit.of_mul_eq_one (star U) hUU
  have key : (-(1 / 2) : ℂ) • specFun hH (fun t => (Real.log t : ℂ)) =
      U * Matrix.diagonal (fun i => (-(1 / 2) : ℂ) * ((Real.log (hH.eigenvalues i) : ℝ) : ℂ)) *
        U⁻¹ := by
    rw [← specFun_smul]
    unfold specFun; rw [hUinv]
  have hD : (NormedSpace.exp
      (fun i => (-(1 / 2) : ℂ) * ((Real.log (hH.eigenvalues i) : ℝ) : ℂ)) : ι → ℂ) =
      fun i => (((Real.sqrt (hH.eigenvalues i))⁻¹ : ℝ) : ℂ) := by
    funext i
    have hpos := hP.eigenvalues_pos i
    have e : (-(1 / 2) : ℂ) * ((Real.log (hH.eigenvalues i) : ℝ) : ℂ) =
        ((-(1 / 2 * Real.log (hH.eigenvalues i)) : ℝ) : ℂ) := by push_cast; ring
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, e, ← Complex.ofReal_exp, Real.exp_neg,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
    congr 3
    ring
  rw [key, Matrix.exp_conj U _ hunit, Matrix.exp_diagonal, hD]
  unfold invSqrtMat specFun
  rw [hUinv]

/-- **`sqrtMat A = exp (-½ logMat A)`** for every `A` with `ResOK A`: the principal inverse square
root is the exponential of minus one half of the principal logarithm. -/
theorem sqrtMat_eq_exp_logMat [Nonempty ι] {A : Matrix ι ι ℂ} (hA : ResOK A) :
    sqrtMat A = NormedSpace.exp ((-(1 / 2) : ℂ) • logMat A) := by
  have h := principal_identity
    (fun A => sqrtMat A - NormedSpace.exp ((-(1 / 2) : ℂ) • logMat A)) ?_
    (fun A hP => by rw [sqrtMat_eq_exp_of_posDef hP, sub_self]) hA
  · exact sub_eq_zero.1 h
  · intro M D hD hRes hM z hz
    have hS : RectAt (fun w => sqrtMat (M w)) z := fun p q =>
      analyticOnNhd_sqrtMat_fam hD hRes hM p q z hz
    have hL : RectAt (fun w => logMat (M w)) z := fun p q =>
      analyticOnNhd_logMat_fam hD hRes hM p q z hz
    have hLan : AnalyticAt ℂ (fun w => (-(1 / 2) : ℂ) • logMat (M w)) z := by
      show AnalyticAt ℂ ((-(1 / 2) : ℂ) • fun w => logMat (M w)) z
      exact (analyticAt_of_rectAt' hL).const_smul
    have hE : AnalyticAt ℂ (fun w => NormedSpace.exp ((-(1 / 2) : ℂ) • logMat (M w))) z :=
      (NormedSpace.exp_analytic _).comp hLan
    exact hS.sub (rectAt_of_analyticAt' hE)

/-- **`det (sqrtMat A) = exp (-½ tr (logMat A))`** for every `A` with `ResOK A`. -/
theorem det_sqrtMat {A : Matrix ι ι ℂ} (hA : ResOK A) :
    (sqrtMat A).det = Complex.exp (-(1 / 2) * (logMat A).trace) := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [Matrix.det_isEmpty, Matrix.trace]
  · rw [sqrtMat_eq_exp_logMat hA, det_exp_eq_exp_trace, Matrix.trace_smul, smul_eq_mul]

/-- **`(sqrtMat A)ᵀ A (sqrtMat A) = 1`** for a complex symmetric `A` with `ResOK A`. -/
theorem sqrtMat_transpose_mul {A : Matrix ι ι ℂ} (hA : ResOK A) (hT : Aᵀ = A) :
    (sqrtMat A)ᵀ * A * sqrtMat A = 1 := by
  rcases isEmpty_or_nonempty ι with h | h
  · exact Matrix.subsingleton_of_empty_left.elim _ _
  · have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 (by simpa using hA 0 le_rfl)
    rw [sqrtMat_transpose, hT, sqrtMat_commute hA, Matrix.mul_assoc, sqrtMat_mul_self hA,
      Matrix.mul_nonsing_inv _ hu]

end Principal

section Symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The constraint form `φ · A φ` of a complex symmetric `A` is complex symmetric. -/
theorem constraintForm_transpose {A : Matrix ι ι ℂ} (hA : Aᵀ = A) (φ : ι → Fin N → ℂ) :
    (constraintForm A φ)ᵀ = constraintForm A φ := by
  unfold constraintForm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Balaban.Fluctuation.liftOp_transpose', hA, Matrix.mul_assoc]

/-- The constrained operator `Π` of a complex symmetric `A` is complex symmetric. -/
theorem constrainedOp_transpose {A : Matrix ι ι ℂ} (hA : Aᵀ = A) (φ : ι → Fin N → ℂ) :
    (constrainedOp A φ)ᵀ = constrainedOp A φ := by
  unfold constrainedOp
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Balaban.Fluctuation.liftOp_transpose', hA, Matrix.transpose_nonsing_inv,
    constraintForm_transpose hA, Matrix.mul_assoc]

end Symm

section CovSymm

open Balaban Balaban.Background Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT ν : ℝ}
  {α : G.Ω 1 → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
  {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

omit [Fintype κι] in
/-- **`𝒜 = a L⁻² Q*Q + Δ^{(k)}` is complex symmetric** for every (complex) background, when the
Dirichlet operator `H₀` and `P` are. -/
theorem covOp_transpose (hH : (xH0 G a ν α)ᵀ = xH0 G a ν α) (hP : Pᵀ = P) :
    (covOp G a aT ν α φ Q P)ᵀ = covOp G a aT ν α φ Q P := by
  have hGi : ((xH0 G a ν α)⁻¹)ᵀ = (xH0 G a ν α)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hH]
  unfold covOp
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_transpose,
    Balaban.Fluctuation.liftOp_transpose', hP, hGi, constrainedOp_transpose hGi, Matrix.mul_assoc]

/-- **The Dirichlet operator `H₀` of the level `k + 1` is complex symmetric**: it is `H_k` of
Lemma 2.3 relabelled (`opHk_eq_xH0`), and `H_D(α)` is symmetric. -/
theorem xH0_transpose_of_level {G G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ) :
    (xH0 G' a ν α₁)ᵀ = xH0 G' a ν α₁ := by
  have h := Balaban.Fluctuation.opHk_eq_xH0 hG hG' a ν α₁
  have ht : (Balaban.Fluctuation.opHk (hG.precedes hG' (le_refl (k + 1))) a ν α₁)ᵀ =
      Balaban.Fluctuation.opHk (hG.precedes hG' (le_refl (k + 1))) a ν α₁ :=
    Balaban.Fluctuation.dirichletOperator_transpose _ _ _
  ext x y
  have h1 := congrFun (congrFun ht ((Balaban.Fluctuation.levelEquiv hG hG').symm x))
    ((Balaban.Fluctuation.levelEquiv hG hG').symm y)
  rw [h] at h1
  simpa using h1

end CovSymm

section Chart

open Balaban Balaban.Background Balaban.SmallField Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The smallness constant of Theorem I-4c is increasing in the polydisc parameter `κ`. -/
theorem smallConstX_zero_le (d L : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    smallConstX d L 0 ≤ smallConstX d L κ := by
  have h1 := commXConst_nonneg d L
  have h2 : 0 ≤ gradConstX d + valConstX d := by unfold gradConstX valConstX; positivity
  have h3 : Real.exp ((N0 d L : ℝ) * 0) ≤ Real.exp ((N0 d L : ℝ) * κ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hκ (Nat.cast_nonneg _))
  unfold smallConstX kConstX
  gcongr

/-- **The pointwise premises of Theorem I-4c hold at the complex background of a datum of the
chart** (RAY-CHART §1): for `D ∈ Ξ^c(𝔹_{k+1}; 1, ε)` under `FlCore` and the margins of the covariance
chart, the multiplier `bgMultC D` is admissible for every `x ≥ 0` at `s ≡ 1` (`XData … 0 1`), and
the field `φ̄ = barField` of `bgFieldC D` is a constraint field of parameter `δc` with
`δc² smallConstX(0) ≤ ¼`.  These are the premises of `decCovSqrt_one_eq_sqrtMat`,
`decLog_one_eq_logMat`, `resOK_covOp` (stated at `κ = 0`), obtained from the membership in `DecDom`
(`decDom_of_isDecBg`) at the `κ` of the chart. -/
theorem xData_zero_of_xiCData (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    (∀ x, 0 ≤ x → XData Gp (compWeight L a₁) a₁ ν x
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) 0 (fun _ => 1)) ∧
      IsConstraintField Gp δc
        (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D)) ∧
      0 ≤ δc ∧ δc ^ 2 * smallConstX d L 0 ≤ 1 / 4 := by
  obtain ⟨hI, -⟩ := isDecBg_one_of_xiCData hC hD
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using hE1
  have hmem := decDom_of_isDecBg hC hs hD hI hdm hα
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have hε := hC.eps_pos
      have hc1 := one_le_xiC1 d
      have hδ0 : 0 < xiC1 d * eps := by positivity
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hbig : cstarX d L * Real.exp (N0 d L * 0) ≤ (L : ℝ) ^ m₁ := by
    refine le_trans ?_ hMX
    have h0 := (cstarX_pos d L).le
    have hκ := hC.hκ.le
    have h3 : Real.exp ((N0 d L : ℝ) * 0) ≤ Real.exp ((N0 d L : ℝ) * κ) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hκ (Nat.cast_nonneg _))
    exact mul_le_mul_of_nonneg_left h3 h0
  refine ⟨fun x hx => ⟨hX, fun w => (hmem.2.2 w).le, hx, le_rfl, hbig, fun P => by simp⟩,
    hmem.2.1.toIsConstraintField, hδc, ?_⟩
  exact (mul_le_mul_of_nonneg_left (smallConstX_zero_le d L hC.hκ.le) (sq_nonneg δc)).trans hsm

end Chart

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **`𝒜` of the complex step is complex symmetric**, at every datum. -/
theorem covAC_transpose : S.covACᵀ = S.covAC :=
  covOp_transpose (xH0_transpose_of_level S.hG S.hG' S.a S.ν _) unitP_transpose

section Pointwise

variable {δc : ℝ}
  (hfamC : ∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x
    (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') 0 (fun _ => 1))
  (hφC : IsConstraintField S.G' δc (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')))
  (hδc : 0 ≤ δc) (hsm0 : δc ^ 2 * smallConstX d L 0 ≤ 1 / 4)

include hfamC hφC hδc hsm0 in
/-- `x + 𝒜` is invertible for every `x ≥ 0` at a complex datum (Theorem I-4c (iv)). -/
theorem resOK_covAC : ResOK S.covAC :=
  resOK_covOp hfamC hφC hδc hsm0 (isUnitLatticeB_unit (G := S.G'))

include hfamC hφC hδc hsm0 in
/-- `C^{(k)1/2}` of the complex step is the principal inverse square root of `𝒜`. -/
theorem covSqrtC_eq_sqrtMat : S.covSqrtC = sqrtMat S.covAC :=
  decCovSqrt_one_eq_sqrtMat hfamC hφC hδc hsm0 (isUnitLatticeB_unit (G := S.G'))

include hfamC hφC hδc hsm0 in
/-- `𝕃` of the complex step is the principal logarithm of `𝒜`. -/
theorem logAC_eq_logMat : S.logAC = logMat S.covAC :=
  decLog_one_eq_logMat hfamC hφC hδc hsm0 (isUnitLatticeB_unit (G := S.G'))

include hfamC hφC hδc hsm0 in
/-- `C^{(k)1/2}` of the complex step is complex symmetric. -/
theorem covSqrtC_transpose : S.covSqrtCᵀ = S.covSqrtC := by
  rw [S.covSqrtC_eq_sqrtMat hfamC hφC hδc hsm0, sqrtMat_transpose, S.covAC_transpose]

include hfamC hφC hδc hsm0 in
/-- **`C^{1/2 ᵀ} 𝒜 C^{1/2} = 1` at a complex datum** (Lemma 2.4 (c); the complex form of
`covSqrt_T_mul`): the Gaussian part of (2.6) after the substitution (2.7). -/
theorem covSqrtC_T_mul : S.covSqrtCᵀ * S.covAC * S.covSqrtC = 1 := by
  rw [S.covSqrtC_eq_sqrtMat hfamC hφC hδc hsm0]
  exact sqrtMat_transpose_mul (S.resOK_covAC hfamC hφC hδc hsm0) S.covAC_transpose

include hfamC hφC hδc hsm0 in
/-- **`det C^{(k)1/2} = exp (½ log det C^{(k)})` at a complex datum** (Lemma 2.4 (c), (2.7); the
complex form of `abs_det_K`), with the analytic `½ log det C^{(k)} = -½ ∑_y tr 𝕃(y,y)`
(`halfLogDetCC`): the Jacobian of the substitution (2.7). -/
theorem det_covSqrtC : S.covSqrtC.det = Complex.exp S.halfLogDetCC := by
  rw [S.covSqrtC_eq_sqrtMat hfamC hφC hδc hsm0, det_sqrtMat (S.resOK_covAC hfamC hφC hδc hsm0),
    ← S.logAC_eq_logMat hfamC hφC hδc hsm0]
  unfold halfLogDetCC
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_prod_type]

include hfamC hφC hδc hsm0 in
/-- `exp (2 · ½ log det C^{(k)}) = det C^{(k)}` at a complex datum: `halfLogDetCC` is one half of a
logarithm of the determinant of `C^{(k)} = 𝒜⁻¹` (`lemma24_c_logdet_complex`). -/
theorem exp_two_halfLogDetCC : Complex.exp (2 * S.halfLogDetCC) = (S.covAC)⁻¹.det := by
  have h := (lemma24_c_logdet_complex hfamC hφC hδc hsm0).2
  unfold covAC
  rw [h]
  unfold halfLogDetCC logAC
  congr 1
  ring

end Pointwise

section FromChart

variable {ϱm : ℝ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
  (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')

include hC hMX hdm hα hsm hD in
/-- **The pointwise premises of Theorem I-4c at the complex background of the step**, for a
(complex) block datum of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` under `FlCore` and the margins of the
covariance chart. -/
theorem covData_of_chart :
    (∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x
        (bgMultC S.G' S.a S.ν (bgC0 d L N) S.D') 0 (fun _ => 1)) ∧
      IsConstraintField S.G' δc (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D')) ∧
      0 ≤ δc ∧ δc ^ 2 * smallConstX d L 0 ≤ 1 / 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := xData_zero_of_xiCData hC S.hk1 hMX hdm hα hsm hD
  have hb : barField S.G' S.D'.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') := by
    funext x i
    exact barField_eq_svec S.hG' _ _ x i
  rw [hb] at h2
  exact ⟨h1, h2, h3, h4⟩

include hC hMX hdm hα hsm hD in
/-- **`C^{1/2 ᵀ} 𝒜 C^{1/2} = 1` on the complex chart.** -/
theorem covSqrtC_T_mul_of_chart : S.covSqrtCᵀ * S.covAC * S.covSqrtC = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := S.covData_of_chart hC hMX hdm hα hsm hD
  exact S.covSqrtC_T_mul h1 h2 h3 h4

include hC hMX hdm hα hsm hD in
/-- **`det C^{(k)1/2} = exp (½ log det C^{(k)})` on the complex chart**, with the analytic
`halfLogDetCC`. -/
theorem det_covSqrtC_of_chart : S.covSqrtC.det = Complex.exp S.halfLogDetCC := by
  obtain ⟨h1, h2, h3, h4⟩ := S.covData_of_chart hC hMX hdm hα hsm hD
  exact S.det_covSqrtC h1 h2 h3 h4

end FromChart

end StepSetting

end Balaban.Fluctuation
