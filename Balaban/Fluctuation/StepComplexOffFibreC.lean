/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepSettingH
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complex step identities at an arbitrary block datum

The old spin inherits the external field of the block datum. The formulas below use the
existing covariance and background objects evaluated at that datum.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale
  Balaban.Localization Balaban.SmallField Finset Matrix

namespace StepSettingH

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (H : StepSettingH S)

/-- The interaction vanishes at the critical old spin for an arbitrary external field. -/
theorem VkC_psi0C (ha₁ : 0 < S.a₁) (HB : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hD : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν H.D') :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' (H.dataUCH ψ₀))
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (H.dataUCH ψ₀) -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) = 0 := by
  dsimp only
  obtain ⟨-, -, hfield, -⟩ :=
    criticalPoint_complex ha₁ S.hG S.hG' (le_refl (k + 1)) HB HB H.D' hD
  rw [H.dataUCH_psi0C]
  have htan : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
      (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D') = 0 := by
    funext z i
    unfold compTangent
    exact sub_self _
  rw [htan, hfield, sub_self]
  exact interactionV_zero' _ _ _ _ _

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- The complex old spin on the hat ray lies in the small-solution domain, with the ray margin,
for an arbitrary block datum in the chart. -/
theorem dataUCH_hatRay_inUnionDomainC_plus
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 ≤ S.β) {pp : ℝ} (hpp : 0 < pp)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun p => B.Ψ (unitRep (G' := S.G') p.1) p.2
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (H.dataUCH (ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D')
        ((q.1 : ℂ) • yhat q.2))) := by
  dsimp only
  refine inUnionDomainC_of_tangent_hatLift hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR
    hMX hdm hα hsm _ hpp.le (by rwa [S.norm_betaU_rpow hβ])
    (ψh := (q.1 : ℂ) • yhat q.2) (fun p => ?_) hD
    (fun z i => H.dataUCH_h _ z i) ?_
  · have h1 : ‖((q.2 p.1 p.2 : ℝ) : ℂ)‖ ≤ ‖q.2‖ := by
      rw [Complex.norm_real]
      exact (PiLp.norm_apply_le (q.2 p.1) p.2).trans (norm_le_pi_norm q.2 p.1)
    show ‖(q.1 : ℂ) * ((q.2 p.1 p.2 : ℝ) : ℂ)‖ ≤ pp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans hq.le
  · rw [H.compTangent_dataUCH]
    simp only [add_sub_cancel_left]
    rfl

/-- The old spin on the fluctuation support lies in the small-solution domain. -/
theorem dataUCH_hatRay_inUnionDomainC
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 ≤ S.β) (hp₁ : 0 < S.p₁)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun p => B.Ψ (unitRep (G' := S.G') p.1) p.2
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (H.dataUCH (ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D')
        ((s : ℂ) • yhat x))) := by
  dsimp only
  refine inUnionDomainC_of_tangent_hatLift hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR
    hMX hdm hα hsm _ hp₁.le (by rwa [S.norm_betaU_rpow hβ])
    (ψh := (s : ℂ) • yhat x) (S.norm_smul_yhat_le hp₁ hs hx) hD
    (fun z i => H.dataUCH_h _ z i) ?_
  rw [H.compTangent_dataUCH]
  simp only [add_sub_cancel_left]
  rfl

/-- The pointwise covariance hypotheses hold at any datum of the complex chart. -/
theorem covData_of_chart
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') :
    (∀ x, 0 ≤ x → XData S.G' S.a S.a₁ S.ν x
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') 0 (fun _ => 1)) ∧
    IsConstraintField S.G' δc
      (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) ∧
    0 ≤ δc ∧ δc ^ 2 * smallConstX d L 0 ≤ 1 / 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := xData_zero_of_xiCData hC S.hk1 hMX hdm hα hsm hD
  have hb : barField S.G' H.D'.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') := by
    funext x i
    exact barField_eq_svec S.hG' _ _ x i
  rw [hb] at h2
  exact ⟨h1, h2, h3, h4⟩

/-- The raw covariance square root conjugates its quadratic operator to the identity. -/
theorem covSqrt_T_mul_of_chart
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') :
    let M := hatCovSqrt S.G' S.a₁ S.ν H.D'
    let A := covOp S.G' S.a S.a₁ S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
      (unitQ S.G') (unitP S.G')
    Mᵀ * A * M = 1 := by
  dsimp only
  obtain ⟨hfam, hφ, hδ, hsm0⟩ := H.covData_of_chart hC hMX hdm hα hsm hD
  have hb : barField S.G' H.D'.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') := by
    funext x i
    exact barField_eq_svec S.hG' _ _ x i
  have hM : hatCovSqrt S.G' S.a₁ S.ν H.D' = sqrtMat
      (covOp S.G' S.a S.a₁ S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
        (unitQ S.G') (unitP S.G')) := by
    unfold hatCovSqrt
    rw [hb]
    exact decCovSqrt_one_eq_sqrtMat hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G'))
  rw [hM]
  exact sqrtMat_transpose_mul
    (resOK_covOp hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G')))
    (covOp_transpose (xH0_transpose_of_level S.hG S.hG' S.a S.ν _) unitP_transpose)

/-- The determinant of the raw covariance square root uses the principal logarithm branch. -/
theorem det_hatCovSqrt_of_chart
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') :
    (hatCovSqrt S.G' S.a₁ S.ν H.D').det = Complex.exp
      (-(1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N,
        (decLog S.G' S.a S.a₁ S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') (fun _ => 1)
          (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
          (unitQ S.G') (unitP S.G')) (y, i) (y, i)) := by
  obtain ⟨hfam, hφ, hδ, hsm0⟩ := H.covData_of_chart hC hMX hdm hα hsm hD
  have hb : barField S.G' H.D'.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') := by
    funext x i
    exact barField_eq_svec S.hG' _ _ x i
  unfold hatCovSqrt
  rw [hb, decCovSqrt_one_eq_sqrtMat hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G')),
    det_sqrtMat (resOK_covOp hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G'))),
    ← decLog_one_eq_logMat hfam hφ hδ hsm0 (isUnitLatticeB_unit (G := S.G'))]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_prod_type]

/-- The Gaussian quadratic on the raw hat shift is the Euclidean quadratic of the fluctuation. -/
theorem quad_hatField_of_chart
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') (x : S.E) :
    let M := hatCovSqrt S.G' S.a₁ S.ν H.D'
    let A := covOp S.G' S.a S.a₁ S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
      (unitQ S.G') (unitP S.G')
    let shift := S.hatField M (yhat x)
    shift ⬝ᵥ (A *ᵥ shift) =
      (((S.betaU ^ (-(1 / 2 : ℝ))) ^ 2 * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) := by
  dsimp only
  have hT := H.covSqrt_T_mul_of_chart hC hMX hdm hα hsm hD
  have key : (hatCovSqrt S.G' S.a₁ S.ν H.D' *ᵥ yhat x) ⬝ᵥ
        (covOp S.G' S.a S.a₁ S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
          (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
          (unitQ S.G') (unitP S.G') *ᵥ
            (hatCovSqrt S.G' S.a₁ S.ν H.D' *ᵥ yhat x)) = yhat x ⬝ᵥ yhat x := by
    calc
      _ = ((hatCovSqrt S.G' S.a₁ S.ν H.D')ᵀ *ᵥ
          (covOp S.G' S.a S.a₁ S.ν
            (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
            (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
            (unitQ S.G') (unitP S.G') *ᵥ
              (hatCovSqrt S.G' S.a₁ S.ν H.D' *ᵥ yhat x))) ⬝ᵥ yhat x := by
              rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      _ = (((hatCovSqrt S.G' S.a₁ S.ν H.D')ᵀ *
          covOp S.G' S.a S.a₁ S.ν
            (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
            (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
            (unitQ S.G') (unitP S.G') *
          hatCovSqrt S.G' S.a₁ S.ν H.D') *ᵥ yhat x) ⬝ᵥ yhat x := by
            simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = yhat x ⬝ᵥ yhat x := by rw [hT, Matrix.one_mulVec]
  have hshift : S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x) =
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        (hatCovSqrt S.G' S.a₁ S.ν H.D' *ᵥ yhat x) := rfl
  rw [hshift, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, key, S.yhat_dot]
  simp only [smul_eq_mul]
  push_cast
  ring

end StepSettingH

end Balaban.Fluctuation
