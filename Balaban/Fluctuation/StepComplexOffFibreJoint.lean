/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreIntegrand

/-!
# Covariance and critical interaction in the raw joint representation
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Multiscale
  Balaban.Localization Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  (H : StepSettingH S)
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- The determinant of the joint covariance square root is the exponential of its principal
trace branch at an arbitrary block datum. -/
theorem det_Mx_eq_trace
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') :
    (Jr.Mx (rawOf H.D')).det = Complex.exp
      (-(1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N,
        (decLog S.G' S.a S.a₁ S.ν (Jr.F₀ (rawOf H.D')).2 (fun _ => 1)
          (svec S.G' (Jr.F₀ (rawOf H.D')).1) (unitQ S.G') (unitP S.G'))
            (y, i) (y, i)) := by
  rw [Jr.Mx_eq H.D' hD, Jr.F₀_eq H.D' hD]
  exact H.det_hatCovSqrt_of_chart hC hMX hdm hα hsm hD

/-- The joint interaction vanishes at the critical old spin for any external field. -/
theorem VJ_zero
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D') :
    Jr.VJ (rawOf H.D', 0) = 0 := by
  have hD' : InUnionDomainC S.G' (bgC0 d L N) (thm73C1 d L N) S.ν H.D' :=
    (isDecBg_one_of_xiCData hC hD).2.mono
      ((hc7.trans (thm73C3_le_thm73C2 d L N)).trans (thm73C2_le_thm73C1 d L N))
  rw [Jr.VJ_dataUCH H hD Jr.zero_le_pp]
  have hz : S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (0 : S.EC) = 0 := by
    unfold StepSetting.hatField
    rw [Matrix.mulVec_zero, smul_zero]
  rw [hz, add_zero]
  exact H.VkC_psi0C ha₁ hC.HBp hD'

end Balaban.Fluctuation.StepSetting.JointRep
