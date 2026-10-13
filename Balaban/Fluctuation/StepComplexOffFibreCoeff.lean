/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreJoint
public import Balaban.Fluctuation.StepComplexOutAnalytic

/-!
# The local direction of the raw energy coefficient

The inverse covariance square root sends a masked physical fluctuation to the corresponding
hat direction at every block datum in the complex chart.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  (H : StepSettingH S) {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- On the chart, applying the covariance square root to the local hat direction recovers
the masked physical fluctuation. -/
theorem Mx_mulVec_inv_mask_of_chart
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E) :
    Jr.Mx (rawOf H.D') *ᵥ
        ((Jr.Mx (rawOf H.D'))⁻¹ *ᵥ
          S.maskUC z (Jr.Mx (rawOf H.D') *ᵥ yhat x)) =
      S.maskUC z (Jr.Mx (rawOf H.D') *ᵥ yhat x) := by
  have hdet : IsUnit (Jr.Mx (rawOf H.D')).det := by
    rw [Jr.det_Mx_eq_trace H hC hMX hdm hα hsm hX]
    exact (Complex.exp_ne_zero _).isUnit
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The local hat direction produces the masked shift after the covariance substitution. -/
theorem hatField_inv_mask_of_chart
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (x : S.E) :
    S.hatField (Jr.Mx (rawOf H.D'))
        ((Jr.Mx (rawOf H.D'))⁻¹ *ᵥ
          S.maskUC z (Jr.Mx (rawOf H.D') *ᵥ yhat x)) =
      S.maskUC z (S.hatField (Jr.Mx (rawOf H.D')) (yhat x)) := by
  unfold StepSetting.hatField
  rw [Jr.Mx_mulVec_inv_mask_of_chart H hC hMX hdm hα hsm hX z x]
  funext q
  by_cases hq : q.1 ∈ S.blockU z
  · simp [StepSetting.maskUC, hq]
  · simp [StepSetting.maskUC, hq]

end Balaban.Fluctuation.StepSetting.JointRep
