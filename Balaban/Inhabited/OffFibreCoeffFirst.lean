/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreE1Loc

/-!
# First free-datum coefficient value leaf

The derivative in the local first-energy integrand is evaluated on the composed old datum
carrying the incoming external field. This identifies the raw derivative that the marked
expansion must reproduce at every chart datum.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Matrix Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)

/-- The local raw derivative at a free datum is the derivative of the composed old action
in the masked hat direction. -/
theorem e1_raw_masked_deriv_dataUCH
    (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hlt : S.p₁ < pp)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : S.E) (hx : ‖x‖ < S.p₁) :
    let H := S.withDatumH D
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let Dpath := fun w : S.EC =>
      H.dataUCH (ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) w)
    let Dcrit := Dpath 0
    (fderiv ℂ (fun w : S.EC => Jr.W1 C (rawOf D, w))
      ((s : ℂ) • yhat x))
      ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
    (fderiv ℂ (fun w : S.EC =>
      -(S.β : ℂ) * interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D)
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D (Dpath w))
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (Dpath w) -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) D)) +
      (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (Dpath w) -
        EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) Dcrit))
      ((s : ℂ) • yhat x))
      ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) := by
  have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hu : ‖(s : ℂ) • yhat x‖ < pp := by
    calc
      ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := norm_smul_yhat_le (S := S) s x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ < pp := by simpa using hx.trans hlt
  exact Jr.fderiv_W1_dataUCH C (S.withDatumH D) hX hu _

end Balaban.Fluctuation.StepSetting.JointRep
