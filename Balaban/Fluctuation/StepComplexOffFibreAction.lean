/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreC
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The raw action expansion of the complex step
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.LargeField Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale
  Balaban.Localization Balaban.SmallField Finset Matrix

namespace StepSettingH

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (H : StepSettingH S)
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- The exact quadratic action expansion at an arbitrary datum of the complex chart. -/
theorem JbgC_expansion
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun p => B.Ψ (unitRep (G' := S.G') p.1) p.2
    let ψ := ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)
    let D := H.dataUCH ψ
    couplingC S.G' S.a₁ (k + 1) H.D'.Ψ D.Ψ +
      actionRawC (stepG d L N₁ m₁ k ϱ) S.a S.ν D.Ψ D.h
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D) =
      actionRawC S.G' S.a S.ν H.D'.Ψ H.D'.h
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') +
      ((1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) +
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' D)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) := by
  dsimp only
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have hDC := H.dataUCH_hatRay_inUnionDomainC hC hMX hdm hα hsm ha₁ hc7 hR hsmR
    hβ.le hp₁ hδ₁ hD h1 hx
  dsimp only at hDC
  simp only [Complex.ofReal_one, one_smul] at hDC
  have hb : barField S.G' H.D'.Ψ (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') =
      svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') := by
    funext z i
    exact barField_eq_svec S.hG' _ _ z i
  have hM : hatCovSqrt S.G' S.a₁ S.ν H.D' =
      decCovSqrt S.G' S.a S.a₁ S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
        (unitQ S.G') (unitP S.G') := by
    unfold hatCovSqrt
    rw [hb]
  have ht : compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
      (H.dataUCH ((fun p =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') p.1) p.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x))) =
      liftC S.hG' (S.hatField
        (decCovSqrt S.G' S.a S.a₁ S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D') (fun _ => 1)
          (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
          (unitQ S.G') (unitP S.G')) (yhat x)) := by
    rw [H.compTangent_dataUCH]
    simp only [add_sub_cancel_left]
    rw [hM]
  change couplingC S.G' S.a₁ (k + 1) H.D'.Ψ _ + actionC _ _ _ _ _ =
    actionC _ _ _ _ _ + _ + _
  exact S.action_expansion_core hC hMX hdm hα hsm ha₁ hc7 hβ
    H.D' hD _ hDC (fun z i => H.dataUCH_h _ z i) x ht

end StepSettingH

end Balaban.Fluctuation
