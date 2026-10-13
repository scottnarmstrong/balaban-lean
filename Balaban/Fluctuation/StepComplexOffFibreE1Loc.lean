/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreCoeff
public import Balaban.Fluctuation.StepComplexProp26Agree

/-!
# The localized first energy coefficient of the raw joint representation
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)

/-- On the representative chart, the raw first exponent is the fibre exponent after the
covariance substitution. -/
theorem W1_eq_Phi1C_withDatum (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {u : S.EC} (hu : ‖u‖ ≤ pp) :
    Jr.W1 C (rawOf D, u) =
      (S.withDatum D hD).Phi1C C (S.hatField (Jr.Mx (rawOf D)) u) := by
  have hcoord : ∀ p, ‖u p‖ ≤ pp := fun p => (norm_le_pi_norm u p).trans hu
  exact Jr.W1_withDatum_hat C D hD hX hcoord

/-- The covariance-substituted exponent agrees with the fibre exponent on a neighbourhood
of each hat variable strictly inside the representative radius. -/
theorem W1_eventuallyEq_Phi1C_withDatum (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {u : S.EC} (hu : ‖u‖ < pp) :
    (fun v : S.EC => Jr.W1 C (rawOf D, v)) =ᶠ[nhds u]
      (fun v => (S.withDatum D hD).Phi1C C (S.hatField (Jr.Mx (rawOf D)) v)) := by
  filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hu] with v hv
  exact Jr.W1_eq_Phi1C_withDatum C D hD hX hv.le

/-- The complex derivative of the raw first exponent is the fibre derivative transported
through the covariance substitution. -/
theorem fderiv_W1_withDatum (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {u : S.EC} (hu : ‖u‖ < pp)
    (hd : DifferentiableAt ℂ ((S.withDatum D hD).Phi1C C)
      (S.hatField (Jr.Mx (rawOf D)) u)) (v : S.EC) :
    (fderiv ℂ (fun w : S.EC => Jr.W1 C (rawOf D, w)) u) v =
      (fderiv ℂ ((S.withDatum D hD).Phi1C C)
        (S.hatField (Jr.Mx (rawOf D)) u))
          (S.hatField (Jr.Mx (rawOf D)) v) := by
  let T : S.EC →L[ℂ] S.EC :=
    (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
      LinearMap.toContinuousLinearMap (Matrix.mulVecLin (Jr.Mx (rawOf D))))
  have hT (w : S.EC) : T w = S.hatField (Jr.Mx (rawOf D)) w := by
    rfl
  rw [← hT u] at hd
  have hchain : HasFDerivAt (fun w : S.EC => (S.withDatum D hD).Phi1C C (T w))
      ((fderiv ℂ ((S.withDatum D hD).Phi1C C) (T u)).comp T) u :=
    hd.hasFDerivAt.comp u T.hasFDerivAt
  have hev : (fun w : S.EC => Jr.W1 C (rawOf D, w)) =ᶠ[nhds u]
      (fun w : S.EC => (S.withDatum D hD).Phi1C C (T w)) := by
    simpa only [hT] using Jr.W1_eventuallyEq_Phi1C_withDatum C D hD hX hu
  have hraw := hchain.congr_of_eventuallyEq hev
  have hfv := congrArg (fun f : S.EC →L[ℂ] ℂ => f v) hraw.fderiv
  change (fderiv ℂ (fun w : S.EC => Jr.W1 C (rawOf D, w)) u) v =
    (fderiv ℂ ((S.withDatum D hD).Phi1C C) (T u)) (T v) at hfv
  simpa only [hT] using hfv

/-- The complexified real ray has no larger supremum norm than its real radius. -/
theorem norm_smul_yhat_le (s : ℝ) (x : S.E) :
    ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))).2
  exact fun p => S.norm_smul_yhat_le_mul s x p

/-- At any incoming block datum, the derivative of the raw first exponent is the derivative
of the interaction and composed-energy expression evaluated on the old spin of that datum. -/
theorem fderiv_W1_dataUCH (C : StepClass d L N₁ m₁ k N ϱ)
    (H : StepSettingH S) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    {u : S.EC} (hu : ‖u‖ < pp) (v : S.EC) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun q => B.Ψ (unitRep (G' := S.G') q.1) q.2
    let Dpath := fun w : S.EC =>
      H.dataUCH (ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') w)
    let Dcrit := Dpath 0
    (fderiv ℂ (fun w : S.EC => Jr.W1 C (rawOf H.D', w)) u) v =
      (fderiv ℂ (fun w : S.EC =>
        -(S.β : ℂ) * interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
          (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' (Dpath w))
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) (Dpath w) -
            (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
              (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) +
        (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (Dpath w) -
          EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) Dcrit)) u) v := by
  dsimp only
  have hev : (fun w : S.EC => Jr.W1 C (rawOf H.D', w)) =ᶠ[nhds u]
      (fun w : S.EC =>
        -(S.β : ℂ) * interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
          (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
            (H.dataUCH ((fun q =>
              (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
                (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                  (unitRep (G' := S.G') q.1) q.2) +
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') w)))
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
            (H.dataUCH ((fun q =>
              (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
                (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                  (unitRep (G' := S.G') q.1) q.2) +
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') w)) -
            (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
              (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) +
        (EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
          (H.dataUCH ((fun q =>
            (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
              (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                (unitRep (G' := S.G') q.1) q.2) +
            S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') w)) -
          EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
            (H.dataUCH ((fun q =>
              (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
                (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
                  (unitRep (G' := S.G') q.1) q.2) +
              S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') 0)))) := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hu] with w hw
    exact Jr.W1_dataUCH H C hX (fun p => (norm_le_pi_norm w p).trans hw.le)
  exact congrArg (fun f : S.EC →L[ℂ] ℂ => f v) hev.fderiv_eq

/-- The raw localized first energy value agrees with the fibre coefficient when the incoming
field is constant. The raw formula uses the inverse covariance square root to express the
physical block mask in hat coordinates. -/
theorem E1loc_raw_withDatum
    (C : StepClass d L N₁ m₁ k N ϱ)
    {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hc : (S.withDatum D hD).ClassRegularLocC C)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    (∫ s in (0 : ℝ)..1, avgFun S.nuFl
      (fun s x => Jr.W1 C (rawOf D, (s : ℂ) • yhat x))
      (fun x => (fderiv ℂ (fun u : S.EC => Jr.W1 C (rawOf D, u))
        ((s : ℂ) • yhat x))
          ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))) s) =
      (S.withDatum D hD).E1locC C z := by
  obtain ⟨O, hO, hcd, hmem⟩ := hc.phi1
  unfold StepSetting.E1locC
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  refine avgFun_congr_ae ?_ ?_
  · exact Jr.ae_W1_path C hp₁ hlt.le D hD hX hs
  · filter_upwards [S.ae_ball hp₁] with x hx
    have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp₁ x).1 hx
    have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    have hu : ‖(s : ℂ) • yhat x‖ < pp := by
      calc ‖(s : ℂ) • yhat x‖ ≤ |s| * ‖x‖ := norm_smul_yhat_le (S := S) s x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
        _ < pp := by simpa using hxn.trans hlt
    have hshift : S.hatField (Jr.Mx (rawOf D)) (yhat x) =
        (S.withDatum D hD).shiftUC x := by
      rw [Jr.hatField_Mx_withDatum D hD hX]
      rfl
    have hsmul : S.hatField (Jr.Mx (rawOf D)) ((s : ℂ) • yhat x) =
        (s : ℂ) • S.hatField (Jr.Mx (rawOf D)) (yhat x) := by
      unfold StepSetting.hatField
      rw [Matrix.mulVec_smul, smul_comm]
    have hbase : S.hatField (Jr.Mx (rawOf D)) ((s : ℂ) • yhat x) =
        (s : ℂ) • (S.withDatum D hD).shiftUC x := by
      rw [hsmul, hshift]
      rfl
    have hd : DifferentiableAt ℂ ((S.withDatum D hD).Phi1C C)
        (S.hatField (Jr.Mx (rawOf D)) ((s : ℂ) • yhat x)) := by
      rw [hbase]
      exact (hcd.differentiableOn (by norm_num)).differentiableAt
        (hO.mem_nhds (hmem x hxn.le s hs))
    rw [Jr.fderiv_W1_withDatum C D hD hX hu hd]
    rw [Jr.hatField_inv_mask_of_chart ⟨D⟩ hC hMX hdm hα hsm hX z x]
    rw [hbase, hshift]
    rfl

end Balaban.Fluctuation.StepSetting.JointRep
