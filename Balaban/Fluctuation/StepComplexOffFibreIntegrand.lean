/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreAction
public import Balaban.Fluctuation.StepComplexJointH
import Mathlib.Tactic.Ring

/-!
# The pointwise fluctuation integrand at an arbitrary block datum
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.LargeField Balaban.SmallField.Def6 Balaban.Background
  Balaban.Multiscale Balaban.Localization Balaban.SmallField Finset Matrix

/-- Algebraic form of the pointwise integrand identity. -/
theorem integrand_of_action_expansion (β u : ℝ) (hβ : β ≠ 0)
    (K J Aold Anew V Eold Enew Fold Fnew Ek : ℂ)
    (hJ : J + Aold = Anew + ((u / (2 * β) : ℝ) : ℂ) + V) :
    K * Complex.exp (-((β : ℂ) * J)) *
      Complex.exp (-(β : ℂ) * Aold + Eold - Ek + Fold) =
      K * Complex.exp (-(β : ℂ) * Anew + Enew - Ek + Fnew) *
        ((Real.exp (-u / 2) : ℝ) : ℂ) *
        Complex.exp (-(β : ℂ) * V + (Eold - Enew) + (Fold - Fnew)) := by
  exact integrand_of_action_expansion_core β u hβ K J Aold Anew V Eold Enew Fold Fnew Ek hJ

namespace StepSettingH

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (H : StepSettingH S)
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- The kernel and density at the raw old spin equal the Gaussian weight times the two
interpolating interaction exponents, for an arbitrary external field. -/
theorem integrandC_eq
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
    (C : StepClass d L N₁ m₁ k N ϱ) (g : Fld d L N₁ m₁ (k + 1) N)
    (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    let ψ₀ : S.EC := fun p => B.Ψ (unitRep (G' := S.G') p.1) p.2
    let ψ := ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)
    let D := H.dataUCH ψ
    let K : ℂ := (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ)
    let J := couplingC S.G' S.a₁ (k + 1) H.D'.Ψ D.Ψ
    let Aold := actionRawC (stepG d L N₁ m₁ k ϱ) S.a S.ν D.Ψ D.h
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D)
    let Anew := actionRawC S.G' S.a S.ν H.D'.Ψ H.D'.h
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
    let V := interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
      (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' D)
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D -
        (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
    let Eold := EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D
    let Enew := EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B
    let Fold := FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D g
    let Fnew := FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B g
    K * Complex.exp (-(S.β : ℂ) * J) *
      Complex.exp (-(S.β : ℂ) * Aold + Eold - (C.Ek : ℂ) * (S.nU : ℂ) + Fold) =
      K * Complex.exp (-(S.β : ℂ) * Anew + Enew - (C.Ek : ℂ) * (S.nU : ℂ) + Fnew) *
        ((gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (-(S.β : ℂ) * V + (Eold - Enew) + (Fold - Fnew)) := by
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
  let ψ₀ : S.EC := fun p => B.Ψ (unitRep (G' := S.G') p.1) p.2
  let ψ := ψ₀ + S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x)
  let D := H.dataUCH ψ
  let K : ℂ := (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ)
  let J := couplingC S.G' S.a₁ (k + 1) H.D'.Ψ D.Ψ
  let Aold := actionRawC (stepG d L N₁ m₁ k ϱ) S.a S.ν D.Ψ D.h
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D)
  let Anew := actionRawC S.G' S.a S.ν H.D'.Ψ H.D'.h
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
  let V := interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
    (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' D)
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D -
      (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D'))
  let Eold := EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D
  let Enew := EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B
  let Fold := FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D g
  let Fnew := FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B g
  have hJ : J + Aold = Anew +
      ((1 / (2 * S.β) * ∑ b : S.U, ‖x b‖ ^ 2 : ℝ) : ℂ) + V :=
    H.JbgC_expansion hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD x hx
  have hJ' : J + Aold = Anew +
      (((∑ b : S.U, ‖x b‖ ^ 2) / (2 * S.β) : ℝ) : ℂ) + V := by
    convert hJ using 1
    congr 1
    field_simp
  change K * Complex.exp (-(S.β : ℂ) * J) *
      Complex.exp (-(S.β : ℂ) * Aold + Eold - (C.Ek : ℂ) * (S.nU : ℂ) + Fold) =
    K * Complex.exp (-(S.β : ℂ) * Anew + Enew - (C.Ek : ℂ) * (S.nU : ℂ) + Fnew) *
      ((gaussWeight S.U N x : ℝ) : ℂ) *
      Complex.exp (-(S.β : ℂ) * V + (Eold - Enew) + (Fold - Fnew))
  convert (integrand_of_action_expansion S.β (∑ b : S.U, ‖x b‖ ^ 2) hβ.ne'
    K J Aold Anew V Eold Enew Fold Fnew ((C.Ek : ℂ) * (S.nU : ℂ)) hJ') using 1
  · simp only [neg_mul]
  · unfold gaussWeight
    rfl

end StepSettingH

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  (H : StepSettingH S) (C : StepClass d L N₁ m₁ k N ϱ)
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- On fluctuation support, the joint integrand agrees with the Gaussian expression at any
block datum without comparing the support radius to the representative radius. -/
theorem integrandJ_eq_unbounded
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
    (g : Fld d L N₁ m₁ (k + 1) N)
    (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    Jr.tKJ (rawOf H.D', yhat x) * Jr.rhoJ C g (rawOf H.D', yhat x) =
      (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
        Complex.exp (-(S.β : ℂ) *
          actionRawC S.G' S.a S.ν H.D'.Ψ H.D'.h
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') +
          EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B -
          (C.Ek : ℂ) * (S.nU : ℂ) +
          FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B g) *
        ((gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (Jr.W1 C (rawOf H.D', yhat x) +
          Jr.W2 C g (rawOf H.D', yhat x)) := by
  dsimp only
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.right_mem_Icc.2 zero_le_one
  have hdom := H.dataUCH_hatRay_inUnionDomainC hC hMX hdm hα hsm ha₁ hc7 hR hsmR
    hβ.le hp₁ hδ₁ hD h1 hx
  dsimp only at hdom
  simp only [Complex.ofReal_one, one_smul] at hdom
  let D₀ := H.dataUCH
    ((fun q =>
      (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
          (unitRep (G' := S.G') q.1) q.2) +
      S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (yhat x))
  have hraw : Jr.gJ (rawOf H.D', yhat x) = rawOf D₀ := Jr.gJ_dataUCH H hD (yhat x)
  have hFJ : Jr.FJ (rawOf H.D', yhat x) =
      (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀,
       bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀) := by
    unfold JointRep.FJ
    rw [hraw]
    exact Jr.Fb_eq D₀ hdom
  have hPJ (j : ℕ) : Jr.PJ j (rawOf H.D', yhat x) =
      composedPairAtC S.a S.ν (Nat.le_succ k) j D₀ := by
    unfold JointRep.PJ composedPairAtC
    split_ifs with hj
    · rw [hFJ, hraw]
      rfl
    · rfl
  have hEJ : Jr.EJ C (rawOf H.D', yhat x) =
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ := by
    unfold JointRep.EJ EcompAtC
    simp only [hPJ]
  have hFcJ : Jr.FcJ C g (rawOf H.D', yhat x) =
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D₀ g := by
    unfold JointRep.FcJ FcompAtC
    simp only [hPJ, hFJ]
  have hVJ : Jr.VJ (rawOf H.D', yhat x) =
      interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) H.D')
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')
        (compTangent S.hG S.hG' (le_refl (k + 1)) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' D₀)
        (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D₀ -
          (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D')) := by
    unfold JointRep.VJ
    dsimp only
    rw [hFJ, Jr.F₀_eq H.D' hD, Jr.Mx_eq H.D' hD,
      Jr.tangent_datum H.D' hD D₀ hraw]
  have hcrit : H.dataUCH
      ((fun q =>
        (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D').Ψ
            (unitRep (G' := S.G') q.1) q.2) +
        S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') 0) =
      composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D' := by
    have hz : S.hatField (hatCovSqrt S.G' S.a₁ S.ν H.D') (0 : S.EC) = 0 := by
      unfold StepSetting.hatField
      rw [Matrix.mulVec_zero, smul_zero]
    rw [hz, add_zero]
    exact H.dataUCH_psi0C
  rw [Jr.tKJ_dataUCH H hD (yhat x)]
  unfold JointRep.rhoJ JointRep.W1 JointRep.W2
  rw [hFJ, hraw, hEJ, hFcJ, hVJ]
  rw [Jr.EJ_dataUCH H C hD Jr.zero_le_pp,
    Jr.FcJ_dataUCH H C hD Jr.zero_le_pp g]
  rw [hcrit]
  have hint := H.integrandC_eq hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ hD C g x hx
  dsimp only at hint
  simpa only [rawOf, Prod.fst, Prod.snd, neg_mul, add_assoc] using hint

/-- The joint kernel and density have the Gaussian pointwise integrand at an arbitrary datum. -/
theorem integrandJ_eq
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hpp : S.p₁ ≤ pp)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps H.D')
    (g : Fld d L N₁ m₁ (k + 1) N)
    (x : S.E) (hx : chiFl S.U N S.p₁ x = 1) :
    let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') H.D'
    Jr.tKJ (rawOf H.D', yhat x) * Jr.rhoJ C g (rawOf H.D', yhat x) =
      (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
        Complex.exp (-(S.β : ℂ) *
          actionRawC S.G' S.a S.ν H.D'.Ψ H.D'.h
            (bgFieldC S.G' S.a S.ν (bgC0 d L N) H.D') +
          EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B -
          (C.Ek : ℂ) * (S.nU : ℂ) +
          FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B g) *
        ((gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (Jr.W1 C (rawOf H.D', yhat x) +
          Jr.W2 C g (rawOf H.D', yhat x)) := by
  have _hbound : S.p₁ ≤ pp := hpp
  exact Jr.integrandJ_eq_unbounded H C hC hMX hdm hα hsm ha₁ hc7 hR hsmR
    hβ hp₁ hδ₁ hD g x hx

end StepSetting.JointRep

end Balaban.Fluctuation
