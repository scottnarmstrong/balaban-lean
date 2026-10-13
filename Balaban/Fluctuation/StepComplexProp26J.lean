/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexOffFibreJoint
public import Balaban.Fluctuation.StepComplexOutAnalytic
public import Balaban.Fluctuation.StepInterpolationCore
import Mathlib.Tactic.Ring

/-!
# Proposition 2.6 at an arbitrary block datum

The joint representation gives the step identity without fixing the external field of the
incoming datum. The analytic input is regularity and nonvanishing along the two interpolation
segments.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Fluctuation Balaban.LargeField Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Multiscale Balaban.Localization Matrix MeasureTheory Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp)
  {c BG κ Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- Proposition 2.6 for the joint representation with no comparison between the support radius
and the representative radius. -/
theorem prop26J_step_unbounded (C : StepClass d L N₁ m₁ k N ϱ)
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
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (hreg : ∃ (U : Set ℝ) (W₁' W₂' : ℝ → S.E → ℂ),
      IsC1Family U
        (fun s x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W1 C (rawOf D, (s : ℂ) • yhat x) else 0) W₁' ∧
      IsC1Family U
        (fun t x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W2 C g (rawOf D, (t : ℂ) • yhat x) else 0) W₂')
    (hnv1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 C (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl) ≠ 0)
    (hnv2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 C (rawOf D, yhat x) +
          Jr.W2 C g (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) :
    Jr.TstepJ C g (rawOf D) = Complex.exp (
      -(S.β : ℂ) * actionRawC S.G' S.a S.ν D.Ψ D.h (Jr.F₀ (rawOf D)).1 +
      Jr.EJ C (rawOf D, 0) - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      Jr.FcJ C g (rawOf D, 0) -
      (1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N,
        (decLog S.G' S.a S.a₁ S.ν (Jr.F₀ (rawOf D)).2 (fun _ => 1)
          (svec S.G' (Jr.F₀ (rawOf D)).1) (unitQ S.G') (unitP S.G'))
            (y, i) (y, i) +
      S.avgJ (fun _ => 0) (Jr.W1 C) (Jr.W1 C) (rawOf D) +
      S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.W2 C g) (rawOf D)) := by
  classical
  let H : StepSettingH S := S.withDatumH D
  let W₁ : ℝ → S.E → ℂ := fun s x => Jr.W1 C (rawOf D, (s : ℂ) • yhat x)
  let W₂ : ℝ → S.E → ℂ := fun t x => Jr.W2 C g (rawOf D, (t : ℂ) • yhat x)
  let Wt₁ : ℝ → S.E → ℂ := fun s x => if chiFl S.U N S.p₁ x = 1 then W₁ s x else 0
  let Wt₂ : ℝ → S.E → ℂ := fun t x => if chiFl S.U N S.p₁ x = 1 then W₂ t x else 0
  obtain ⟨U, W₁', W₂', h₁, h₂⟩ := hreg
  have hprob : IsProbabilityMeasure S.nuFl := isProbabilityMeasure_fluctMeasure S.U N hp₁
  have hae : ∀ᵐ x ∂S.nuFl, chiFl S.U N S.p₁ x = 1 := S.ae_ball hp₁
  have hae₁ : ∀ᵐ x ∂S.nuFl, ∀ r, Wt₁ r x = W₁ r x :=
    hae.mono fun x hx r => by simp [Wt₁, hx]
  have hae₂ : ∀ᵐ x ∂S.nuFl, ∀ r, Wt₂ r x = W₂ r x :=
    hae.mono fun x hx r => by simp [Wt₂, hx]
  have hW₁0 : ∀ x, W₁ 0 x = 0 := by
    intro x
    simp only [W₁, Complex.ofReal_zero, zero_smul]
    unfold StepSetting.JointRep.W1
    have hV : Jr.VJ (rawOf D, 0) = 0 := by
      simpa only [H, StepSetting.withDatumH] using Jr.VJ_zero H hC ha₁ hc7 hX
    rw [hV]
    ring
  have hW₂0 : ∀ x, W₂ 0 x = 0 := by
    intro x
    simp [W₂, StepSetting.JointRep.W2]
  have hWt₁0 : ∀ x, Wt₁ 0 x = 0 := fun x => by simp [Wt₁, hW₁0 x]
  have hWt₂0 : ∀ x, Wt₂ 0 x = 0 := fun x => by simp [Wt₂, hW₂0 x]
  let K0 : ℝ := (S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2)
  let bp : ℝ := S.betaU ^ (-((N * Fintype.card S.U : ℕ) : ℝ) / 2)
  let Zc : ℝ := fluctNorm N S.p₁ ^ Fintype.card S.U
  let Y : ℂ := -(S.β : ℂ) * actionRawC S.G' S.a S.ν D.Ψ D.h
      (Jr.F₀ (rawOf D)).1 + Jr.EJ C (rawOf D, 0) - (C.Ek : ℂ) * (S.nU : ℂ) +
      Jr.FcJ C g (rawOf D, 0)
  let P : ℂ := (K0 : ℂ) * Complex.exp Y
  let B := composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
    (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D
  have hzero : S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (0 : S.EC) = 0 := by
    unfold StepSetting.hatField
    rw [Matrix.mulVec_zero, smul_zero]
  have hE0 : Jr.EJ C (rawOf D, 0) =
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B := by
    have he := Jr.EJ_dataUCH H C hX Jr.zero_le_pp
    dsimp only [H, StepSetting.withDatumH] at he
    rw [hzero, add_zero, StepSettingH.dataUCH_psi0C] at he
    exact he
  have hF0 : Jr.FcJ C g (rawOf D, 0) =
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) B g := by
    have hf := Jr.FcJ_dataUCH H C hX Jr.zero_le_pp g
    dsimp only [H, StepSetting.withDatumH] at hf
    rw [hzero, add_zero, StepSettingH.dataUCH_psi0C] at hf
    exact hf
  have hconst := S.const_identity C (Nat.pos_of_ne_zero (NeZero.ne L)) ha₁ hβ hp₁
  have hδ : Complex.exp (((-((S.Eppp C - C.Ek) * S.nU) : ℝ) : ℂ)) =
      (K0 : ℂ) * ((bp : ℂ) * (Zc : ℂ)) := by
    rw [← Complex.ofReal_exp, ← hconst]
    dsimp [K0, bp, Zc]
    push_cast
    ring
  have hint : ∀ x : S.E,
      ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
        (Jr.tKJ (rawOf D, yhat x) * Jr.rhoJ C g (rawOf D, yhat x)) =
      P * ((chiFl S.U N S.p₁ x * gaussWeight S.U N x : ℝ) : ℂ) *
        Complex.exp (Wt₁ 1 x + Wt₂ 1 x) := by
    intro x
    by_cases hx : chiFl S.U N S.p₁ x = 1
    · have hi := Jr.integrandJ_eq_unbounded H C hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
        hδ₁ hX g x hx
      dsimp only [H] at hi
      dsimp only [StepSetting.withDatumH] at hi
      rw [hi]
      simp only [Wt₁, Wt₂, W₁, W₂, hx, ite_true]
      dsimp [P, Y, K0]
      rw [Jr.F₀_eq D hX, hE0, hF0]
      dsimp [B]
      simp only [one_smul, one_mul]
    · have h0 : chiFl S.U N S.p₁ x = 0 := (chiFl_eq_zero_or_one S.p₁ x).resolve_right hx
      simp [h0]
  have hdet := Jr.det_Mx_eq_trace H hC hMX hdm hα hsm hX
  unfold TstepJ
  refine step_interp_identity S.nuFl MeasureTheory.volume Wt₁ Wt₂ W₁ W₂ h₁ h₂
    hae₁ hae₂ hWt₁0 hWt₂0 hW₂0
    (fun s hs => by
      simpa only [partFun₂, hW₂0, add_zero, W₁] using hnv1 s hs)
    (fun t ht => ?_)
    (fun x => ((chiFl S.U N S.p₁ x : ℝ) : ℂ) *
      (Jr.tKJ (rawOf D, yhat x) * Jr.rhoJ C g (rawOf D, yhat x)))
    (fun x => chiFl S.U N S.p₁ x * gaussWeight S.U N x)
    P (Zc : ℂ) (K0 : ℂ) (bp : ℂ) (Jr.Mx (rawOf D)).det
    Y (((-((S.Eppp C - C.Ek) * S.nU) : ℝ) : ℂ))
    (-(1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N,
      (decLog S.G' S.a S.a₁ S.ν (Jr.F₀ (rawOf D)).2 (fun _ => 1)
        (svec S.G' (Jr.F₀ (rawOf D)).1) (unitQ S.G') (unitP S.G'))
          (y, i) (y, i))
    (S.avgJ (fun _ => 0) (Jr.W1 C) (Jr.W1 C) (rawOf D))
    (S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.W2 C g) (rawOf D)) _
    ?_ ?_ hint
    (integral_fluct_weight_eq (T := S.U) (N := N) hp₁ P Wt₁ Wt₂)
    rfl hδ hdet ?_
  · simpa only [partFun₂, W₁, W₂, Complex.ofReal_one, one_smul] using hnv2 t ht
  · unfold avgJ avgFun partFun W₁
    simp only [zero_add]
  · unfold avgJ avgFun₂ partFun₂ W₁ W₂
    simp only [Complex.ofReal_one, one_smul]
  · dsimp [Y]
    push_cast
    ring

/-- Proposition 2.6 for the joint representation at any datum of the complex chart. -/
theorem prop26J_step (C : StepClass d L N₁ m₁ k N ϱ)
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
    (D : BgData S.G' N) (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (hreg : ∃ (U : Set ℝ) (W₁' W₂' : ℝ → S.E → ℂ),
      IsC1Family U
        (fun s x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W1 C (rawOf D, (s : ℂ) • yhat x) else 0) W₁' ∧
      IsC1Family U
        (fun t x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W2 C g (rawOf D, (t : ℂ) • yhat x) else 0) W₂')
    (hnv1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 C (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl) ≠ 0)
    (hnv2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 C (rawOf D, yhat x) +
          Jr.W2 C g (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) :
    Jr.TstepJ C g (rawOf D) = Complex.exp (
      -(S.β : ℂ) * actionRawC S.G' S.a S.ν D.Ψ D.h (Jr.F₀ (rawOf D)).1 +
      Jr.EJ C (rawOf D, 0) - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      Jr.FcJ C g (rawOf D, 0) -
      (1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N,
        (decLog S.G' S.a S.a₁ S.ν (Jr.F₀ (rawOf D)).2 (fun _ => 1)
          (svec S.G' (Jr.F₀ (rawOf D)).1) (unitQ S.G') (unitP S.G'))
            (y, i) (y, i) +
      S.avgJ (fun _ => 0) (Jr.W1 C) (Jr.W1 C) (rawOf D) +
      S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.W2 C g) (rawOf D)) := by
  have _hbound : S.p₁ ≤ pp := hpp
  exact Jr.prop26J_step_unbounded C hC hMX hdm hα hsm ha₁ hc7 hR hsmR
    hβ hp₁ hδ₁ D hX g hreg hnv1 hnv2

end Balaban.Fluctuation.StepSetting.JointRep
