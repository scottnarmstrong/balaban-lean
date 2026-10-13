/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexProp26
public import Balaban.Fluctuation.StepComplexOutAnalytic

/-!
# The chart function and the exponential identity of a step, for a general class member

`classPath_step` packages two landed theorems: the analytic chart function of the fluctuation
integral (`exists_analyticAt_TstepC_of_analyticAt_class`, with the path analyticity of the class
terms) and the exponential identity of Proposition 2.6 at a complex block datum
(`prop26C_class_of_activity`, with the class regularity and the complex activity bound).
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- The analytic chart function of the fluctuation integral and the exponential identity of
Proposition 2.6, for a general class member with the complex activity bound. -/
theorem classPath_step
    (hcore : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 1 < R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {pp : ℝ} (hlt : S.p₁ < pp)
    (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D')
    (g : Fld d L N₁ m₁ (k + 1) N)
    (hpaths : ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      (S.withDatum D hDh).EdensAnalyticOnPath C ∧
      (S.withDatum D hDh).FlocAnalyticOnPath C g)
    (hreg : S.ClassRegularC C g) (hact : StepActivityBoundC S C g) :
    (∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hDh).TstepC C g ∧
        AnalyticAt ℂ F (rawOf D)) ∧
    (S.TstepC C g = Complex.exp (-(S.β : ℂ) * S.AnewC +
      EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC -
      (S.Eppp C : ℂ) * (S.nU : ℂ) +
      FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) S.psiKdC g +
      S.E0C C + S.F0C C g)) := by
  refine ⟨?_, S.prop26C_class_of_activity C hcore hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hlt hδ₁
    hD g hreg hact⟩
  obtain ⟨F, hF⟩ := S.exists_analyticAt_TstepC_of_analyticAt_class C hcore hMX hdm hα hsm ha₁ hc7
    hR hsmR hβ.le hp₁ hlt hδ₁ g
  refine ⟨F, fun D hDh hX => ?_⟩
  obtain ⟨h1, h2⟩ := hF D hDh hX
  exact ⟨h1, h2 (hpaths D hDh hX).1 (hpaths D hDh hX).2⟩

end Balaban.Fluctuation.StepSetting
