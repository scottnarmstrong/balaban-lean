/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The exponents of the complex step as functions of the block datum (FLUCTUATION Lemma 2.3 (d))

* `analyticAt_interactionV`: the interaction `V^{(k)}` of (2.4) is analytic in
  `(α_{k+1}, φ_{k+1}, ψ', φ')` at every point where `H_k` and the constraint form
  `φ_{k+1} · G_k φ_{k+1}` are invertible (FLUCTUATION Lemma 2.3 (d): "`V^{(k)}(z)` is analytic in
  `(ψ', φ_{k+1}, α_{k+1})`");
* `exists_analytic_interactionV_tangent`, `StepSetting.exists_analytic_VkC_path`: on the complex
  chart, the potential part `V^{(k)}(ψ^{(k)} + s ψ')` of `W₁` of the complex step is analytic in the
  block datum;
* `StepSetting.exists_analytic_composedPairAtC_path`: the composed data `(ψ_k^{(j)}, h)` of (H.2)
  of the complex old spin on the path are analytic in the block datum;
* `StepSetting.exists_analyticAt_WoneC_of_analyticAt_Edens`,
  `StepSetting.exists_analyticAt_WtwoC_of_analyticAt_Floc`: one function of the raw data returns
  `WoneC` (`WtwoC`) of the step at every datum of the chart with `h = h₀`, and is analytic at every
  such datum at which the densities `ℰ^{(j)}` (the terms `ℱ^{(j)}`) of the class are analytic at
  the composed data of the path point and of the critical point.  These two are conditional: the
  analyticity of the class terms on `Ξ^c_j` ((H.2), (H.7)) gives the premise once the composed data
  of the complex path are known to lie in the domains `XiDom` (not proved here).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Rect

variable {E m n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coordinates of `M *ᵥ v` are analytic if the entries of `M` and the coordinates of `v`
are. -/
theorem RectAt.mulVec [Fintype n] {M : E → Matrix m n ℂ} {v : E → n → ℂ} {e : E}
    (hM : RectAt M e) (hv : ∀ j, AnalyticAt ℂ (fun e' => v e' j) e) (i : m) :
    AnalyticAt ℂ (fun e' => (M e' *ᵥ v e') i) e := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.analyticAt_fun_sum _ fun j _ => (hM i j).mul (hv j)

end Rect

section Interaction

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'}

/-- **The interaction `V^{(k)}` is analytic in `(α_{k+1}, φ_{k+1}, ψ', φ')`** (FLUCTUATION
Lemma 2.3 (d); P4 (2.29)) at every point where `H_k = opHk` and the constraint form
`φ_{k+1} · G_k φ_{k+1}` are invertible (so that `G_k = H_k⁻¹` and `Π_k` are analytic). -/
theorem analyticAt_interactionV {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q₀ : Q}
    (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) {αF : Q → G'.Ω 1 → ℂ}
    {φF : Q → G'.Ω 1 × Fin N → ℂ} {ψF : Q → Torus d (N₀ * L ^ K) → Fin N → ℂ}
    {φ'F : Q → G.Ω 1 × Fin N → ℂ}
    (hα : ∀ y, AnalyticAt ℂ (fun q => αF q y) q₀) (hφ : ∀ r, AnalyticAt ℂ (fun q => φF q r) q₀)
    (hψ : ∀ y i, AnalyticAt ℂ (fun q => ψF q y i) q₀)
    (hφ' : ∀ r, AnalyticAt ℂ (fun q => φ'F q r) q₀)
    (hH : IsUnit (opHk h a ν (αF q₀)))
    (hM : IsUnit (constraintForm (opHk h a ν (αF q₀))⁻¹ (fieldBase (N := N) h (φF q₀)))) :
    AnalyticAt ℂ (fun q => interactionV h a ν (αF q) (φF q) (ψF q) (φ'F q)) q₀ := by
  classical
  have hHk : RectAt (fun q => opHk h a ν (αF q)) q₀ := by
    unfold opHk dirichletOperator
    refine (RectAt.const _ q₀).add fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact hα _
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact analyticAt_const
  have hA : RectAt (fun q => (opHk h a ν (αF q))⁻¹) q₀ :=
    hHk.inv ((Matrix.isUnit_iff_isUnit_det _).1 hH).ne_zero
  have hFm : RectAt (fun q => fieldMul (fieldBase (N := N) h (φF q))) q₀ := by
    intro p y
    by_cases hpy : p.1 = y
    · simp only [fieldMul, hpy, ↓reduceIte]
      exact hφ _
    · simp only [fieldMul, hpy, ↓reduceIte]
      exact analyticAt_const
  have hCF : RectAt (fun q => constraintForm (opHk h a ν (αF q))⁻¹
      (fieldBase (N := N) h (φF q))) q₀ :=
    (hFm.transpose'.mul (hA.liftOp (N := N))).mul hFm
  have hCFi := hCF.inv ((Matrix.isUnit_iff_isUnit_det _).1 hM).ne_zero
  have hPi : RectAt (fun q => constrainedOp (opHk h a ν (αF q))⁻¹
      (fieldBase (N := N) h (φF q))) q₀ :=
    ((((hA.liftOp (N := N)).mul hFm).mul hCFi).mul hFm.transpose').mul (hA.liftOp (N := N))
  have hS : ∀ p, AnalyticAt ℂ (fun q => qStar G a (ψF q) p) q₀ := fun p => by
    unfold qStar
    exact analyticAt_const.mul (hψ _ _)
  have hphi1 : ∀ p, AnalyticAt ℂ
      (fun q => phiOne h a ν (αF q) (φF q) (qStar G a (ψF q)) p) q₀ := fun p => by
    unfold phiOne
    exact ((hA.liftOp (N := N)).sub hPi).mulVec hS p
  have halpha1 : ∀ x, AnalyticAt ℂ
      (fun q => alphaOne h a ν (αF q) (φF q) (qStar G a (ψF q)) x) q₀ := fun x => by
    unfold alphaOne
    exact hCFi.mulVec (fun y => hFm.transpose'.mulVec
      (fun r => (hA.liftOp (N := N)).mulVec hS r) y) x
  have hdiff : ∀ p, AnalyticAt ℂ
      (fun q => (φ'F q - phiOne h a ν (αF q) (φF q) (qStar G a (ψF q))) p) q₀ := fun p =>
    (hφ' p).sub (hphi1 p)
  unfold interactionV pair
  exact (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun x _ => (halpha1 x).mul
      (Finset.analyticAt_fun_sum _ fun i _ => (hφ' _).mul (hφ' _)))).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun p _ => (hdiff p).mul
      ((hHk.liftOp (N := N)).mulVec hdiff p)))

end Interaction

section VTangent

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
  (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (ha₁ : 0 < a₁)
  (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
  {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
  {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)

include hC hk ha₁ H hc7 hR hsmR hMX hdm hα hsm hcψ hδ₁ hψh in
/-- **The interaction `V^{(k)}` at the old spin with tangent `hatLift cc D' ψ̂` is analytic in the
block datum `D'`** on the chart (FLUCTUATION Lemma 2.3 (d), with the analytic backgrounds): one
function of the raw data, analytic on `Ξ^c(𝔹_{k+1}; 1, ε)`, returns
`V^{(k)}(ψ') = interactionV (α_{k+1}, φ_{k+1}, ψ', φ_k(ψ) - φ_{k+1})` for every datum `D` of level
`k` with the same `h̃` as `D'` and tangent `ψ' = D.Ψ - ψ^{(k)}(D') = hatLift cc D' ψ̂`. -/
theorem exists_analytic_interactionV_tangent :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      AnalyticOnNhd ℂ F (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) ∧
      ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
        ∀ D : BgData Hm N, (∀ x i, D.h x i = D'.h x i) →
          compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D =
              hatLift Gp a₁ ν hG' cc D' ψh →
          F (rawOf D') = interactionV (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν
            (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D')
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')
            (compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
              (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D)
            (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
              (hG.precedes hG' (le_refl (k + 1))).restrictφ
                (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D')) := by
  obtain ⟨F₀, hF₀an, hF₀⟩ := exists_analytic_bgC hC
  obtain ⟨M, hMan, hM⟩ := exists_analytic_hatCovSqrt hC hk hMX hdm hα hsm
  obtain ⟨F₁, hF₁an, hF₁⟩ := exists_analytic_bgC_tangent hC hk hG hG' ha₁ H hc7 hR hsmR hMX hdm hα
    hsm cc hcψ hδ₁ hψh
  refine ⟨fun Θ => interactionV (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν (F₀ Θ).2
    (F₀ Θ).1 (liftC hG' (cc • (M Θ *ᵥ ψh)))
    ((F₁ Θ).1 - (hG.precedes hG' (le_refl (k + 1))).restrictφ (F₀ Θ).1), ?_, ?_⟩
  · rintro Θ ⟨D', hD', rfl⟩
    have hF₀at := hF₀an _ ⟨D', hD', rfl⟩
    have hF₁at := hF₁an _ ⟨D', hD', rfl⟩
    have hD'2 : InUnionDomainC Gp (bgC0 d L N) (thm73C2 d L N) ν D' :=
      (isDecBg_one_of_xiCData hC hD').2.mono (hc7.trans (thm73C3_le_thm73C2 d L N))
    obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ hG hG' (le_refl (k + 1)) H hC.HBp D' hD'2
    have hΦ' : restrictField Hm Φ = fieldBase (hG.precedes hG' (le_refl (k + 1)))
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') := funext fun x => funext fun i => hΦ x i
    refine analyticAt_interactionV (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν
      (αF := fun Θ => (F₀ Θ).2) (φF := fun Θ => (F₀ Θ).1)
      (ψF := fun Θ => liftC hG' (cc • (M Θ *ᵥ ψh)))
      (φ'F := fun Θ => (F₁ Θ).1 - (hG.precedes hG' (le_refl (k + 1))).restrictφ (F₀ Θ).1)
      (fun y => analyticAt_pi_iff.1 (analyticAt_snd.comp hF₀at) y)
      (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀at) r)
      (fun y i => ?_) (fun r => ?_) ?_ ?_
    · simp only [liftC_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun r _ =>
        (hMan _ r _ ⟨D', hD', rfl⟩).mul analyticAt_const)
    · exact (analyticAt_pi_iff.1 (analyticAt_fst.comp hF₁at) r).sub
        (analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀at) _)
    · show IsUnit (opHk (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν (F₀ (rawOf D')).2)
      rw [hF₀ D' hD']
      exact dirichletOperator_isUnit Hm St.pos St.mass St.weights _ St.alpha
    · show IsUnit (constraintForm
        (opHk (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν (F₀ (rawOf D')).2)⁻¹
        (fieldBase (hG.precedes hG' (le_refl (k + 1))) (F₀ (rawOf D')).1))
      rw [hF₀ D' hD', ← hΦ']
      exact constraintForm_isUnit St
  · intro D' hD' D hh ht
    show interactionV (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν (F₀ (rawOf D')).2
      (F₀ (rawOf D')).1 (liftC hG' (cc • (M (rawOf D') *ᵥ ψh)))
      ((F₁ (rawOf D')).1 - (hG.precedes hG' (le_refl (k + 1))).restrictφ (F₀ (rawOf D')).1) = _
    rw [hF₀ D' hD', hM D' hD', hF₁ D' hD' D hh ht, ht]
    rfl

end VTangent

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Localization Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

section Path

variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (ha₁ : 0 < S.a₁) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 1 < R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hβ : 0 ≤ S.β) (hp₁ : 0 < S.p₁)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * S.p₁)) < δ₁)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **The potential part `V^{(k)}(ψ^{(k)} + s ψ')` of `W₁` of the complex step is analytic in the
block datum** on the chart: for `s ∈ [0,1]` and `χ_fl(ψ̂) = 1`, one function of the raw data,
analytic on `Ξ^c(𝔹_{k+1}; 1, ε)`, returns `VkC (psiAtC s ψ̂)` of the step with the datum `D`, for
every datum `D` of the chart with `h = h₀`. -/
theorem exists_analytic_VkC_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).VkC ((S.withDatum D hD).psiAtC s x) := by
  obtain ⟨F, hFan, hF⟩ := exists_analytic_interactionV_tangent hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7
    hR hsmR hMX hdm hα hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hp₁.le
    (by rwa [S.norm_betaU_rpow hβ]) (S.norm_smul_yhat_le hp₁ hs hx)
  refine ⟨F, hFan, fun D hD hX => ?_⟩
  exact hF D hX ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x))
    (fun z i => by rw [(S.withDatum D hD).dataUC_h]; exact (hD z i).symm)
    ((S.withDatum D hD).compTangent_psiAtC s x)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **The composed data `(ψ_k^{(j)}, h)` of (H.2) of the complex old spin on the path are analytic
in the block datum** on the chart: for `s ∈ [0,1]`, `χ_fl(ψ̂) = 1` and every `j`, one function of
the raw data, analytic on `Ξ^c(𝔹_{k+1}; 1, ε)`, returns the pair `composedPairAtC j` of the datum
`dataUC (psiAtC s ψ̂)` of the step with the block datum `D`, for every datum `D` of the chart with
`h = h₀`.  These are the arguments of the class terms `ℰ^{(j)}`, `ℳ^{(j)}` in `WoneC`, `WtwoC`. -/
theorem exists_analytic_composedPairAtC_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) (j : ℕ) :
    ∃ P : RawData d L (N₁ * L ^ m₁) (k + 1) N →
        Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      AnalyticOnNhd ℂ P (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        P (rawOf D) = composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)) := by
  classical
  obtain ⟨g, F, hgan, hFan, hgF⟩ := exists_analytic_oldSpin hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7
    hR hsmR hMX hdm hα hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hp₁.le
    (by rwa [S.norm_betaU_rpow hβ]) (S.norm_smul_yhat_le hp₁ hs hx)
  have hval : ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
      XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      rawOf ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)) = g (rawOf D) ∧
      F (rawOf D) = (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)),
        bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
          ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x))) := fun D hD hX =>
    hgF D hX ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x))
      (fun z i => by rw [(S.withDatum D hD).dataUC_h]; exact (hD z i).symm)
      ((S.withDatum D hD).compTangent_psiAtC s x)
  by_cases hj : j ≤ k
  · refine ⟨fun Θ => ((fun y i => composeField
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
          (hj.trans (Nat.le_succ k))) (stepG d L N₁ m₁ k ϱ) S.a (F Θ).1 (g Θ).1 y i),
      (fun y i => if y ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
          (hj.trans (Nat.le_succ k))).Ω 1 then (g Θ).2 y i else 0)), ?_, fun D hD hX => ?_⟩
    · intro Θ hΘ
      have hgat := hgan Θ hΘ
      have hFat := hFan Θ hΘ
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_)
        (analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_)
      · exact analyticAt_composeField (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) j (hj.trans (Nat.le_succ k))) (G' := stepG d L N₁ m₁ k ϱ) S.a
          (fun Θ => (F Θ).1) (fun Θ => (g Θ).1)
          (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hFat) r)
          (fun y' j' => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_fst.comp hgat) y') j')
          y i
      · by_cases hy : y ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
            j (hj.trans (Nat.le_succ k))).Ω 1
        · simp only [hy, ↓reduceIte]
          exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_snd.comp hgat) y) i
        · simp only [hy, ↓reduceIte]
          exact analyticAt_const
    · obtain ⟨hg, hF⟩ := hval D hD hX
      unfold composedPairAtC
      simp only [hj, ↓reduceDIte]
      show ((fun y i => composeField _ (stepG d L N₁ m₁ k ϱ) S.a (F (rawOf D)).1
          (g (rawOf D)).1 y i),
        (fun y i => if y ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
          (ϱ := ϱ) j (hj.trans (Nat.le_succ k))).Ω 1 then (g (rawOf D)).2 y i else 0)) = _
      rw [hF, ← hg]
      rfl
  · refine ⟨fun _ => (0, 0), fun _ _ => analyticAt_const, fun D hD hX => ?_⟩
    unfold composedPairAtC
    simp only [hj, ↓reduceDIte]

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **A sum of functions of the composed data of the path, as a function of the block datum**: for
functions `Φ j` of the pair `(ψ_k^{(j)}, h)`, one function of the raw data returns
`∑_{j=1}^k Φ_j(ψ_k^{(j)}(ψ), h)` at the complex old spin `ψ = psiAtC s ψ̂` of the step with the
datum `D`, for every datum `D` of the chart with `h = h₀`, and is analytic at `rawOf D` as soon as
every `Φ j` is analytic at the composed pair there. -/
theorem exists_composite_path_family
    (Φ : ℕ → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = ∑ j ∈ Finset.Icc 1 k, Φ j (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x))) ∧
        ((∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ (Φ j) (composedPairAtC S.a S.ν (Nat.le_succ k) j
          ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)))) →
          AnalyticAt ℂ F (rawOf D)) := by
  choose P hPan hP using fun j => S.exists_analytic_composedPairAtC_path hC hMX hdm hα hsm ha₁ hc7
    hR hsmR hβ hp₁ hδ₁ hs hx j
  refine ⟨fun Θ => ∑ j ∈ Finset.Icc 1 k, Φ j (P j Θ), fun D hD hX => ⟨?_, fun hΦ => ?_⟩⟩
  · exact Finset.sum_congr rfl fun j _ => by rw [hP j D hD hX]
  · exact Finset.analyticAt_fun_sum _ fun j hj =>
      (hΦ j hj).comp_of_eq (hPan j _ ⟨D, hX, rfl⟩) (hP j D hD hX)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **`W₁` of the complex step as a function of the block datum** (FLUCTUATION §2.6, (2.6); the
analyticity (H.2) of the class).  For `s ∈ [0,1]` and `χ_fl(ψ̂) = 1`, one function of the raw data
returns `WoneC C s ψ̂` of the step with the datum `D`, for every datum `D` of the chart with
`h = h₀`, and it is analytic at `rawOf D` if the densities `ℰ^{(j)}` (`Edens`, `1 ≤ j ≤ k`) of the
class are analytic at the composed data `(ψ_k^{(j)}, h)` of the path point `ψ^{(k)} + s ψ'` and of
the critical point `ψ^{(k)}`.  The potential part needs no such premise
(`exists_analytic_VkC_path`). -/
theorem exists_analyticAt_WoneC_of_analyticAt_Edens {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).WoneC C s x ∧
        ((∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
            (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
              Edens C.m₀ C.Tm j p.1 p.2)
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)))) →
          (∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
            (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
              Edens C.m₀ C.Tm j p.1 p.2)
            (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.withDatum D hD).psiKdC)) →
          AnalyticAt ℂ F (rawOf D)) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  obtain ⟨FV, hFVan, hFV⟩ := S.exists_analytic_VkC_path hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    hδ₁ hs hx
  obtain ⟨FE, hFE⟩ := S.exists_composite_path_family hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁
    (fun j p => Edens C.m₀ C.Tm j p.1 p.2) hs hx
  obtain ⟨FE0, hFE0⟩ := S.exists_composite_path_family hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    hδ₁ (fun j p => Edens C.m₀ C.Tm j p.1 p.2) h0 hx
  refine ⟨fun Θ => -(S.β : ℂ) * FV Θ + (FE Θ - FE0 Θ), fun D hD hX => ?_⟩
  have e0 : (S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC 0 x) =
      (S.withDatum D hD).psiKdC :=
    (congrArg (S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC_zero x)).trans
      (S.withDatum D hD).dataUC_psi0C
  obtain ⟨hE, hEan⟩ := hFE D hD hX
  obtain ⟨hE0, hE0an⟩ := hFE0 D hD hX
  rw [e0] at hE0 hE0an
  refine ⟨?_, fun h1 h2 => ?_⟩
  · have hd := (S.withDatum D hD).dEC_eq C ((S.withDatum D hD).psiAtC s x)
    show -(S.β : ℂ) * FV (rawOf D) + (FE (rawOf D) - FE0 (rawOf D)) =
      -((S.withDatum D hD).β : ℂ) * (S.withDatum D hD).VkC ((S.withDatum D hD).psiAtC s x) +
        (S.withDatum D hD).dEC C ((S.withDatum D hD).psiAtC s x)
    rw [hd, hFV D hD hX, hE, hE0]
    rfl
  · exact (analyticAt_const.mul (hFVan _ ⟨D, hX, rfl⟩)).add ((hEan h1).sub (hE0an h2))

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **`W₂` of the complex step as a function of the block datum** (FLUCTUATION §2.6, (2.6); the
analyticity (H.7) of the class).  For `t ∈ [0,1]`, `χ_fl(ψ̂) = 1` and a source `g`, one function of
the raw data returns `WtwoC C g t ψ̂` of the step with the datum `D`, for every datum `D` of the
chart with `h = h₀`, and it is analytic at `rawOf D` if the terms `ℱ^{(j)}(·, ·, g)` (`Floc`,
`1 ≤ j ≤ k`) of the class are analytic at the composed data `(ψ_k^{(j)}, h)` of the path point
`ψ^{(k)} + t ψ'` and of the critical point `ψ^{(k)}`.  The direct part `⟨g, φ_k(ψ)⟩₁` needs no such
premise (`exists_analytic_bgC_path`). -/
theorem exists_analyticAt_WtwoC_of_analyticAt_Floc (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) = (S.withDatum D hD).WtwoC C g t x ∧
        ((∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
            (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
              Floc C.m₀ C.Tm j p.1 p.2 g)
            (composedPairAtC S.a S.ν (Nat.le_succ k) j
              ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC t x)))) →
          (∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
            (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
              Floc C.m₀ C.Tm j p.1 p.2 g)
            (composedPairAtC S.a S.ν (Nat.le_succ k) j (S.withDatum D hD).psiKdC)) →
          AnalyticAt ℂ F (rawOf D)) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.2 zero_le_one
  obtain ⟨B, hBan, hB⟩ := S.exists_analytic_bgC_path hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁
    ht hx
  obtain ⟨B0, hB0an, hB0⟩ := S.exists_analytic_bgC_path hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    hδ₁ h0 hx
  obtain ⟨FF, hFF⟩ := S.exists_composite_path_family hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁
    (fun j p => Floc C.m₀ C.Tm j p.1 p.2 g) ht hx
  obtain ⟨FF0, hFF0⟩ := S.exists_composite_path_family hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁
    hδ₁ (fun j p => Floc C.m₀ C.Tm j p.1 p.2 g) h0 hx
  -- the direct part `⟨g, φ_k(ψ)⟩₁`
  have hdir : ∀ {B : RawData d L (N₁ * L ^ m₁) (k + 1) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)}
      {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}, AnalyticAt ℂ B Θ →
      AnalyticAt ℂ (fun Θ => ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        svec (stepG d L N₁ m₁ k ϱ) (B Θ).1 y i) Θ := fun {B Θ} hBat =>
    Finset.analyticAt_fun_sum _ fun y _ => Finset.analyticAt_fun_sum _ fun i _ =>
      analyticAt_const.mul (analyticAt_svec (G' := stepG d L N₁ m₁ k ϱ) (fun Θ => (B Θ).1)
        (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hBat) r) y i)
  refine ⟨fun Θ => ((∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
      svec (stepG d L N₁ m₁ k ϱ) (B Θ).1 y i) + FF Θ) -
    ((∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
      svec (stepG d L N₁ m₁ k ϱ) (B0 Θ).1 y i) + FF0 Θ), fun D hD hX => ?_⟩
  have e0 : (S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC 0 x) =
      (S.withDatum D hD).psiKdC :=
    (congrArg (S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC_zero x)).trans
      (S.withDatum D hD).dataUC_psi0C
  obtain ⟨hF, hFan⟩ := hFF D hD hX
  obtain ⟨hF0, hF0an⟩ := hFF0 D hD hX
  have hB0' := hB0 D hD hX
  rw [e0] at hF0 hF0an hB0'
  refine ⟨?_, fun h1 h2 => ?_⟩
  · show ((∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        svec (stepG d L N₁ m₁ k ϱ) (B (rawOf D)).1 y i) + FF (rawOf D)) -
      ((∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i *
        svec (stepG d L N₁ m₁ k ϱ) (B0 (rawOf D)).1 y i) + FF0 (rawOf D)) = _
    rw [hB D hD hX, hB0', hF, hF0]
    have hd := (S.withDatum D hD).dFC_eq C g ((S.withDatum D hD).psiAtC t x)
    show _ = (S.withDatum D hD).dFC C g ((S.withDatum D hD).psiAtC t x)
    rw [hd]
    rfl
  · exact ((hdir (hBan _ ⟨D, hX, rfl⟩)).add (hFan h1)).sub
      ((hdir (hB0an _ ⟨D, hX, rfl⟩)).add (hF0an h2))

end Path

end StepSetting

end Balaban.Fluctuation
