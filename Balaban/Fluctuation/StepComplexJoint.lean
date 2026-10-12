/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexSource
public import Balaban.LargeField.R.PsiZeroAnalyticAction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The complex step as a jointly analytic function of the block datum and the hat variable

`StepComplexAnalytic`, `StepComplexExponent` give, for each fixed fluctuation variable `ψ̂`, a
function of the raw block datum `Θ = (θ, h̃)` which is analytic on the chart and returns the object
of the complex step.  To integrate over `ψ̂` and keep analyticity in `Θ` one needs these functions
for all `ψ̂` at once, with joint regularity.  This file gives them as functions on
`Q = RawData × (ℂ^N)^{T^{(k)}_1}`, jointly analytic at every point `(Θ, ψ̂)` with `Θ` in the chart
`Ξ^c(𝔹_{k+1}; 1, ε)` and `|ψ̂(b)_i| ≤ p⁺`:

* `exists_oldSpin_of_hat`: for a datum of the chart and every complex hat variable bounded by
  `c_ψ`, the old spin with tangent `hatLift cc θ ψ̂` exists in `𝒟(𝔹_k)`, with raw data given by the
  critical point and the square root (`hreal_level`; the existence part of
  `exists_analytic_oldSpin`, uniformly in the hat variable);
* `StepSetting.psiHat`: the complex old spin `ψ^{(k)}(θ) + β_k^{-1/2} C^{(k)1/2}(θ) ψ̂` of a complex
  hat variable (`psiAtC s ψ̂ = psiHat (s ψ̂)`);
* `StepSetting.JointRep`: a bundle of analytic representatives (the background of `θ`, the square
  root `C^{(k)1/2}`, the critical point, the small solution of `𝔹_k`) with their specifications on
  the chart; `nonempty_jointRep`: it exists under the hypotheses of the complex chart;
* for `Jr : JointRep`: the joint functions `Jr.gJ` (raw data of the old spin), `Jr.FJ` (its small
  solution), `Jr.VJ` (the interaction `V^{(k)}`), `Jr.PJ j` (the composed pairs `(ψ_k^{(j)}, h)` of
  (H.2)), `Jr.EJ`, `Jr.FcJ`, `Jr.McJ` (the composites `ℰ_k`, `ℱ_k`, `ℳ_k`), `Jr.W1`, `Jr.W2` (the
  exponents of `μ_{s,t}`), `Jr.tKJ`, `Jr.rhoJ` (the kernel `∏ t_k` and the density `ρ_k`), with
  - their values at `(rawOf θ, ψ̂)` for the block datum `θ` of the step, in the chart: the objects of
    the complex step at the old spin `psiHat ψ̂` (`VJ_eq`, `W1_eq`, `W1_path`, …), and, since the
    bundle does not depend on the block datum (`JointRep.withDatum`), for the step with any datum
    `D` of the chart with `h = h₀` (`W1_withDatum`, `W2_withDatum`, `McJ_withDatum`, …);
  - their joint analyticity at `(Θ, ψ̂)`, `Θ` in the chart (`analyticAt_VJ`, `analyticAt_W1`, …);
    for the class terms it is conditional on the analyticity of `ℰ^{(j)}`, `ℱ^{(j)}`, `ℳ^{(j)}` at
    the composed pairs `Jr.PJ j (Θ, ψ̂)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section JointTangent

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

include hC hk ha₁ H hc7 hR hsmR hMX hdm hα hsm hcψ hδ₁ in
/-- **The old spin with tangent `hatLift cc D' ψ̂` exists in the domain `𝒟(𝔹_k)`, with raw data
given by the critical point and the square root** (`hreal_level`; the existence part of
`exists_analytic_oldSpin`, uniformly in the hat variable): for a datum `D'` of the chart and every
complex hat variable with `|ψ̂(b)_i| ≤ c_ψ`, there is a datum `D₀` of level `k` in `𝒟(𝔹_k)` with
`D₀.Ψ = ψ^{(k)}(D') + liftC (cc • C^{1/2}(D') ψ̂)` and `D₀.h = D'.h`. -/
theorem exists_oldSpin_of_hat {D' : BgData Gp N}
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D') {ψh : unitPts Gp × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    ∃ D₀ : BgData Hm N, InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν D₀ ∧
      (D₀.Ψ, D₀.h) =
        ((fun z i => (composeData (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ z i +
          liftC hG' (cc • (hatCovSqrt Gp a₁ ν D' *ᵥ ψh)) z i), D'.h) := by
  have hψ := hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD' hψh
  obtain ⟨D₀, hDh, hDt, -⟩ := hreal_level hC hG hG' (le_refl (k + 1)) ha₁ H hc7
    (R := R) (by linarith) hsmR D' hD' _ hψ.1 hψ.2
  have hdom := inUnionDomainC_of_tangent_hatLift hC hk hG hG' ha₁ H hc7 hR hsmR hMX hdm hα hsm
    cc hcψ hδ₁ hψh hD' hDh hDt
  refine ⟨D₀, hdom, Prod.ext ?_ ?_⟩
  · funext z i
    have h2 := congrFun (congrFun hDt z) i
    simp only [compTangent] at h2
    have h3 : hatLift Gp a₁ ν hG' cc D' ψh z i =
        liftC hG' (cc • (hatCovSqrt Gp a₁ ν D' *ᵥ ψh)) z i := rfl
    show D₀.Ψ z i = _ + liftC hG' (cc • (hatCovSqrt Gp a₁ ν D' *ᵥ ψh)) z i
    linear_combination h2 + h3
  · funext z i
    exact hDh z i

end JointTangent

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Localization Balaban.LargeField Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)

/-! ### The complex old spin of a complex hat variable -/

/-- **The complex old spin of a complex hat variable**:
`ψ = ψ^{(k)}(θ) + β_k^{-1/2} C^{(k)1/2}(θ) ψ̂` for `ψ̂ ∈ (ℂ^N)^{T^{(k)}_1}`.  On the path of the
interpolation, `psiAtC s ψ̂ = psiHat (s ψ̂)` (`psiAtC_eq_psiHat`). -/
noncomputable def psiHat (ψh : S.EC) : S.EC := S.psi0C + S.hatField S.covSqrtC ψh

theorem psiHat_zero : S.psiHat 0 = S.psi0C := by
  unfold psiHat hatField
  rw [Matrix.mulVec_zero, smul_zero, add_zero]

theorem psiAtC_eq_psiHat (s : ℝ) (x : S.E) : S.psiAtC s x = S.psiHat ((s : ℂ) • yhat x) := by
  unfold psiAtC psiHat
  rw [S.shiftUC_eq_hatField]
  unfold hatField
  rw [Matrix.mulVec_smul, smul_comm]

theorem psiHat_yhat (x : S.E) : S.psiHat (yhat x) = S.psiAtC 1 x := by
  rw [S.psiAtC_eq_psiHat, Complex.ofReal_one, one_smul]

/-- The tangent of the datum of `psiHat ψ̂` is the fluctuation field of the hat engine. -/
theorem compTangent_psiHat (ψh : S.EC) :
    compTangent S.hG S.hG' (le_refl (k + 1)) S.a (bgFieldC S.G' S.a S.ν (bgC0 d L N) S.D') S.D'
      (S.dataUC (S.psiHat ψh)) =
      hatLift S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) S.D' ψh := by
  rw [S.compTangent_dataUC, S.hatLift_eq_liftC]
  congr 1
  unfold psiHat hatField
  abel

/-- The raw data of the datum of `psiHat ψ̂`: the critical point plus the lift of the hat field,
and the field `h` of the block datum. -/
theorem rawOf_dataUC_psiHat (ψh : S.EC) :
    ((S.dataUC (S.psiHat ψh)).Ψ, (S.dataUC (S.psiHat ψh)).h) =
      ((fun z i => S.psiKdC.Ψ z i +
        liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (S.covSqrtC *ᵥ ψh)) z i), S.D'.h) := by
  refine Prod.ext ?_ ?_
  · funext z i
    have h0 : S.psiKdC.Ψ z i = S.psi0C (unitPt S.hG' z, i) := by
      rw [← S.dataUC_psi0C, S.dataUC_Ψ]
    show (S.dataUC (S.psiHat ψh)).Ψ z i = S.psiKdC.Ψ z i + _
    rw [S.dataUC_Ψ, h0]
    rfl
  · funext z i
    show (S.dataUC (S.psiHat ψh)).h z i = S.D'.h z i
    rw [S.dataUC_h, S.hh₀]


/-! ### The bundle of analytic representatives -/

/-- **Analytic representatives of the backgrounds of the complex step on the chart**
`Ξ^c(𝔹_{k+1}; 1, ε)`, for hat variables bounded by `p⁺`: functions of the raw block datum
`Θ = (θ, h̃)` which are analytic on the chart and return

* `F₀`: the complex small solution `(φ_{k+1}, α_{k+1})(θ)` (Theorem 7.2);
* `Mx`: the square root `C^{(k)1/2}(θ)` (RAY-CHART §1);
* `Pc`: the critical point `ψ^{(k)}(θ)` of (2.1);

the analytic function `Fb` of the raw data of level `k` which returns the small solution
`(φ_k, α_k)` on `𝒟(𝔹_k)`; the inclusion `dom` of the old spins
`ψ^{(k)}(θ) + β_k^{-1/2} C^{(k)1/2}(θ) ψ̂`, `|ψ̂(b)_i| ≤ p⁺`, in `𝒟(𝔹_k)` (FLUCTUATION Lemma 2.3 (d));
and the invertibility of `H_k` and of the constraint form at the background of `θ`.  It exists
under the hypotheses of the complex chart (`nonempty_jointRep`). -/
structure JointRep (eps pp : ℝ) where
  F₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)
  Mx : RawData d L (N₁ * L ^ m₁) (k + 1) N → Matrix (S.U × Fin N) (S.U × Fin N) ℂ
  Pc : RawData d L (N₁ * L ^ m₁) (k + 1) N → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ
  Fb : RawData d L (N₁ * L ^ m₁) (k + 1) N →
    ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ)
  hpp : 0 ≤ pp
  F₀_an : AnalyticOnNhd ℂ F₀ (XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
  F₀_eq : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    F₀ (rawOf D) = (bgFieldC S.G' S.a S.ν (bgC0 d L N) D, bgMultC S.G' S.a S.ν (bgC0 d L N) D)
  Mx_an : ∀ p q, AnalyticOnNhd ℂ (fun Θ => Mx Θ p q) (XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
  Mx_eq : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    Mx (rawOf D) = hatCovSqrt S.G' S.a₁ S.ν D
  Pc_an : ∀ x i, AnalyticOnNhd ℂ (fun Θ => Pc Θ x i) (XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
  Pc_eq : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    Pc (rawOf D) = (composeData (S.hG.precedes S.hG' (le_refl (k + 1))) S.a
      (bgFieldC S.G' S.a S.ν (bgC0 d L N) D) D).Ψ
  Fb_an : AnalyticOnNhd ℂ Fb {p | ∃ D : BgData (stepG d L N₁ m₁ k ϱ) N,
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)}
  Fb_eq : ∀ D : BgData (stepG d L N₁ m₁ k ϱ) N,
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν D →
    Fb (D.Ψ, D.h) = (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D,
      bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N) D)
  dom : ∀ D' : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D' →
    ∀ ψh : S.EC, (∀ p, ‖ψh p‖ ≤ pp) →
      ∃ D₀ : BgData (stepG d L N₁ m₁ k ϱ) N,
        InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν D₀ ∧
        (D₀.Ψ, D₀.h) = ((fun z i => Pc (rawOf D') z i +
          liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (Mx (rawOf D') *ᵥ ψh)) z i), D'.h)
  unitH : ∀ D' : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D' →
    IsUnit (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
      (bgMultC S.G' S.a S.ν (bgC0 d L N) D'))
  unitM : ∀ D' : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D' →
    IsUnit (constraintForm
      (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D'))⁻¹
      (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
        (bgFieldC S.G' S.a S.ν (bgC0 d L N) D')))

section Exists

variable {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
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

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hpp hδ₁ in
/-- **`JointRep` is inhabited** under the hypotheses of the complex chart of RAY-CHART §1 (`FlCore`,
the margins of the covariance chart and of the ray with `p⁺`): Theorem 7.2 (analyticity) at the
levels `k + 1` and `k`, the analytic square root, the analytic critical point, and `hreal_level`. -/
theorem nonempty_jointRep : Nonempty (S.JointRep eps pp) := by
  obtain ⟨F₀, hF₀an, hF₀⟩ := exists_analytic_bgC hC
  obtain ⟨M, hMan, hM⟩ := exists_analytic_hatCovSqrt hC S.hk1 hMX hdm hα hsm
  obtain ⟨Pc, hPcan, hPc⟩ := exists_analytic_composeField hC
    (S.hG.precedes S.hG' (le_refl (k + 1)))
  obtain ⟨F, hFan, hF⟩ := theorem72_analytic (G := stepG d L N₁ m₁ k ϱ) (a := S.a) (ν := S.ν)
    (N := N) hC.HBp
  have hunit : ∀ D' : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D' →
      IsUnit (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D')) ∧
      IsUnit (constraintForm
        (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
          (bgMultC S.G' S.a S.ν (bgC0 d L N) D'))⁻¹
        (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) D'))) := by
    intro D' hD'
    have hD'2 : InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν D' :=
      (isDecBg_one_of_xiCData hC hD').2.mono (hc7.trans (thm73C3_le_thm73C2 d L N))
    obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ S.hG S.hG' (le_refl (k + 1)) hC.HBp hC.HBp D'
      hD'2
    have hΦ' : restrictField (stepG d L N₁ m₁ k ϱ) Φ =
        fieldBase (S.hG.precedes S.hG' (le_refl (k + 1)))
          (bgFieldC S.G' S.a S.ν (bgC0 d L N) D') := funext fun x => funext fun i => hΦ x i
    refine ⟨dirichletOperator_isUnit (stepG d L N₁ m₁ k ϱ) St.pos St.mass St.weights _ St.alpha,
      ?_⟩
    rw [← hΦ']
    exact constraintForm_isUnit St
  exact ⟨{
    F₀ := F₀
    Mx := M
    Pc := Pc
    Fb := F
    hpp := hpp.le
    F₀_an := hF₀an
    F₀_eq := hF₀
    Mx_an := hMan
    Mx_eq := hM
    Pc_an := hPcan
    Pc_eq := hPc
    Fb_an := hFan
    Fb_eq := hF
    dom := fun D' hD' ψh hψh => by
      rw [hPc D' hD', hM D' hD']
      exact exists_oldSpin_of_hat hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR hMX hdm hα hsm _
        hpp.le (by rwa [S.norm_betaU_rpow hβ]) hD' hψh
    unitH := fun D' hD' => (hunit D' hD').1
    unitM := fun D' hD' => (hunit D' hD').2 }⟩

end Exists


/-! ### The joint functions -/

section Helpers

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A function of the first variable, analytic there, is analytic on the product. -/
theorem analyticAt_comp_fst' {f : E → G} {p : E × F} (h : AnalyticAt ℂ f p.1) :
    AnalyticAt ℂ (fun q : E × F => f q.1) p :=
  h.comp_of_eq analyticAt_fst rfl

/-- A function of the second variable, analytic there, is analytic on the product. -/
theorem analyticAt_comp_snd' {f : F → G} {p : E × F} (h : AnalyticAt ℂ f p.2) :
    AnalyticAt ℂ (fun q : E × F => f q.2) p :=
  h.comp_of_eq analyticAt_snd rfl

end Helpers

namespace JointRep

variable {S} {eps pp : ℝ} (Jr : S.JointRep eps pp)

/-- The raw data `(Ψ, h̃)` of the old spin `ψ^{(k)}(θ) + β_k^{-1/2} C^{(k)1/2}(θ) ψ̂`, as a function
of the raw block datum and the hat variable. -/
noncomputable def gJ (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    RawData d L (N₁ * L ^ m₁) (k + 1) N :=
  ((fun z i => Jr.Pc q.1 z i +
    liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (Jr.Mx q.1 *ᵥ q.2)) z i), q.1.2)

/-- The small solution `(φ_k(ψ), α_k(ψ))` of the old spin, as a function of the raw block datum and
the hat variable. -/
noncomputable def FJ (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ) :=
  Jr.Fb (Jr.gJ q)

/-- The interaction `V^{(k)}` of (2.4), as a function of the raw block datum and the hat
variable. -/
noncomputable def VJ (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν (Jr.F₀ q.1).2 (Jr.F₀ q.1).1
    (liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (Jr.Mx q.1 *ᵥ q.2)))
    ((Jr.FJ q).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (Jr.F₀ q.1).1)

open Classical in
/-- The composed pair `(ψ_k^{(j)}, h)` of (H.2) of the old spin, as a function of the raw block
datum and the hat variable. -/
noncomputable def PJ (j : ℕ) (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N :=
  if hj : j ≤ k then
    ((fun y i => composeField
        (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
          (hj.trans (Nat.le_succ k))) (stepG d L N₁ m₁ k ϱ) S.a (Jr.FJ q).1 (Jr.gJ q).1 y i),
      (fun y i => if y ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) j
          (hj.trans (Nat.le_succ k))).Ω 1 then (Jr.gJ q).2 y i else 0))
  else (0, 0)

/-- The composite `ℰ_k` of (H.2), as a function of the raw block datum and the hat variable. -/
noncomputable def EJ (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k, Edens C.m₀ C.Tm j (Jr.PJ j q).1 (Jr.PJ j q).2

/-- The composite `ℱ_k` of (H.7), as a function of the raw block datum and the hat variable. -/
noncomputable def FcJ (g : Fld d L N₁ m₁ (k + 1) N)
    (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  (∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i, g y i * svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ q).1 y i) +
    ∑ j ∈ Finset.Icc 1 k, Floc C.m₀ C.Tm j (Jr.PJ j q).1 (Jr.PJ j q).2 g

/-- The component `(y, i)` of the composite `ℳ_k` of (H.7), as a function of the raw block datum
and the hat variable. -/
noncomputable def McJ (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ q).1 y i +
    ∑ j ∈ Finset.Icc 1 k, Mloc C.m₀ C.Tm j y (Jr.PJ j q).1 (Jr.PJ j q).2 g i

/-- The exponent `W₁ = -β_k V^{(k)} + δℰ_k` of (2.6), as a function of the raw block datum and the
hat variable. -/
noncomputable def W1 (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  -(S.β : ℂ) * Jr.VJ q + (Jr.EJ C q - Jr.EJ C (q.1, 0))

/-- The exponent `W₂ = δℱ_k(·, g)` of (2.6), as a function of the raw block datum and the hat
variable. -/
noncomputable def W2 (g : Fld d L N₁ m₁ (k + 1) N)
    (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  Jr.FcJ C g q - Jr.FcJ C g (q.1, 0)

/-- The kernel `∏ t_k` of Definition 2.1, as a function of the raw block datum and the hat
variable. -/
noncomputable def tKJ (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  (((S.cKernel / (2 * Real.pi)) ^ ((N : ℝ) * S.nBlocks / 2) : ℝ) : ℂ) *
    Complex.exp (-((S.β : ℂ) * couplingC S.G' S.a₁ (k + 1) q.1.1 (Jr.gJ q).1))

/-- The exponential of the density `ρ_k` of (H.1), as a function of the raw block datum and the hat
variable. -/
noncomputable def rhoJ (g : Fld d L N₁ m₁ (k + 1) N)
    (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) : ℂ :=
  Complex.exp (-(S.β : ℂ) *
      actionRawC (stepG d L N₁ m₁ k ϱ) S.a S.ν (Jr.gJ q).1 (Jr.gJ q).2 (Jr.FJ q).1 +
    Jr.EJ C q - (C.Ek : ℂ) * (S.nU : ℂ) + Jr.FcJ C g q)

/-! ### Values at the block datum of the step -/

section Values

variable (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp)

include hX in
theorem gJ_eq (ψh : S.EC) : Jr.gJ (rawOf S.D', ψh) =
    rawOf (S.dataUC (S.psiHat ψh)) := by
  have h := S.rawOf_dataUC_psiHat ψh
  have hc := S.covSqrtC_eq_hatCovSqrt
  unfold gJ
  dsimp only
  rw [Jr.Pc_eq S.D' hX, Jr.Mx_eq S.D' hX]
  show _ = ((S.dataUC (S.psiHat ψh)).Ψ,
    (S.dataUC (S.psiHat ψh)).h)
  rw [h, hc]
  rfl

include Jr hX hψh in
/-- The old spin of a bounded hat variable lies in the domain `𝒟(𝔹_k)` of the small solution. -/
theorem dataUC_psiHat_dom :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiHat ψh)) := by
  obtain ⟨D₀, hdom, hraw⟩ := Jr.dom S.D' hX ψh hψh
  have h1 : rawOf D₀ = rawOf (S.dataUC (S.psiHat ψh)) := by
    rw [← Jr.gJ_eq hX ψh]
    exact hraw
  rw [← BgData.eq_of_raw h1]
  exact hdom

include hX hψh in
theorem FJ_eq : Jr.FJ (rawOf S.D', ψh) =
    (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (S.dataUC (S.psiHat ψh)),
      bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
        (S.dataUC (S.psiHat ψh))) := by
  unfold FJ
  rw [Jr.gJ_eq hX ψh]
  exact Jr.Fb_eq _ (Jr.dataUC_psiHat_dom hX hψh)

include hX hψh in
theorem VJ_eq : Jr.VJ (rawOf S.D', ψh) = S.VkC (S.psiHat ψh) := by
  unfold VJ VkC
  dsimp only
  rw [Jr.FJ_eq hX hψh, Jr.F₀_eq S.D' hX, Jr.Mx_eq S.D' hX, S.compTangent_psiHat]
  rfl

include hX hψh in
theorem PJ_eq (j : ℕ) : Jr.PJ j (rawOf S.D', ψh) =
    composedPairAtC S.a S.ν (Nat.le_succ k) j
      (S.dataUC (S.psiHat ψh)) := by
  unfold PJ composedPairAtC
  by_cases hj : j ≤ k
  · simp only [hj, ↓reduceDIte]
    rw [Jr.FJ_eq hX hψh, Jr.gJ_eq hX ψh]
    rfl
  · simp only [hj, ↓reduceDIte]

include hX hψh in
theorem EJ_eq : Jr.EJ C (rawOf S.D', ψh) =
    EcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
      (S.dataUC (S.psiHat ψh)) := by
  unfold EJ EcompAtC
  simp only [Jr.PJ_eq hX hψh]

include hX hψh in
theorem FcJ_eq (g : Fld d L N₁ m₁ (k + 1) N) : Jr.FcJ C g (rawOf S.D', ψh) =
    FcompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
      (S.dataUC (S.psiHat ψh)) g := by
  unfold FcJ FcompAtC
  simp only [Jr.PJ_eq hX hψh, Jr.FJ_eq hX hψh]

include hX hψh in
theorem McJ_eq (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    Jr.McJ C g y i (rawOf S.D', ψh) =
      McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataUC (S.psiHat ψh)) g y i := by
  unfold McJ McompAtC
  simp only [Jr.PJ_eq hX hψh, Jr.FJ_eq hX hψh]

include Jr in
theorem zero_le_pp (p : S.U × Fin N) : ‖(0 : S.EC) p‖ ≤ pp := by
  simpa using Jr.hpp

include hX hψh in
theorem W1_eq : Jr.W1 C (rawOf S.D', ψh) =
    -(S.β : ℂ) * S.VkC (S.psiHat ψh) +
      S.dEC C (S.psiHat ψh) := by
  unfold W1 dEC
  dsimp only
  rw [Jr.VJ_eq hX hψh, Jr.EJ_eq C hX hψh, Jr.EJ_eq C hX Jr.zero_le_pp,
    S.psiHat_zero]

include hX hψh in
theorem W2_eq (g : Fld d L N₁ m₁ (k + 1) N) : Jr.W2 C g (rawOf S.D', ψh) =
    S.dFC C g (S.psiHat ψh) := by
  unfold W2 dFC
  dsimp only
  rw [Jr.FcJ_eq C hX hψh, Jr.FcJ_eq C hX Jr.zero_le_pp, S.psiHat_zero]

include hX in
theorem tKJ_eq (ψh : S.EC) : Jr.tKJ (rawOf S.D', ψh) =
    S.tKernelC (S.psiHat ψh) := by
  unfold tKJ tKernelC
  dsimp only
  rw [Jr.gJ_eq hX ψh]
  rfl

include hX hψh in
theorem rhoJ_eq (g : Fld d L N₁ m₁ (k + 1) N) : Jr.rhoJ C g (rawOf S.D', ψh) =
    S.rhoExpC C g (S.psiHat ψh) := by
  unfold rhoJ rhoExpC AoldC
  rw [Jr.EJ_eq C hX hψh, Jr.FcJ_eq C hX hψh, Jr.FJ_eq hX hψh, Jr.gJ_eq hX ψh]
  rfl

/-- On the ray, the hat variable `s ψ̂` is bounded by `|s| ‖ψ̂‖`. -/
theorem smul_yhat_le {s : ℝ} {x : S.E} (h : |s| * ‖x‖ ≤ pp) (p : S.U × Fin N) :
    ‖((s : ℂ) • yhat x) p‖ ≤ pp :=
  (S.norm_smul_yhat_le_mul s x p).trans h

include hX in
/-- **`W₁` of the complex step on the path is the joint exponent at the hat variable `s ψ̂`.** -/
theorem W1_path {s : ℝ} {x : S.E} (h : |s| * ‖x‖ ≤ pp) :
    Jr.W1 C (rawOf S.D', (s : ℂ) • yhat x) = S.WoneC C s x := by
  rw [Jr.W1_eq C hX (smul_yhat_le h), ← S.psiAtC_eq_psiHat]
  rfl

include hX in
/-- **`W₂` of the complex step on the path is the joint exponent at the hat variable `t ψ̂`.** -/
theorem W2_path (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ} {x : S.E} (h : |t| * ‖x‖ ≤ pp) :
    Jr.W2 C g (rawOf S.D', (t : ℂ) • yhat x) = S.WtwoC C g t x := by
  rw [Jr.W2_eq C hX (smul_yhat_le h), ← S.psiAtC_eq_psiHat]
  rfl

include hX in
/-- The component of `ℳ_k` on the path is the joint function at the hat variable `t ψ̂`. -/
theorem McJ_path (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {t : ℝ} {x : S.E} (h : |t| * ‖x‖ ≤ pp) :
    Jr.McJ C g y i (rawOf S.D', (t : ℂ) • yhat x) =
      McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataUC (S.psiAtC t x)) g y i := by
  rw [Jr.McJ_eq C hX (smul_yhat_le h), ← S.psiAtC_eq_psiHat]

include hX in
/-- The composed pairs of the path point are the joint functions at the hat variable `s ψ̂`. -/
theorem PJ_path (j : ℕ) {s : ℝ} {x : S.E} (h : |s| * ‖x‖ ≤ pp) :
    Jr.PJ j (rawOf S.D', (s : ℂ) • yhat x) =
      composedPairAtC S.a S.ν (Nat.le_succ k) j (S.dataUC (S.psiAtC s x)) := by
  rw [Jr.PJ_eq hX (smul_yhat_le h), ← S.psiAtC_eq_psiHat]

include hX in
/-- The kernel `∏ t_k` on the contour of `TstepC` is the joint function at the hat variable `ψ̂`. -/
theorem tKJ_one (x : S.E) : Jr.tKJ (rawOf S.D', yhat x) = S.tKernelC (S.psiAtC 1 x) := by
  rw [Jr.tKJ_eq hX, S.psiHat_yhat]

include hX in
/-- The exponential of `ρ_k` on the contour of `TstepC` is the joint function at the hat variable
`ψ̂`. -/
theorem rhoJ_one (g : Fld d L N₁ m₁ (k + 1) N) {x : S.E} (h : ‖x‖ ≤ pp) :
    Jr.rhoJ C g (rawOf S.D', yhat x) = S.rhoExpC C g (S.psiAtC 1 x) := by
  have h1 : ∀ p : S.U × Fin N, ‖yhat x p‖ ≤ pp := fun p => by
    have := smul_yhat_le (S := S) (pp := pp) (s := 1) (x := x) (by simpa using h) p
    simpa using this
  rw [Jr.rhoJ_eq C hX h1, S.psiHat_yhat]

end Values

/-! ### The same representatives for the step with another block datum -/

/-- The bundle of analytic representatives does not depend on the block datum of the step: the
same functions represent the step with the datum `D`. -/
def withDatum (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) :
    (S.withDatum D hD).JointRep eps pp where
  F₀ := Jr.F₀
  Mx := Jr.Mx
  Pc := Jr.Pc
  Fb := Jr.Fb
  hpp := Jr.hpp
  F₀_an := Jr.F₀_an
  F₀_eq := Jr.F₀_eq
  Mx_an := Jr.Mx_an
  Mx_eq := Jr.Mx_eq
  Pc_an := Jr.Pc_an
  Pc_eq := Jr.Pc_eq
  Fb_an := Jr.Fb_an
  Fb_eq := Jr.Fb_eq
  dom := Jr.dom
  unitH := Jr.unitH
  unitM := Jr.unitM

section WithDatum

variable (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ))
  (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)

include hX in
theorem Mx_withDatum : Jr.Mx (rawOf D) = (S.withDatum D hD).covSqrtC :=
  (Jr.Mx_eq D hX).trans (S.withDatum D hD).covSqrtC_eq_hatCovSqrt.symm

include hX in
/-- **`W₁` of the step with the datum `D` on the path.** -/
theorem W1_withDatum {s : ℝ} {x : S.E} (h : |s| * ‖x‖ ≤ pp) :
    Jr.W1 C (rawOf D, (s : ℂ) • yhat x) = (S.withDatum D hD).WoneC C s x :=
  (Jr.withDatum D hD).W1_path C hX h

include hX in
/-- **`W₂` of the step with the datum `D` on the path.** -/
theorem W2_withDatum (g : Fld d L N₁ m₁ (k + 1) N) {t : ℝ} {x : S.E} (h : |t| * ‖x‖ ≤ pp) :
    Jr.W2 C g (rawOf D, (t : ℂ) • yhat x) = (S.withDatum D hD).WtwoC C g t x :=
  (Jr.withDatum D hD).W2_path C hX g h

include hX in
/-- The component of `ℳ_k` of the step with the datum `D` on the path. -/
theorem McJ_withDatum (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {t : ℝ} {x : S.E} (h : |t| * ‖x‖ ≤ pp) :
    Jr.McJ C g y i (rawOf D, (t : ℂ) • yhat x) =
      McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC t x)) g y i :=
  (Jr.withDatum D hD).McJ_path C hX g y i h

include hX in
/-- The composed pairs of the step with the datum `D` on the path. -/
theorem PJ_withDatum (j : ℕ) {s : ℝ} {x : S.E} (h : |s| * ‖x‖ ≤ pp) :
    Jr.PJ j (rawOf D, (s : ℂ) • yhat x) =
      composedPairAtC S.a S.ν (Nat.le_succ k) j
        ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)) :=
  (Jr.withDatum D hD).PJ_path hX j h

include hX in
/-- The kernel `∏ t_k` of the step with the datum `D` on the contour of `TstepC`. -/
theorem tKJ_withDatum (x : S.E) :
    Jr.tKJ (rawOf D, yhat x) = (S.withDatum D hD).tKernelC ((S.withDatum D hD).psiAtC 1 x) :=
  (Jr.withDatum D hD).tKJ_one hX x

include hX in
/-- The exponential of `ρ_k` of the step with the datum `D` on the contour of `TstepC`. -/
theorem rhoJ_withDatum (g : Fld d L N₁ m₁ (k + 1) N) {x : S.E} (h : ‖x‖ ≤ pp) :
    Jr.rhoJ C g (rawOf D, yhat x) =
      (S.withDatum D hD).rhoExpC C g ((S.withDatum D hD).psiAtC 1 x) :=
  (Jr.withDatum D hD).rhoJ_one C hX g h

end WithDatum


/-! ### Joint analyticity on the chart -/

section Analytic

variable {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
  (hΘ : Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps) {ψh : S.EC} (hψh : ∀ p, ‖ψh p‖ ≤ pp)

include hΘ in
theorem analyticAt_gJ (ψh : S.EC) : AnalyticAt ℂ Jr.gJ (Θ, ψh) := by
  unfold gJ
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun z => analyticAt_pi_iff.2 fun i => ?_)
    (analyticAt_comp_fst' (f := fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => Θ.2)
      (p := (Θ, ψh)) analyticAt_snd)
  refine (analyticAt_comp_fst' (p := (Θ, ψh)) (Jr.Pc_an z i Θ hΘ)).add ?_
  simp only [liftC_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun r _ => ?_)
  exact (analyticAt_comp_fst' (p := (Θ, ψh)) (Jr.Mx_an _ r Θ hΘ)).mul
    (analyticAt_comp_snd' (f := fun v : S.EC => v r) (p := (Θ, ψh))
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ) r).analyticAt ψh))

include hΘ hψh in
theorem analyticAt_FJ : AnalyticAt ℂ Jr.FJ (Θ, ψh) := by
  have hg := Jr.analyticAt_gJ hΘ ψh
  obtain ⟨D', hD', rfl⟩ := hΘ
  obtain ⟨D₀, hdom, hraw⟩ := Jr.dom D' hD' ψh hψh
  have hFb : AnalyticAt ℂ Jr.Fb (Jr.gJ (rawOf D', ψh)) :=
    Jr.Fb_an (Jr.gJ (rawOf D', ψh)) ⟨D₀, hdom, hraw.symm⟩
  exact hFb.comp hg

include hΘ hψh in
theorem analyticAt_VJ : AnalyticAt ℂ Jr.VJ (Θ, ψh) := by
  have hFJ := Jr.analyticAt_FJ hΘ hψh
  obtain ⟨D', hD', rfl⟩ := hΘ
  have hΘ' : rawOf D' ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps := ⟨D', hD', rfl⟩
  have hF₀ : AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC => Jr.F₀ q.1)
      (rawOf D', ψh) := analyticAt_comp_fst' (p := (rawOf D', ψh)) (Jr.F₀_an _ hΘ')
  unfold VJ
  refine analyticAt_interactionV (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν
    (αF := fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC => (Jr.F₀ q.1).2)
    (φF := fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC => (Jr.F₀ q.1).1)
    (ψF := fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC =>
      liftC S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (Jr.Mx q.1 *ᵥ q.2)))
    (φ'F := fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC =>
      (Jr.FJ q).1 - (S.hG.precedes S.hG' (le_refl (k + 1))).restrictφ (Jr.F₀ q.1).1)
    (fun y => analyticAt_pi_iff.1 (analyticAt_snd.comp hF₀) y)
    (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀) r)
    (fun y i => ?_) (fun r => ?_) ?_ ?_
  · simp only [liftC_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun r _ => ?_)
    exact (analyticAt_comp_fst' (p := (rawOf D', ψh)) (Jr.Mx_an _ r _ hΘ')).mul
      (analyticAt_comp_snd' (f := fun v : S.EC => v r) (p := (rawOf D', ψh))
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.U × Fin N => ℂ) r).analyticAt ψh))
  · exact (analyticAt_pi_iff.1 (analyticAt_fst.comp hFJ) r).sub
      (analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀) _)
  · show IsUnit (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν (Jr.F₀ (rawOf D')).2)
    rw [Jr.F₀_eq D' hD']
    exact Jr.unitH D' hD'
  · show IsUnit (constraintForm
      (opHk (S.hG.precedes S.hG' (le_refl (k + 1))) S.a S.ν (Jr.F₀ (rawOf D')).2)⁻¹
      (fieldBase (S.hG.precedes S.hG' (le_refl (k + 1))) (Jr.F₀ (rawOf D')).1))
    rw [Jr.F₀_eq D' hD']
    exact Jr.unitM D' hD'

include hΘ hψh in
theorem analyticAt_PJ (j : ℕ) : AnalyticAt ℂ (Jr.PJ j) (Θ, ψh) := by
  classical
  have hFJ := Jr.analyticAt_FJ hΘ hψh
  have hgJ := Jr.analyticAt_gJ hΘ ψh
  unfold PJ
  by_cases hj : j ≤ k
  · simp only [hj, ↓reduceDIte]
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun y => analyticAt_pi_iff.2 fun i => ?_)
    · exact analyticAt_composeField (G := levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) j (hj.trans (Nat.le_succ k))) (G' := stepG d L N₁ m₁ k ϱ) S.a
        (fun q => (Jr.FJ q).1) (fun q => (Jr.gJ q).1)
        (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hFJ) r)
        (fun y' j' => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_fst.comp hgJ) y') j')
        y i
    · by_cases hy : y ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
          j (hj.trans (Nat.le_succ k))).Ω 1
      · simp only [hy, ↓reduceIte]
        exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_snd.comp hgJ) y) i
      · simp only [hy, ↓reduceIte]
        exact analyticAt_const
  · simp only [hj, ↓reduceDIte]
    exact analyticAt_const

include hΘ hψh in
/-- The composite `ℰ_k` is jointly analytic where the densities `ℰ^{(j)}` are analytic at the
composed pairs. -/
theorem analyticAt_EJ
    (hE : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, ψh))) : AnalyticAt ℂ (Jr.EJ C) (Θ, ψh) := by
  unfold EJ
  exact Finset.analyticAt_fun_sum _ fun j hj =>
    AnalyticAt.comp (f := Jr.PJ j) (hE j hj) (Jr.analyticAt_PJ hΘ hψh j)

include hΘ hψh in
/-- The direct part `⟨g, φ_k(ψ)⟩₁` of `ℱ_k`, and every component of `φ_k(ψ)`, are jointly
analytic. -/
theorem analyticAt_svec_FJ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC =>
      svec (stepG d L N₁ m₁ k ϱ) (Jr.FJ q).1 y i) (Θ, ψh) := by
  have hFJ := Jr.analyticAt_FJ hΘ hψh
  exact analyticAt_svec (G' := stepG d L N₁ m₁ k ϱ) (fun q => (Jr.FJ q).1)
    (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hFJ) r) y i

include hΘ hψh in
/-- The composite `ℱ_k` is jointly analytic where the terms `ℱ^{(j)}(·, ·, g)` are analytic at the
composed pairs. -/
theorem analyticAt_FcJ (g : Fld d L N₁ m₁ (k + 1) N)
    (hF : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
      (Jr.PJ j (Θ, ψh))) : AnalyticAt ℂ (Jr.FcJ C g) (Θ, ψh) := by
  unfold FcJ
  refine (Finset.analyticAt_fun_sum _ fun y _ => Finset.analyticAt_fun_sum _ fun i _ =>
    analyticAt_const.mul (Jr.analyticAt_svec_FJ hΘ hψh y i)).add ?_
  exact Finset.analyticAt_fun_sum _ fun j hj =>
    AnalyticAt.comp (f := Jr.PJ j) (hF j hj) (Jr.analyticAt_PJ hΘ hψh j)

include hΘ hψh in
/-- The component `(y, i)` of `ℳ_k` is jointly analytic where the terms `ℳ^{(j)}(y; ·, ·, g)_i` are
analytic at the composed pairs. -/
theorem analyticAt_McJ (g : Fld d L N₁ m₁ (k + 1) N) (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (hM : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        Mloc C.m₀ C.Tm j y p.1 p.2 g i) (Jr.PJ j (Θ, ψh))) :
    AnalyticAt ℂ (Jr.McJ C g y i) (Θ, ψh) := by
  unfold McJ
  refine (Jr.analyticAt_svec_FJ hΘ hψh y i).add ?_
  exact Finset.analyticAt_fun_sum _ fun j hj =>
    AnalyticAt.comp (f := Jr.PJ j) (hM j hj) (Jr.analyticAt_PJ hΘ hψh j)

include hΘ hψh in
/-- **The exponent `W₁` is jointly analytic** at `(Θ, ψ̂)`, `Θ` in the chart, where the densities
`ℰ^{(j)}` are analytic at the composed pairs of `ψ̂` and of `0` (the critical point). -/
theorem analyticAt_W1
    (hE : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, ψh)))
    (hE0 : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, 0))) : AnalyticAt ℂ (Jr.W1 C) (Θ, ψh) := by
  unfold W1
  refine (analyticAt_const.mul (Jr.analyticAt_VJ hΘ hψh)).add
    ((Jr.analyticAt_EJ C hΘ hψh hE).sub ?_)
  exact (Jr.analyticAt_EJ C hΘ Jr.zero_le_pp hE0).comp_of_eq
    (analyticAt_fst.prod analyticAt_const) rfl

include hΘ hψh in
/-- **The exponent `W₂` is jointly analytic** at `(Θ, ψ̂)`, `Θ` in the chart, where the terms
`ℱ^{(j)}(·, ·, g)` are analytic at the composed pairs of `ψ̂` and of `0`. -/
theorem analyticAt_W2 (g : Fld d L N₁ m₁ (k + 1) N)
    (hF : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
      (Jr.PJ j (Θ, ψh)))
    (hF0 : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
      (Jr.PJ j (Θ, 0))) : AnalyticAt ℂ (Jr.W2 C g) (Θ, ψh) := by
  unfold W2
  refine (Jr.analyticAt_FcJ C hΘ hψh g hF).sub ?_
  exact (Jr.analyticAt_FcJ C hΘ Jr.zero_le_pp g hF0).comp_of_eq
    (analyticAt_fst.prod analyticAt_const) rfl

include hΘ in
/-- The kernel `∏ t_k` is jointly analytic. -/
theorem analyticAt_tKJ (ψh : S.EC) : AnalyticAt ℂ Jr.tKJ (Θ, ψh) := by
  have hgJ := Jr.analyticAt_gJ hΘ ψh
  unfold tKJ
  refine analyticAt_const.mul (AnalyticAt.cexp (AnalyticAt.neg (analyticAt_const.mul ?_)))
  exact analyticAt_couplingC (G' := S.G') S.a₁ (k + 1)
    (θF := fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC => q.1.1)
    (ψF := fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC => (Jr.gJ q).1)
    (fun y i => analyticAt_comp_fst'
      (f := fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => Θ.1 y i) (p := (Θ, ψh))
      (analyticAt_rawΨ y i Θ))
    (fun y i => analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (analyticAt_fst.comp hgJ) y) i)

include hΘ hψh in
/-- The exponential of the density `ρ_k` is jointly analytic where the class terms are analytic at
the composed pairs. -/
theorem analyticAt_rhoJ (g : Fld d L N₁ m₁ (k + 1) N)
    (hE : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
      (Jr.PJ j (Θ, ψh)))
    (hF : ∀ j ∈ Finset.Icc 1 k, AnalyticAt ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Floc C.m₀ C.Tm j p.1 p.2 g)
      (Jr.PJ j (Θ, ψh))) : AnalyticAt ℂ (Jr.rhoJ C g) (Θ, ψh) := by
  have hFJ := Jr.analyticAt_FJ hΘ hψh
  have hgJ := Jr.analyticAt_gJ hΘ ψh
  unfold rhoJ
  have hA : AnalyticAt ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC =>
      actionRawC (stepG d L N₁ m₁ k ϱ) S.a S.ν (Jr.gJ q).1 (Jr.gJ q).2 (Jr.FJ q).1) (Θ, ψh) :=
    analyticAt_actionRawC (stepG d L N₁ m₁ k ϱ) S.a S.ν (analyticAt_fst.comp hgJ)
      (analyticAt_snd.comp hgJ) (analyticAt_fst.comp hFJ)
  exact ((((analyticAt_const.mul hA).add (Jr.analyticAt_EJ C hΘ hψh hE)).sub
    analyticAt_const).add (Jr.analyticAt_FcJ C hΘ hψh g hF)).cexp

end Analytic

end JointRep

end StepSetting

end Balaban.Fluctuation
