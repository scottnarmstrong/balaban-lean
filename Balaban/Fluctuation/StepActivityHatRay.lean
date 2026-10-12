/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexExponent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential `V^{(k)}` is holomorphic along the complex ray of the hat variable

For a datum `D'` of `Ξ^c(𝔹_{k+1}; 1, ε)` on the covariance chart and a hat variable `ψ̂` with
`‖s ψ̂‖ < c_ψ`, the function `λ ↦ interactionOne (Θ, hatLift cc D' (λ ψ̂))` is analytic at `λ = s`
(FLUCTUATION Lemma 2.3 (d): `V^{(k)}` is analytic in `(ψ', φ_{k+1}, α_{k+1})`, composed with the
analytic small solution of Theorem 7.2 at the level `k`).  This is the holomorphy needed to
identify the third complex derivative `dirS3` of the hat expansion with the third real derivative
of the interpolation (`StepActivityHat`).

* `iteratedDeriv_comp_ofReal`: the iterated derivative of the real restriction of a function
  analytic at a real point is that of the function.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Filter Topology

/-- **The real restriction of a function analytic at a real point**: its `n`-th real derivative at
the point is the `n`-th complex derivative. -/
theorem iteratedDeriv_comp_ofReal (n : ℕ) :
    ∀ (G : ℂ → ℂ) (x : ℝ), AnalyticAt ℂ G (x : ℂ) →
      iteratedDeriv n (fun r : ℝ => G (r : ℂ)) x = iteratedDeriv n G (x : ℂ) := by
  induction n with
  | zero => intro G x _; simp
  | succ n ih =>
    intro G x hG
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hev : deriv (fun r : ℝ => G (r : ℂ)) =ᶠ[𝓝 x] fun r : ℝ => deriv G (r : ℂ) := by
      have h1 : ∀ᶠ z in 𝓝 (x : ℂ), AnalyticAt ℂ G z := hG.eventually_analyticAt
      have h2 : ∀ᶠ r : ℝ in 𝓝 x, AnalyticAt ℂ G (r : ℂ) :=
        Complex.continuous_ofReal.continuousAt.eventually h1
      filter_upwards [h2] with r hr
      exact (hr.differentiableAt.hasDerivAt.comp_ofReal).deriv
    rw [hev.iteratedDeriv_eq]
    exact ih (deriv G) x hG.deriv

section Ray

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
/-- **`V^{(k)}` is holomorphic along the complex ray of the hat variable**: for a datum `D'` of
`Ξ^c(𝔹_{k+1}; 1, ε)` and a hat variable `ψ̂` with `‖s ψ̂‖ < c_ψ` (`s` real), the function
`λ ↦ interactionOne (rawOf D', hatLift cc D' (λ ψ̂))` is analytic at `λ = s`. -/
theorem analyticAt_interactionOne_hatRay {D' : BgData Gp N}
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D') (ψh : unitPts Gp × Fin N → ℂ)
    {s : ℂ} (hs : ∀ p, ‖s * ψh p‖ < cψ) :
    AnalyticAt ℂ (fun l : ℂ => interactionOne hG hG' le_rfl a₁ ν eps
      (rawOf D', hatLift Gp a₁ ν hG' cc D' (l • ψh))) s := by
  classical
  have hU : ∀ᶠ l in 𝓝 s, ∀ p, ‖l * ψh p‖ ≤ cψ := by
    rw [Filter.eventually_all]
    intro p
    have hcont : ContinuousAt (fun l : ℂ => ‖l * ψh p‖) s := by fun_prop
    exact (hcont.eventually_lt continuousAt_const (hs p)).mono fun l hl => hl.le
  set y1 := hatLift Gp a₁ ν hG' cc D' ψh with hy1
  set φ0 := bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D' with hφ0
  set α0 := bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D' with hα0
  set Ψc := (composeData (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) φ0 D').Ψ
    with hΨc
  obtain ⟨F72, hF72an, hF72⟩ := theorem72_analytic (G := Hm) (a := compWeight L a₁) (ν := ν)
    (N := N) H
  -- for each `l` in the neighbourhood: the datum with tangent `l • y1`
  have hdat : ∀ l : ℂ, (∀ p, ‖l * ψh p‖ ≤ cψ) → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁) φ0 D' D = l • y1 ∧
      InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν D := by
    intro l hl
    have hl' : ∀ p, ‖(l • ψh) p‖ ≤ cψ := fun p => by simpa using hl p
    have hψ := hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD' hl'
    obtain ⟨D₀, hDh, hDt, -⟩ := hreal_level hC hG hG' (le_refl (k + 1)) ha₁ H hc7
      (R := R) (by linarith) hsmR D' hD' _ hψ.1 hψ.2
    have ht : compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁) φ0 D' D₀ = l • y1 := by
      rw [hDt, hy1, ← hatLift_smul]
    exact ⟨D₀, hDh, ht, inUnionDomainC_of_tangent_hatLift hC hk hG hG' ha₁ H hc7 hR hsmR hMX hdm
      hα hsm cc hcψ hδ₁ hl' hD' hDh (by rw [hDt])⟩
  -- the raw data of that datum, as an analytic function of `l`
  let P : ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N :=
    fun l => ((fun z i => Ψc z i + l * y1 z i), (fun z i => D'.h z i))
  have hPan : AnalyticAt ℂ P s := by
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun z => analyticAt_pi_iff.2 fun i => ?_)
      analyticAt_const
    exact analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hraw : ∀ l : ℂ, ∀ D : BgData Hm N, (∀ x i, D.h x i = D'.h x i) →
      compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁) φ0 D' D = l • y1 →
      (D.Ψ, D.h) = P l := by
    intro l D hh ht
    refine Prod.ext ?_ ?_
    · funext z i
      have h2 := congrFun (congrFun ht z) i
      simp only [compTangent] at h2
      show D.Ψ z i = Ψc z i + l * y1 z i
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      linear_combination h2
    · funext z i
      exact hh z i
  -- the analytic expression
  obtain ⟨hs0, hsl⟩ : (∀ p, ‖s * ψh p‖ ≤ cψ) ∧ True := ⟨fun p => (hs p).le, trivial⟩
  obtain ⟨Ds, hDsh, hDst, hDsd⟩ := hdat s hs0
  have hF72at : AnalyticAt ℂ F72 (P s) := by
    refine hF72an _ ⟨Ds, hDsd, ?_⟩
    exact (hraw s Ds hDsh hDst).symm
  have hD'2 : InUnionDomainC Gp (bgC0 d L N) (thm73C2 d L N) ν D' :=
    (isDecBg_one_of_xiCData hC hD').2.mono (hc7.trans (thm73C3_le_thm73C2 d L N))
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ hG hG' (le_refl (k + 1)) H hC.HBp D' hD'2
  have hΦ' : restrictField Hm Φ = fieldBase (hG.precedes hG' (le_refl (k + 1))) φ0 :=
    funext fun x => funext fun i => hΦ x i
  have hE : AnalyticAt ℂ (fun l : ℂ => interactionV (hG.precedes hG' (le_refl (k + 1)))
      (compWeight L a₁) ν α0 φ0 (l • y1)
      ((F72 (P l)).1 - (hG.precedes hG' (le_refl (k + 1))).restrictφ φ0)) s := by
    refine analyticAt_interactionV (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν
      (αF := fun _ => α0) (φF := fun _ => φ0) (ψF := fun l => l • y1)
      (φ'F := fun l => (F72 (P l)).1 - (hG.precedes hG' (le_refl (k + 1))).restrictφ φ0)
      (fun y => analyticAt_const) (fun r => analyticAt_const) (fun y i => ?_) (fun r => ?_) ?_ ?_
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact analyticAt_id.mul analyticAt_const
    · exact (analyticAt_pi_iff.1 (analyticAt_fst.comp (hF72at.comp_of_eq hPan rfl)) r).sub
        analyticAt_const
    · show IsUnit (opHk (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν α0)
      exact dirichletOperator_isUnit Hm St.pos St.mass St.weights _ St.alpha
    · show IsUnit (constraintForm
        (opHk (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) ν α0)⁻¹
        (fieldBase (N := N) (hG.precedes hG' (le_refl (k + 1))) φ0))
      rw [← hΦ']
      exact constraintForm_isUnit St
  refine hE.congr ?_
  filter_upwards [hU] with l hl
  obtain ⟨D, hh, ht, hdom⟩ := hdat l hl
  have hy : hatLift Gp a₁ ν hG' cc D' (l • ψh) = l • y1 := by rw [hy1, hatLift_smul]
  have hOne := interactionOne_eq hG hG' (le_refl (k + 1)) hD' hh
  show interactionV _ _ _ _ _ _ _ = interactionOne hG hG' le_rfl a₁ ν eps
    (rawOf D', hatLift Gp a₁ ν hG' cc D' (l • ψh))
  have e : (F72 (P l)).1 = bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D := by
    rw [← hraw l D hh ht, hF72 D hdom]
  rw [hy, ← ht, hOne, e]

end Ray

end Balaban.Localization
