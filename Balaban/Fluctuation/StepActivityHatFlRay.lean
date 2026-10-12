/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatRay
public import Balaban.Fluctuation.InteractionBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fluctuation field `flFieldOne` along the ray of the hat variable

* `bgFieldC_sub_eq_flFieldOne_hatLift`: for a datum `D` of level `k` whose tangent is
  `hatLift cc D' ψ̂` (`‖ψ̂‖ ≤ c_ψ`), `φ_k(D) - φ_{k+1}| = flFieldOne D' (hatLift cc D' ψ̂)`
  (`exact_fluct_eq_flFieldOne`, with the disc hypothesis supplied by `hreal_level`).
* `analyticAt_flFieldOne_hatRay`: `λ ↦ flFieldOne D' (hatLift cc D' (λ ψ̂)) y` is analytic at a
  complex `s` with `‖s ψ̂‖ < c_ψ` (the small solution of Theorem 7.2 at level `k` is analytic).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Filter Topology

section FlRay

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
  (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (ha₁ : 0 < a₁)
  (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
  {R : ℝ} (hR : 2 ≤ R)
  (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
  (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
  (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)

include hC hk hG hG' ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **The exact fluctuation along the ray of the hat variable**: if the tangent of the datum `D`
of level `k` (same `h̃`) is `hatLift cc D' ψ̂` with `‖ψ̂‖ ≤ c_ψ`, then
`φ_k(D) - φ_{k+1}| = flFieldOne D' (hatLift cc D' ψ̂)`. -/
theorem bgFieldC_sub_eq_flFieldOne_hatLift {D' : BgData Gp N}
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D') {D : BgData Hm N}
    (hh : ∀ x i, D.h x i = D'.h x i) {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    (ht : compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = hatLift Gp a₁ ν hG' cc D' ψh) :
    bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D -
        (hG.precedes hG' (le_refl (k + 1))).restrictφ
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') =
      flFieldOne Gp Hm BG₂ κ a₁ ν D' (hatLift Gp a₁ ν hG' cc D' ψh) := by
  have hψ := hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD' hψh
  obtain ⟨D₀, hDh, hDt, hDdisc⟩ := hreal_level hC hG hG' (le_refl (k + 1)) ha₁ H hc7
    (R := R) (by linarith) hsmR D' hD' _ hψ.1 hψ.2
  have hDeq : D₀ = D := by
    refine BgData.eq_of_raw (Prod.ext ?_ ?_)
    · funext z i
      have h1 := congrFun (congrFun hDt z) i
      have h2 := congrFun (congrFun ht z) i
      simp only [compTangent] at h1 h2
      show D₀.Ψ z i = D.Ψ z i
      linear_combination h1 - h2
    · funext z i
      show D₀.h z i = D.h z i
      rw [hDh z i, hh z i]
  subst hDeq
  have := exact_fluct_eq_flFieldOne hC hG hG' (le_refl (k + 1)) ha₁ H D' hD' hc7 D₀ hDh
    (by rw [hDt]; exact hψ.1) hR hDdisc hRs hsmall hnum hnum'
  rw [this, hDt]

include hC hk hG hG' ha₁ H hc7 hR hsmR hRs hsmall hnum hnum' hMX hdm hα hsm hcψ hδ₁ in
/-- **`flFieldOne` is holomorphic along the complex ray of the hat variable**: for a datum `D'` of
`Ξ^c(𝔹_{k+1}; 1, ε)` and a hat variable `ψ̂` with `‖s ψ̂‖ < c_ψ` (`s` complex), each coordinate of
`λ ↦ flFieldOne D' (hatLift cc D' (λ ψ̂))` is analytic at `λ = s`: it is the coordinate of
`F72 (P λ) - φ_{k+1}|` with `F72` the analytic small solution of Theorem 7.2. -/
theorem analyticAt_flFieldOne_hatRay {D' : BgData Gp N}
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D') (ψh : unitPts Gp × Fin N → ℂ)
    {s : ℂ} (hs : ∀ p, ‖s * ψh p‖ < cψ) (q : Hm.Ω 1 × Fin N) :
    AnalyticAt ℂ (fun l : ℂ => flFieldOne Gp Hm BG₂ κ a₁ ν D' (hatLift Gp a₁ ν hG' cc D' (l • ψh)) q)
      s := by
  classical
  have hU : ∀ᶠ l in 𝓝 s, ∀ p, ‖l * ψh p‖ ≤ cψ := by
    rw [Filter.eventually_all]
    intro p
    have hcont : ContinuousAt (fun l : ℂ => ‖l * ψh p‖) s := by fun_prop
    exact (hcont.eventually_lt continuousAt_const (hs p)).mono fun l hl => hl.le
  set y1 := hatLift Gp a₁ ν hG' cc D' ψh with hy1
  set φ0 := bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D' with hφ0
  set Ψc := (composeData (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁) φ0 D').Ψ
    with hΨc
  obtain ⟨F72, hF72an, hF72⟩ := theorem72_analytic (G := Hm) (a := compWeight L a₁) (ν := ν)
    (N := N) H
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
    exact ⟨D₀, hDh, ht, inUnionDomainC_of_tangent_hatLift hC hk hG hG' ha₁ H hc7
      (R := R) (by linarith) hsmR hMX hdm
      hα hsm cc hcψ hδ₁ hl' hD' hDh (by rw [hDt])⟩
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
  obtain ⟨Ds, hDsh, hDst, hDsd⟩ := hdat s (fun p => (hs p).le)
  have hF72at : AnalyticAt ℂ F72 (P s) := by
    refine hF72an _ ⟨Ds, hDsd, ?_⟩
    exact (hraw s Ds hDsh hDst).symm
  have hE : AnalyticAt ℂ (fun l : ℂ => (F72 (P l)).1 q -
      ((hG.precedes hG' (le_refl (k + 1))).restrictφ φ0) q) s :=
    (analyticAt_pi_iff.1 (analyticAt_fst.comp (hF72at.comp_of_eq hPan rfl)) q).sub analyticAt_const
  refine hE.congr ?_
  filter_upwards [hU] with l hl
  obtain ⟨D, hh, ht, hdom⟩ := hdat l hl
  have hl' : ∀ p, ‖ψh p * l‖ ≤ cψ := fun p => by rw [mul_comm]; exact hl p
  have hy : hatLift Gp a₁ ν hG' cc D' (l • ψh) = l • y1 := by rw [hy1, hatLift_smul]
  have hl'' : ∀ p, ‖(l • ψh) p‖ ≤ cψ := fun p => by simpa using hl p
  have hex := bgFieldC_sub_eq_flFieldOne_hatLift hC hk hG hG' ha₁ H hc7 hR hsmR hRs hsmall hnum
    hnum' hMX hdm hα hsm cc hcψ hδ₁ hD' hh hl'' (by rw [ht, hy1, ← hatLift_smul])
  have e : (F72 (P l)).1 = bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D := by
    rw [← hraw l D hh ht, hF72 D hdom]
  show _ = flFieldOne Gp Hm BG₂ κ a₁ ν D' (hatLift Gp a₁ ν hG' cc D' (l • ψh)) q
  rw [← hex, e]
  rfl

end FlRay

end Balaban.Localization
