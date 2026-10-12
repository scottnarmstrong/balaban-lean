/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepComplexHat
public import Balaban.Fluctuation.Prop33CloseReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The path of the complex step is analytic in the block datum (RAY-CHART §1; ACTIVITY §2)

On the complex chart of RAY-CHART §1 (a datum `D ∈ Ξ^c(𝔹_{k+1}; 1, ε)`, under `FlCore` and the
margins `decDomMargin < δc`, `K₄ C₁ ε < γ/2`, `δc² smallConstX ≤ 1/4`,
`cstarX e^{N₀ κ} ≤ L^{m₁}` of the covariance chart), the objects of the complex step that enter
the argument of the exponents depend analytically on the datum.  As in `theorem72_analytic`, each
statement gives one function of the raw data `(Ψ, h̃)`, analytic at every point of the chart
`XiCRaw`, which returns the object at every datum of the chart:

* `exists_analytic_bgC`: the complex small solution `(φ_{k+1}, α_{k+1}) = (bgFieldC, bgMultC)`;
* `exists_analytic_hatCovSqrt`: the entries of the square root `C^{(k)1/2}` (`hatCovSqrt`);
* `exists_analytic_composeField`: the critical point `ψ^{(k)}(θ)` of (2.1);
* `inUnionDomainC_of_tangent_hatLift`, `exists_analytic_bgC_tangent`: the old spin with tangent
  `hatLift cc θ ψ̂` lies in the domain `𝒟(𝔹_k)` of the small solution (`hreal_level`), and its small
  solution `(φ_k(ψ), α_k(ψ))` is analytic in `θ`.

A `StepSetting` fixes the datum and requires its field `h` to be a real constant (`hh₀`), so that
"analytic in the datum" is not a statement about one `StepSetting`.  `withDatum` replaces the datum
of a step; the family versions are, for the step with the datum `D` of the chart (and `h = h₀`):

* `exists_analytic_covSqrtC`, `exists_analytic_shiftUC`, `exists_analytic_psi0C`,
  `exists_analytic_psiAtC`: `covSqrtC`, `shiftUC x`, `psi0C` and the path point `psiAtC s x` are
  the values at `rawOf D` of functions analytic on the whole chart (complex `Ψ` and complex `h̃`);
* `dataUC_psiAtC_inUnionDomainC`: the complex old spin on the path (`s ∈ [0,1]`, `χ_fl(ψ̂) = 1`)
  lies in `𝒟(𝔹_k)` (the complex form of `dataU_inDomainR_path`);
* `exists_analytic_bgC_path`: its small solution `(φ_k(ψ), α_k(ψ))` is analytic in the datum.

The landed `shiftU`, `psi0` (real parts of objects of the real minimizer) have no such
continuation.  The analyticity of `WoneC`, `WtwoC` in the datum is the composition of these maps
with `interactionV` (as a function of the backgrounds and the tangent) and with the class terms at
the composed data; neither the analyticity of `interactionV` in the background
`(α_{k+1}, φ_{k+1})` nor the membership of the composed data of the complex path in the domains
`XiDom` of the class terms is landed, and they are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The complex small solution is analytic on the chart** (Theorem 7.2, analyticity): there is
one function of the raw data, analytic at every point of `Ξ^c(𝔹_{k+1}; 1, ε)`, which returns
`(bgFieldC, bgMultC)` at every datum of it. -/
theorem exists_analytic_bgC (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ F (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) ∧
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        F (rawOf D) = (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
          bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) := by
  obtain ⟨F, hFan, hF⟩ := theorem72_analytic (G := Gp) (a := compWeight L a₁) (ν := ν) (N := N)
    hC.HBp
  have hU : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      InUnionDomainC Gp (bgC0 d L N) (bgC1 d L N) ν D := fun D hD =>
    (isDecBg_one_of_xiCData hC hD).2.mono (c7_le_bgC1 d L N BG κ)
  refine ⟨F, ?_, fun D hD => hF D (hU D hD)⟩
  rintro Θ ⟨D, hD, rfl⟩
  exact hFan _ ⟨D, hU D hD, rfl⟩

/-- **The square root `C^{(k)1/2}` is analytic in the datum on the chart** (RAY-CHART §1,
Proposition, at `λ ≡ 1`): there is one matrix-valued function of the raw data, with entries analytic
at every point of `Ξ^c(𝔹_{k+1}; 1, ε)`, which returns `hatCovSqrt` at every datum of it. -/
theorem exists_analytic_hatCovSqrt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N →
        Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => F Θ p q) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)) ∧
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        F (rawOf D) = hatCovSqrt Gp a₁ ν D := by
  classical
  obtain ⟨F₀, hF₀an, hF₀⟩ := exists_analytic_bgC hC
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have hε := hC.eps_pos
      have hc1 := one_le_xiC1 d
      have hδ0 : 0 < xiC1 d * eps := by positivity
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hU := (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
  refine ⟨fun Θ => decCovSqrt Gp (compWeight L a₁) a₁ ν (F₀ Θ).2 (fun _ => 1)
    (barField Gp Θ.1 (F₀ Θ).1) (unitQ Gp) (unitP Gp), fun p q => ?_, fun D hD => ?_⟩
  · rintro Θ ⟨D, hD, rfl⟩
    obtain ⟨hI, -⟩ := isDecBg_one_of_xiCData hC hD
    have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
    have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
      simpa using hE1
    have hmem := decDom_of_isDecBg hC hs hD hI hdm hα
    have hF₀at : AnalyticAt ℂ F₀ (rawOf D) := hF₀an _ ⟨D, hD, rfl⟩
    have hφ : ∀ r, AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).1 r)
        (rawOf D) := fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀at) r
    have hαa : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).2)
        (rawOf D) := analyticAt_snd.comp hF₀at
    have hbar := analyticAt_barField (Gp := Gp) (q := rawOf D)
      (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).1)
      (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => Θ.1) hφ
      (fun y j => analyticAt_rawΨ y j (rawOf D))
    have he : AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)), (barField Gp Θ.1 (F₀ Θ).1, (F₀ Θ).2))) (rawOf D) :=
      AnalyticAt.prod analyticAt_const (hbar.prod hαa)
    have hpt : ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
        (barField Gp (rawOf D).1 (F₀ (rawOf D)).1, (F₀ (rawOf D)).2)) ∈ DecDom Gp N κ δc := by
      rw [hF₀ D hD]; exact hmem
    have hg : AnalyticAt ℂ (fun e : DecData Gp N =>
        decCovSqrt Gp (compWeight L a₁) a₁ ν e.2.2 (extS Gp e.1) e.2.1 (unitQ Gp) (unitP Gp) p q)
        ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
          (barField Gp (rawOf D).1 (F₀ (rawOf D)).1, (F₀ (rawOf D)).2)) :=
      analyticOnNhd_decCovSqrt_entry (N := N) hX hC.hκ.le hMX hδc hsm hU p q _ hpt
    have hcomp := AnalyticAt.comp (f := fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)), (barField Gp Θ.1 (F₀ Θ).1, (F₀ Θ).2))) hg he
    refine hcomp.congr (Filter.Eventually.of_forall fun Θ => ?_)
    show decCovSqrt Gp (compWeight L a₁) a₁ ν (F₀ Θ).2 (extS Gp (fun _ => (1 : ℂ)))
      (barField Gp Θ.1 (F₀ Θ).1) (unitQ Gp) (unitP Gp) p q = _
    rw [extS_one]
  · show decCovSqrt Gp (compWeight L a₁) a₁ ν (F₀ (rawOf D)).2 (fun _ => 1)
      (barField Gp D.Ψ (F₀ (rawOf D)).1) (unitQ Gp) (unitP Gp) = hatCovSqrt Gp a₁ ν D
    rw [hF₀ D hD]
    rfl

/-- **The critical point `ψ^{(k)}(θ)` of (2.1) is analytic in the datum on the chart**: there is
one function of the raw data, with coordinates analytic at every point of `Ξ^c(𝔹_{k+1}; 1, ε)`,
which returns the composed field `composeData h a (bgFieldC D) D` at every datum of it. -/
theorem exists_analytic_composeField (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁} (h : Precedes G Gp) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ,
      (∀ x i, AnalyticOnNhd ℂ (fun Θ => F Θ x i)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)) ∧
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        F (rawOf D) = (composeData h (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) D).Ψ := by
  obtain ⟨F₀, hF₀an, hF₀⟩ := exists_analytic_bgC hC
  refine ⟨fun Θ x i => composeField G Gp (compWeight L a₁) (F₀ Θ).1 Θ.1 x i, fun x i => ?_,
    fun D hD => ?_⟩
  · rintro Θ ⟨D, hD, rfl⟩
    have hF₀at : AnalyticAt ℂ F₀ (rawOf D) := hF₀an _ ⟨D, hD, rfl⟩
    exact analyticAt_composeField (G := G) (G' := Gp) (compWeight L a₁)
      (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => (F₀ Θ).1)
      (fun Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N => Θ.1)
      (fun r => analyticAt_pi_iff.1 (analyticAt_fst.comp hF₀at) r)
      (fun y j => analyticAt_rawΨ y j (rawOf D)) x i
  · funext x i
    show composeField G Gp (compWeight L a₁) (F₀ (rawOf D)).1 D.Ψ x i = _
    rw [hF₀ D hD]
    rfl

/-! ### The old spin with tangent `hatLift` -/

section Tangent

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
/-- **The old spin whose tangent is the fluctuation field of the hat engine lies in the domain `𝒟`
of the small solution** (FLUCTUATION Lemma 2.3 (d); `hreal_level` at the point `t = 1` of its
disc): for a datum `D'` of `Ξ^c(𝔹_{k+1}; 1, ε)` on the covariance chart and a bounded hat variable
`ψ̂`, every datum `D` of level `k` with the same `h̃` and with tangent
`D.Ψ - ψ^{(k)}(D') = hatLift cc D' ψ̂` is in `𝒟(𝔹_k) = InUnionDomainC (bgC0) (bgC1)`. -/
theorem inUnionDomainC_of_tangent_hatLift {D' : BgData Gp N}
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D') {D : BgData Hm N}
    (hh : ∀ x i, D.h x i = D'.h x i)
    (ht : compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = hatLift Gp a₁ ν hG' cc D' ψh) :
    InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν D := by
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
  have hhB : D₀.h = (composeData (hG.precedes hG' (le_refl (k + 1))) (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').h := by
    funext z i
    rw [hDh z i]
    show D'.h z i = (if z ∈ Hm.Ω 1 then D'.h z i else 0 : ℂ)
    simp [(hG z).1]
  have h1 := hDdisc 1 (by simpa using hR)
  rw [lineAt_tangent D₀ _ hhB, hDeq] at h1
  exact h1

include hC hk ha₁ H hc7 hR hsmR hMX hdm hα hsm hcψ hδ₁ hψh in
/-- **The small solution `(φ_k(ψ), α_k(ψ))` of the old spin with tangent `hatLift cc D' ψ̂` is
analytic in the block datum `D'`** on the chart: one function of the raw data, analytic on
`Ξ^c(𝔹_{k+1}; 1, ε)`, returns `(bgFieldC, bgMultC)` of every datum `D` of level `k` with the same
`h̃` as `D'` and tangent `D.Ψ - ψ^{(k)}(D') = hatLift cc D' ψ̂` (Theorem 7.2 at the level `k`,
composed with the analytic critical point and square root). -/
theorem exists_analytic_bgC_tangent :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ),
      AnalyticOnNhd ℂ F (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) ∧
      ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
        ∀ D : BgData Hm N, (∀ x i, D.h x i = D'.h x i) →
          compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D =
              hatLift Gp a₁ ν hG' cc D' ψh →
          F (rawOf D') = (bgFieldC Hm (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Hm (compWeight L a₁) ν (bgC0 d L N) D) := by
  obtain ⟨Pc, hPcan, hPc⟩ := exists_analytic_composeField hC (hG.precedes hG' (le_refl (k + 1)))
  obtain ⟨M, hMan, hM⟩ := exists_analytic_hatCovSqrt hC hk hMX hdm hα hsm
  obtain ⟨F, hFan, hF⟩ := theorem72_analytic (G := Hm) (a := compWeight L a₁) (ν := ν) (N := N) H
  -- the raw data of the old spin, as a function of the raw data of the block datum
  set g : RawData d L (N₁ * L ^ m₁) (k + 1) N → RawData d L (N₁ * L ^ m₁) (k + 1) N :=
    fun Θ => ((fun z i => Pc Θ z i + liftC hG' (cc • (M Θ *ᵥ ψh)) z i), Θ.2) with hg
  have hraw : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ D : BgData Hm N, (∀ x i, D.h x i = D'.h x i) →
        compTangent hG hG' (le_refl (k + 1)) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D =
            hatLift Gp a₁ ν hG' cc D' ψh → (D.Ψ, D.h) = g (rawOf D') := by
    intro D' hD' D hh ht
    refine Prod.ext ?_ ?_
    · funext z i
      have h2 := congrFun (congrFun ht z) i
      simp only [compTangent] at h2
      show D.Ψ z i = Pc (rawOf D') z i + liftC hG' (cc • (M (rawOf D') *ᵥ ψh)) z i
      rw [hPc D' hD', hM D' hD']
      have h3 : hatLift Gp a₁ ν hG' cc D' ψh z i =
          liftC hG' (cc • (hatCovSqrt Gp a₁ ν D' *ᵥ ψh)) z i := rfl
      linear_combination h2 + h3
    · funext z i
      exact hh z i
  refine ⟨fun Θ => F (g Θ), ?_, fun D' hD' D hh ht => ?_⟩
  · rintro Θ ⟨D', hD', rfl⟩
    -- a datum with the prescribed tangent exists (`hreal_level`)
    have hψ := hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD' hψh
    obtain ⟨D₀, hDh, hDt, -⟩ := hreal_level hC hG hG' (le_refl (k + 1)) ha₁ H hc7
      (R := R) (by linarith) hsmR D' hD' _ hψ.1 hψ.2
    have hdom := inUnionDomainC_of_tangent_hatLift hC hk hG hG' ha₁ H hc7 hR hsmR hMX hdm hα hsm
      cc hcψ hδ₁ hψh hD' hDh hDt
    have hpt := hraw D' hD' D₀ hDh hDt
    have hgan : AnalyticAt ℂ g (rawOf D') := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun z => analyticAt_pi_iff.2 fun i => ?_)
        analyticAt_snd
      refine (hPcan z i _ ⟨D', hD', rfl⟩).add ?_
      simp only [liftC_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
      exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun r _ =>
        (hMan _ r _ ⟨D', hD', rfl⟩).mul analyticAt_const)
    exact (hFan _ ⟨D₀, hdom, hpt.symm⟩).comp_of_eq hgan rfl
  · have hdom := inUnionDomainC_of_tangent_hatLift hC hk hG hG' ha₁ H hc7 hR hsmR hMX hdm hα hsm
      cc hcψ hδ₁ hψh hD' hh ht
    show F (g (rawOf D')) = _
    rw [← hraw D' hD' D hh ht]
    exact hF D hdom

end Tangent

end Chart

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The step with the block datum `θ` replaced by `D` (the same generating set, the same real
constant field `h₀`, the same numbers). -/
def withDatum (D : BgData S.G' N) (hD : ∀ x i, D.h x i = (S.h₀ i : ℂ)) :
    StepSetting d L N₁ m₁ k N ϱ :=
  { S with D' := D, hh₀ := hD }

theorem withDatum_self : S.withDatum S.D' S.hh₀ = S := rfl

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

section Family

variable (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)

include hC hMX hdm hα hsm in
/-- **`C^{(k)1/2}` of the complex step is analytic in the block datum** on the chart: one
matrix-valued function of the raw data with analytic entries on `Ξ^c(𝔹_{k+1}; 1, ε)` returns
`covSqrtC` of the step with the datum `D`, for every datum `D` of the chart with `h = h₀`. -/
theorem exists_analytic_covSqrtC :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → Matrix (S.U × Fin N) (S.U × Fin N) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => F Θ p q) (XiCRaw S.G' S.a S.ν (k + 1) 1 eps)) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → F (rawOf D) = (S.withDatum D hD).covSqrtC := by
  obtain ⟨F, hFan, hF⟩ := exists_analytic_hatCovSqrt hC S.hk1 hMX hdm hα hsm
  exact ⟨F, hFan, fun D hD hX => (hF D hX).trans (S.withDatum D hD).covSqrtC_eq_hatCovSqrt.symm⟩

include hC hMX hdm hα hsm in
/-- **The substitution (2.7) of the complex step is analytic in the block datum** on the chart:
for every fluctuation variable `ψ̂`, one function of the raw data, analytic on
`Ξ^c(𝔹_{k+1}; 1, ε)`, returns `shiftUC ψ̂` of the step with the datum `D`. -/
theorem exists_analytic_shiftUC (x : S.E) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → F (rawOf D) = (S.withDatum D hD).shiftUC x := by
  obtain ⟨M, hMan, hM⟩ := S.exists_analytic_covSqrtC hC hMX hdm hα hsm
  refine ⟨fun Θ => ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (M Θ *ᵥ yhat x), fun Θ hΘ => ?_,
    fun D hD hX => ?_⟩
  · refine analyticAt_pi_iff.2 fun q => ?_
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    exact analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun r _ => (hMan q r Θ hΘ).mul analyticAt_const)
  · show ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (M (rawOf D) *ᵥ yhat x) = _
    rw [hM D hD hX]
    rfl

include hC in
/-- **The background `ψ^{(k)}(θ)` of the complex step is analytic in the block datum** on the
chart: one function of the raw data, analytic on `Ξ^c(𝔹_{k+1}; 1, ε)`, returns `psi0C` of the step
with the datum `D`. -/
theorem exists_analytic_psi0C :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → F (rawOf D) = (S.withDatum D hD).psi0C := by
  obtain ⟨P, hPan, hP⟩ := exists_analytic_composeField hC
    (S.hG.precedes S.hG' (le_refl (k + 1)))
  refine ⟨fun Θ q => P Θ (unitRep (G' := S.G') q.1) q.2, fun Θ hΘ => ?_, fun D hD hX => ?_⟩
  · exact analyticAt_pi_iff.2 fun q => hPan _ _ Θ hΘ
  · funext q
    show P (rawOf D) (unitRep (G' := S.G') q.1) q.2 = _
    rw [hP D hX]
    rfl

include hC hMX hdm hα hsm in
/-- **The path of the interpolation of the complex step is analytic in the block datum** on the
chart: for every `s` and every fluctuation variable `ψ̂`, one function of the raw data, analytic on
`Ξ^c(𝔹_{k+1}; 1, ε)`, returns the complex old spin `ψ^{(k)}(θ) + s β_k^{-1/2} C^{(k)1/2}(θ) ψ̂`
(`psiAtC s ψ̂`) of the step with the datum `D`. -/
theorem exists_analytic_psiAtC (s : ℝ) (x : S.E) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC,
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → F (rawOf D) = (S.withDatum D hD).psiAtC s x := by
  obtain ⟨P, hPan, hP⟩ := S.exists_analytic_psi0C hC
  obtain ⟨Q, hQan, hQ⟩ := S.exists_analytic_shiftUC hC hMX hdm hα hsm x
  refine ⟨fun Θ => P Θ + (s : ℂ) • Q Θ, fun Θ hΘ => ?_, fun D hD hX => ?_⟩
  · refine analyticAt_pi_iff.2 fun q => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (analyticAt_pi_iff.1 (hPan Θ hΘ) q).add
      (analyticAt_const.mul (analyticAt_pi_iff.1 (hQan Θ hΘ) q))
  · show P (rawOf D) + (s : ℂ) • Q (rawOf D) = _
    rw [hP D hD hX, hQ D hD hX]
    rfl

end Family

/-! ### The complex old spin on the path stays in the domain of the small solution -/

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

include hβ in
theorem norm_betaU_rpow : ‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ = S.betaU ^ (-(1 / 2 : ℝ)) := by
  have hβU : 0 ≤ S.betaU := by unfold betaU; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hβU _)]

include hp₁ in
/-- On the ray `s ψ̂`, `s ∈ [0,1]`, `χ_fl(ψ̂) = 1`, the hat variable is bounded by `p₁`. -/
theorem norm_smul_yhat_le {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) (p : S.U × Fin N) : ‖((s : ℂ) • yhat x) p‖ ≤ S.p₁ := by
  rw [chiFl_eq_one_iff hp₁] at hx
  have h1 : ‖((x p.1 p.2 : ℝ) : ℂ)‖ ≤ S.p₁ := by
    rw [Complex.norm_real]
    exact ((PiLp.norm_apply_le (x p.1) p.2).trans (norm_le_pi_norm x p.1)).trans hx.le
  show ‖(s : ℂ) * ((x p.1 p.2 : ℝ) : ℂ)‖ ≤ S.p₁
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
  calc s * ‖((x p.1 p.2 : ℝ) : ℂ)‖ ≤ 1 * S.p₁ :=
        mul_le_mul hs.2 h1 (norm_nonneg _) zero_le_one
    _ = S.p₁ := one_mul _

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **The complex old spin on the path of the interpolation lies in the domain `𝒟` of the small
solution** (FLUCTUATION Lemma 2.3 (d), Lemma 2.5, for a complex block datum): for a datum of
`Ξ^c(𝔹_{k+1}; 1, ε)` on the covariance chart, `s ∈ [0,1]` and `χ_fl(ψ̂) = 1`, the datum
`dataUC (psiAtC s ψ̂)` of `ψ^{(k)}(θ) + s β_k^{-1/2} C^{(k)1/2}(θ) ψ̂` is in
`𝒟(𝔹_k) = InUnionDomainC (bgC0) (bgC1)`.  (The complex form of `dataU_inDomainR_path`; the
premise `2 C₄ K₁ C₁ ε + 5 R δ₁ ≤ c₁` is that of `hreal_level`.) -/
theorem dataUC_psiAtC_inUnionDomainC (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E} (hx : chiFl S.U N S.p₁ x = 1) :
    InUnionDomainC (stepG d L N₁ m₁ k ϱ) (bgC0 d L N) (bgC1 d L N) S.ν
      (S.dataUC (S.psiAtC s x)) :=
  inUnionDomainC_of_tangent_hatLift hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR hMX hdm hα hsm _
    hp₁.le (by rwa [S.norm_betaU_rpow hβ]) (S.norm_smul_yhat_le hp₁ hs hx) hD
    (fun z i => by rw [S.dataUC_h, S.hh₀]) (S.compTangent_psiAtC s x)

include hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁ in
/-- **The small solution `(φ_k(ψ), α_k(ψ))` of the complex old spin on the path is analytic in the
block datum** on the chart: for `s ∈ [0,1]` and `χ_fl(ψ̂) = 1`, one function of the raw data,
analytic on `Ξ^c(𝔹_{k+1}; 1, ε)`, returns `(bgFieldC, bgMultC)` of the datum
`dataUC (psiAtC s ψ̂)` of the step with the block datum `D`, for every datum `D` of the chart with
`h = h₀`. -/
theorem exists_analytic_bgC_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) {x : S.E}
    (hx : chiFl S.U N S.p₁ x = 1) :
    ∃ F : RawData d L (N₁ * L ^ m₁) (k + 1) N →
        ((stepG d L N₁ m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ),
      AnalyticOnNhd ℂ F (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        F (rawOf D) =
          (bgFieldC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
              ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x)),
            bgMultC (stepG d L N₁ m₁ k ϱ) S.a S.ν (bgC0 d L N)
              ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x))) := by
  obtain ⟨F, hFan, hF⟩ := exists_analytic_bgC_tangent hC S.hk1 S.hG S.hG' ha₁ hC.HBp hc7 hR hsmR
    hMX hdm hα hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hp₁.le (by rwa [S.norm_betaU_rpow hβ])
    (S.norm_smul_yhat_le hp₁ hs hx)
  refine ⟨F, hFan, fun D hD hX => ?_⟩
  exact hF D hX ((S.withDatum D hD).dataUC ((S.withDatum D hD).psiAtC s x))
    (fun z i => by rw [(S.withDatum D hD).dataUC_h]; exact (hD z i).symm)
    ((S.withDatum D hD).compTangent_psiAtC s x)

end Path

end StepSetting

end Balaban.Fluctuation
