/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassChart
public import Balaban.Fluctuation.LocalPairReplacementHat
public import Balaban.Localization.LocalHatIntegral
public import Balaban.Analysis.ParamIntegralAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local term with the local hat variable, and its `ψ̂`-integral at a local chart point

P3 (4.46)-(4.47), printed pp. 78-79, recomputes a term of the expansion on the local generating set
`𝔹 = 𝔹_{k+1}(Y⁺)`: the decoupled background `(φ, α) = F₁(s, Θ)` of the cover of `𝔹`, the
fluctuation variable `ψ' = cc C^{1/2}(s) ψ̂` formed with the square root of the cover of `𝔹` at that
background (the local hat lift, extended by zero off the unit blocks of `𝔹`), the fluctuation field
`Sol(s, …)` of the fluctuation generating set `H⁻ = 𝔹_k(Y⁺)`, and a functional `Φ` of these
objects.  Every object is computed from the datum `Θ` of `𝔹` alone: no ambient datum enters
(W780 D3).  Here (cover form, no `DGSetting`, no `IsLevel`):

* `fanLC_analyticAt_cover`, `fanLC_norm_le_cover`: the composite `Φ(F₁(s, Θ), Sol(s, …), (Θ, ψ'))`
  is analytic in `((Θ, ψ'), s)` at every point with `Θ` in the chart, `ψ'` in the ball of
  layer-constant fluctuations and `s` in the polydisc, and bounded there, for `Φ` analytic
  (bounded) on the realizable triples with layer-constant fluctuation `FlRealLC`;
* `fanLocalHat_analytic_cover`, `fanLocalHat_norm_le_cover`: the same with `ψ'` the local hat lift
  of `ψ̂`, `|ψ̂| ≤ c_ψ`, and the parameters `s = σ w` for an analytic parameter map `σ` from a
  polydisc (`σ = extParams 𝔹 X₁` for the expansion of `𝔹`, or the transport `τ` of the replacement
  identity `coef_eTermFun_replacement_localB_hat`);
* `analyticOnNhd_setIntegral_box`: a parameter integral over the real box `|ψ̂| ≤ c_ψ` against a
  finite measure of a jointly analytic, bounded integrand is analytic and bounded;
* `fanLocalHat_integral_cover`: **the `ψ̂`-integral of the local term**,
  `(Θ, w) ↦ ∫_{|ψ̂| ≤ c_ψ} Φ(…, ψ'(Θ, σ w, ψ̂)) dγ(ψ̂)`, is analytic on the local chart times the
  polydisc and bounded by `B γ(box)`;
* `localB_eTermHat_integral`: the instance at `𝔹 = localB (k + 1) … Y` and the old-term
  functional `Φ = eTermFun` of the E-part (`localB_eTermFun_analytic`, `localB_eTermFun_bound`);
* `localB_eTermHat_integral_xiFieldDom`: the clauses `analyticE` and `boundE` (uniform bound) of
  the successor class for the `ψ̂`-integrated E-part term at a parameter point `w₀` of the
  polydisc, read on the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` through the cut-off `clipRaw 𝔹`
  (`LocalClassChart.lean`), for `ε_{k+1} ≤ ε'`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory

section FanLC

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- **(AE1) for the cover of `𝔹`, with a layer-constant fluctuation, at one point** (cover form of
the point step of `fanHL_analytic`, the parameters `s` a free variable): for `Φ` analytic on
`FlRealLC`, the composite `Φ(F₁(s, Θ), Sol(s, flEdat(F₁(s, Θ), Θ, ψ')), (Θ, ψ'))` is analytic in
`((Θ, ψ'), s)` at a point with `Θ = D` in the chart `Ξ^c(𝔹; 1, ε')`, `ψ' ∈ FlBallLC H⁻ δ₁` and
`|s_P| < e^κ`, `s = 1` on the cubes meeting `X₁`. -/
theorem fanLC_analyticAt_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
      Φ (F₁ (q.2, q.1.1)) (Sol (q.2, flEdat Gp Hm (F₁ (q.2, q.1.1)) q.1.1.1 q.1.2)).1 q.1)
      ((rawOf D, ψ'), s) := by
  classical
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  obtain ⟨φ, α, δφ, δα, -, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁ hPmp hF₁ hSol hs hs1 hD hψ.1
  set pt : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) ×
      Dec2.DecParams (coverOf Gp) := ((rawOf D, ψ'), s) with hpt
  have ha0 : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) => (q.2, q.1.1)) pt :=
    analyticAt_snd.prod (analyticAt_fst.comp analyticAt_fst)
  have ha1 : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
      F₁ (q.2, q.1.1)) pt :=
    (hF₁an (s, rawOf D) ⟨hs, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have hφ1 : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
      (F₁ (q.2, q.1.1)).1) pt := analyticAt_fst.comp ha1
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
      q.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl
  set ed : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) ×
      Dec2.DecParams (coverOf Gp) → Edat Hm N :=
    fun q => flEdat Gp Hm (F₁ (q.2, q.1.1)) q.1.1.1 q.1.2 with hed
  have haed : AnalyticAt ℂ ed pt := by
    refine AnalyticAt.prod (analyticAt_barField (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
        (F₁ (q.2, q.1.1)).1) (fun q => q.1.1.1)
      (fun r => analyticAt_pi_iff.1 hφ1 r) hΨ1) (AnalyticAt.prod
      (analyticAt_flAlpha (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
        (F₁ (q.2, q.1.1)).2) (fun y => analyticAt_pi_iff.1 (analyticAt_snd.comp ha1) y))
      (AnalyticAt.prod (analyticAt_snd.comp analyticAt_fst) analyticAt_const))
  have e2 : ed pt = flEdat Gp Hm (φ, α) D.Ψ ψ' := by
    show flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ' = _
    rw [hFeq]
  have hSolpt : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
      Sol (q.2, ed q)) pt := by
    refine (hSolan (s, ed pt) ⟨hs, ?_⟩).comp_of_eq (analyticAt_snd.prod haed) rfl
    rw [e2]; exact hstrict
  have hg : AnalyticAt ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) × Dec2.DecParams (coverOf Gp) =>
      (F₁ (q.2, q.1.1), (Sol (q.2, ed q)).1, q.1)) pt :=
    ha1.prod ((analyticAt_fst.comp hSolpt).prod analyticAt_fst)
  have hval : (F₁ (pt.2, pt.1.1), (Sol (pt.2, ed pt)).1, pt.1) =
      ((φ, α), δφ, (rawOf D, ψ')) := by
    show (F₁ (s, rawOf D), (Sol (s, ed pt)).1, (rawOf D, ψ')) = _
    rw [hFeq, e2, hSeq]
  have hΦpt := hΦ _ ⟨hmem, hψ.2⟩
  rw [← hval] at hΦpt
  exact hΦpt.comp_of_eq hg rfl

/-- **The bound of the composite for the cover of `𝔹`, with a layer-constant fluctuation, at one
point**: if `Φ` is bounded by `B` on `FlRealLC`, the composite is bounded by `B` at a point with
`Θ = D` in the chart, `ψ' ∈ FlBallLC H⁻ δ₁` and admissible `s`. -/
theorem fanLC_norm_le_cover {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2) {δ₁ BG₂ : ℝ} (hδ₁ : 0 < δ₁)
    (hPmp : Precedes Hm Gp)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : ℝ} (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ‖Φ t.1 t.2.1 t.2.2‖ ≤ B)
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁) :
    ‖Φ (F₁ (s, rawOf D)) (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1 (rawOf D, ψ')‖ ≤ B := by
  obtain ⟨φ, α, δφ, δα, -, hFeq, -, hSeq, hmem⟩ :=
    point_facts_core_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁ hPmp hF₁ hSol hs hs1 hD hψ.1
  rw [hFeq, hSeq]
  exact hΦbd _ ⟨hmem, hψ.2⟩

end FanLC

section FanHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*} [Fintype ι]

/-- **(AE1) for the local term with the local hat variable** (P3 (4.46) on `𝔹`, cover form).  The
fluctuation is the local hat lift `ψ' = cc C^{1/2}(s) ψ̂` of the cover of `𝔹` at the background
`F₁(s, Θ)` (extended by zero off the unit blocks of `𝔹`), and the parameters are `s = σ w` for an
analytic map `σ` from a polydisc of radius `e^κ` with `|σ w| < e^κ` and `σ w = 1` on the cubes
meeting `X₁`.  For `Φ` analytic on `FlRealLC`, the composite is analytic in `((Θ, ψ̂), w)` on the
chart `Ξ^c(𝔹; 1, ε')` times the ball `|ψ̂| ≤ c_ψ` times the polydisc.  Only the datum `Θ` of `𝔹`
enters. -/
theorem fanLocalHat_analytic_cover (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁)) :
    AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
        (ι → ℂ) =>
      Φ (F₁ (σ p.2, p.1.1))
        (Sol (σ p.2, flEdat Gp Hm (F₁ (σ p.2, p.1.1)) p.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) := by
  classical
  rintro ⟨⟨u, ψh⟩, w⟩ ⟨⟨⟨D, hD, rfl⟩, hψh⟩, hw⟩
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hs : ∀ P, ‖σ w P‖ < Real.exp κ := hσκ w hw
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC HBp hδ0
      (hc7.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hc7
      (xiCData_inDomainC HBp hsmall hD)
  -- the local hat lift at the point lies in the fluctuation ball of `H⁻`
  have hψ := localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS S HBp hκ.le hM hMX hCx hF₁
    heps hsmall hc7 hphi hmarD hαD hsm hs hD cc hcψ hδ₁0 hδ₁ hψh
  -- the fan composite is analytic at the image point
  have hA := fanLC_analyticAt_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁0 hPmp hF₁an hF₁
    hSolan hSol hΦ hs (hσ1 w) hD hψ
  -- the map `p ↦ ((Θ, ψ'(p)), σ w)` is analytic at the point
  obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS S HBp hκ.le hM heps hsmall hc7 hs hD
  have hFe : F₁ (σ w, rawOf D) = (φ, α) := hF₁ (σ w) D hs hU φ α ⟨hI.small, hI.fixed, hI.field⟩
  have hdom := decDom_of_coverBg hS S HBp hκ.le hM heps hsmall hc7 hphi hs hD hI hmarD hαD
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have SX : Dec2.XCover (coverOf Gp) Gp (compWeight L a₁) a₁ ν Cx :=
    ⟨S.toCoverGeom, hk1, ha₁, ha₂⟩
  set pt : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) :=
    ((rawOf D, ψh), w) with hpt
  have hσp : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) => σ p.2) pt :=
    (hσan w).comp_of_eq analyticAt_snd rfl
  have ha0 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) => (σ p.2, p.1.1)) pt :=
    hσp.prod (analyticAt_fst.comp analyticAt_fst)
  have ha1 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) => F₁ (σ p.2, p.1.1)) pt :=
    (hF₁an (σ w, rawOf D) ⟨hs, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have hφ1 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) => (F₁ (σ p.2, p.1.1)).1) pt :=
    analyticAt_fst.comp ha1
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) => p.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl
  have hmem' : (σ pt.2, (barField Gp pt.1.1.1 (F₁ (σ pt.2, pt.1.1)).1,
      (F₁ (σ pt.2, pt.1.1)).2)) ∈ DecDom Gp N κ δc := by
    show (σ w, (barField Gp D.Ψ (F₁ (σ w, rawOf D)).1, (F₁ (σ w, rawOf D)).2)) ∈ DecDom Gp N κ δc
    rw [hFe]; exact hdom
  have hlift := analyticAt_localHatLift_of_decDom (N := N) SX hCx hκ.le hMX hδc hsm cc
    (sF := fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ι → ℂ) => σ p.2)
    (ΨF := fun p => p.1.1.1) (φF := fun p => (F₁ (σ p.2, p.1.1)).1)
    (αF := fun p => (F₁ (σ p.2, p.1.1)).2) (ψh := fun p => p.1.2)
    (fun P => analyticAt_pi_iff.1 hσp P) hΨ1 (fun r => analyticAt_pi_iff.1 hφ1 r)
    (fun y => analyticAt_pi_iff.1 (analyticAt_snd.comp ha1) y)
    (fun r => analyticAt_pi_iff.1 (analyticAt_snd.comp analyticAt_fst) r) hmem'
  have hin : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ι → ℂ) =>
      ((p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
        if h : unitBlock x ∈ unitPts Gp then
          (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
            (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
            (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
        else 0), σ p.2)) pt :=
    ((analyticAt_fst.comp analyticAt_fst).prod hlift).prod hσp
  exact hA.comp_of_eq hin rfl

omit [Fintype ι] in
/-- **The bound of the local term with the local hat variable**: if `Φ` is bounded by `B` on
`FlRealLC`, the composite of `fanLocalHat_analytic_cover` is bounded by `B` on the chart times the
ball `|ψ̂| ≤ c_ψ` times the polydisc. -/
theorem fanLocalHat_norm_le_cover (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {B : ℝ} (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ‖Φ t.1 t.2.1 t.2.2‖ ≤ B) :
    ∀ p ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖Φ (F₁ (σ p.2, p.1.1))
        (Sol (σ p.2, flEdat Gp Hm (F₁ (σ p.2, p.1.1)) p.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf Gp) (σ p.2)) (barField Gp p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0)‖ ≤ B := by
  rintro ⟨⟨u, ψh⟩, w⟩ ⟨⟨⟨D, hD, rfl⟩, hψh⟩, hw⟩
  have hs : ∀ P, ‖σ w P‖ < Real.exp κ := hσκ w hw
  have hψ := localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS S HBp hκ.le hM hMX hCx hF₁
    heps hsmall hc7 hphi hmarD hαD hsm hs hD cc hcψ hδ₁0 hδ₁ hψh
  exact fanLC_norm_le_cover hS S HBp hκ hM heps hsmall hc7 hphi hδ₁0 hPmp hF₁ hSol hΦbd hs
    (hσ1 w) hD hψ

end FanHat

section BoxIntegral

variable {P I : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  [Fintype I]

/-- **A parameter integral over the real box `|ψ̂| ≤ c_ψ`** of a jointly analytic, bounded
integrand: if `(q, v) ↦ F q v` is analytic at `(q, v)` for `q ∈ S` and complex `v` with
`|v| ≤ c_ψ`, and bounded there by `B`, then `q ↦ ∫_{|ψ̂| ≤ c_ψ} F q ψ̂ dγ(ψ̂)` is analytic on `S`
and bounded by `B γ(box)`, for every measure `γ` of finite mass on the box. -/
theorem analyticOnNhd_setIntegral_box {γ : Measure (I → ℝ)} {cψ B : ℝ}
    (hγ : γ {ψ : I → ℝ | ∀ r, |ψ r| ≤ cψ} < ⊤) {S : Set P} {F : P → (I → ℂ) → ℂ}
    (hF : ∀ q ∈ S, ∀ v : I → ℂ, (∀ r, ‖v r‖ ≤ cψ) →
      AnalyticAt ℂ (fun x : P × (I → ℂ) => F x.1 x.2) (q, v))
    (hB : ∀ q ∈ S, ∀ v : I → ℂ, (∀ r, ‖v r‖ ≤ cψ) → ‖F q v‖ ≤ B) :
    AnalyticOnNhd ℂ (fun q => ∫ ψ in {ψ : I → ℝ | ∀ r, |ψ r| ≤ cψ},
        F q (fun r => (ψ r : ℂ)) ∂γ) S ∧
      ∀ q ∈ S, ‖∫ ψ in {ψ : I → ℝ | ∀ r, |ψ r| ≤ cψ}, F q (fun r => (ψ r : ℂ)) ∂γ‖ ≤
        B * (γ {ψ : I → ℝ | ∀ r, |ψ r| ≤ cψ}).toReal := by
  set K : Set (I → ℝ) := {ψ : I → ℝ | ∀ r, |ψ r| ≤ cψ} with hK
  have hKe : K = Set.pi Set.univ (fun _ : I => Set.Icc (-cψ) cψ) := by
    ext ψ
    simp only [hK, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
  have hKc : IsCompact K := by rw [hKe]; exact isCompact_univ_pi fun _ => isCompact_Icc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have : IsFiniteMeasure (γ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hγ⟩
  have hv : ∀ ψ ∈ K, ∀ r, ‖((fun r => (ψ r : ℂ)) : I → ℂ) r‖ ≤ cψ := fun ψ hψ r => by
    simpa [Complex.norm_real] using hψ r
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · exact analyticAt_integral_comp (P := P) (V := I → ℂ) (μ := γ.restrict K) hKc hKm
      (ae_restrict_mem hKm) (ι := fun ψ : I → ℝ => fun r => (ψ r : ℂ))
      (by fun_prop) (G := fun x : P × (I → ℂ) => F x.1 x.2)
      (fun ψ hψ => hF q hq _ (hv ψ hψ))
  · refine (norm_setIntegral_le_of_norm_le_const hγ (fun ψ hψ => hB q hq _ (hv ψ hψ))).trans ?_
    simp [Measure.real]

end BoxIntegral

section HatIntegral

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*} [Fintype ι]

/-- **The `ψ̂`-integral of the local term at a local chart point** (P3 (4.46) on `𝔹`, cover form;
W780 D3 "the hat variable").  For every measure `γ` of finite mass on the real box `|ψ̂| ≤ c_ψ` of
the unit lattice of `𝔹`, the function
`(Θ, w) ↦ ∫_{|ψ̂| ≤ c_ψ} Φ(F₁(σ w, Θ), Sol(σ w, …), (Θ, cc C^{1/2}(σ w) ψ̂)) dγ(ψ̂)`
is analytic on the local chart `Ξ^c(𝔹; 1, ε')` times the polydisc and bounded there by `B γ(box)`,
where `B` bounds `Φ` on `FlRealLC`.  The integrand at a chart point `Θ` is computed from `Θ`
alone (local background, local square root, local fluctuation field). -/
theorem fanLocalHat_integral_cover (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    {B : ℝ} (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ‖Φ t.1 t.2.1 t.2.2‖ ≤ B)
    {γ : Measure (unitPts Gp × Fin N → ℝ)}
    (hγ : γ {ψ : unitPts Gp × Fin N → ℝ | ∀ r, |ψ r| ≤ cψ} < ⊤) :
    AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι → ℂ) =>
        ∫ ψ in {ψ : unitPts Gp × Fin N → ℝ | ∀ r, |ψ r| ≤ cψ},
          Φ (F₁ (σ q.2, q.1))
        (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1)) q.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) ∧
    ∀ q ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖∫ ψ in {ψ : unitPts Gp × Fin N → ℝ | ∀ r, |ψ r| ≤ cψ},
          Φ (F₁ (σ q.2, q.1))
        (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1)) q.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0) ∂γ‖ ≤
        B * (γ {ψ : unitPts Gp × Fin N → ℝ | ∀ r, |ψ r| ≤ cψ}).toReal := by
  have hA := fanLocalHat_analytic_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7
    hphi hmarD hαD hsm cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hΦ
  have hB := fanLocalHat_norm_le_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7
    hphi hmarD hαD hsm cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁ hSol hσκ hσ1 hΦbd
  refine analyticOnNhd_setIntegral_box (P := RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι → ℂ))
    (F := fun (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι → ℂ))
      (v : unitPts Gp × Fin N → ℂ) =>
        Φ (F₁ (σ q.2, q.1))
        (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1)) q.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ v)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1 (F₁ (σ q.2, q.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ v)) (⟨unitBlock x, h⟩, i)
            else 0)) hγ ?_ ?_
  · rintro ⟨Θ, w⟩ ⟨hΘ, hw⟩ v hv
    have h := hA ((Θ, v), w) ⟨⟨hΘ, hv⟩, hw⟩
    refine h.comp_of_eq (((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd).prod
      (analyticAt_snd.comp analyticAt_fst)) rfl
  · rintro ⟨Θ, w⟩ ⟨hΘ, hw⟩ v hv
    exact hB ((Θ, v), w) ⟨⟨hΘ, hv⟩, hw⟩

end HatIntegral

section EvTermBound

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {c : ι → ℕ × CTorus d L N₁ m₁ K}
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
variable {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **The analyticity and the bound of the terms `𝓔(X, Y)` of Theorem I-5 without locality**: the
clauses 3 and 4 of `localization_expansion` use of (AE1)-(AE2) only (AE1) (the Cauchy bound of the
coefficients, (GM4) and the Peierls sum (GM3) over the connected families of the expansion of
`G`).  So for any `F` analytic on `S × {|s_i| < e^{κ₁}}` and bounded by `Eb e^{-(κ-1)Δ}` there,
`evTerm Y` is analytic on `S` and `|evTerm Y u| ≤ Eb e^{-κ₀ Δ - 2κ d̃^cov(Y)}`.  This applies to a
term recomputed on a local generating set, with the families of the expansion of the ambient set
`G`, before its locality is known. -/
theorem evTerm_bound_analyticOnNhd_of_bd (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κ κ₀ κ₁ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {S : Set U} {F : U → (ι → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F p.1 p.2)
      (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X)) :
    (∀ Y, ∀ u ∈ S, ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖ ≤
      Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κ * treeLenCov G m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y) S) := by
  classical
  have hκ1 : 1 ≤ κ₁ := by
    have : (1 : ℝ) ≤ 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) := by
      have hd1 : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have : (1 : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_pow _ _ (by omega)
      nlinarith
    nlinarith
  have hanau : ∀ u ∈ S, AnalyticOnNhd ℂ (F u) (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)) := by
    intro u hu s hs
    exact (hana (u, s) ⟨hu, hs⟩).comp (g := fun p : U × (ι → ℂ) => F p.1 p.2)
      (f := fun s' : ι → ℂ => (u, s')) ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))
  refine ⟨fun Y u hu => ?_, fun Y => ?_⟩
  · set Δ := treeLenCovOne m₀ j X with hΔ
    set T := treeLenCov G m₀ Y with hT
    have hterm : ∀ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y,
        ‖coef (F u) C‖ ≤ Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) *
          Real.exp (-(κ₁ / 2 - 1) * C.card) := by
      intro C hC
      obtain ⟨hconn, hY⟩ := (mem_connFams c).1 hC
      have h4 := gm4 hS hd hL hc C hconn hopt κ κ₀ κ₁ hκ₀ hκ hκ₁
      rw [hY] at h4
      refine (norm_coef_le_exp hκ1 (hanau u hu) (hbd u hu) C).trans ?_
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hEb
      nlinarith [h4]
    calc ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖
        ≤ ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, ‖coef (F u) C‖ := norm_sum_le _ _
      _ ≤ ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) *
          Real.exp (-(κ₁ / 2 - 1) * C.card) := Finset.sum_le_sum hterm
      _ = Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) *
          ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, Real.exp (-(κ₁ / 2 - 1) * C.card) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) * 1 :=
          mul_le_mul_of_nonneg_left (gm3_fam c hS hc hcinj hdisj Y _ h1 hlog)
            (by positivity)
      _ = _ := mul_one _
  · intro a ha
    unfold evTerm
    exact Finset.analyticAt_fun_sum _ fun C _ =>
      analyticOnNhd_coef_of_analyticOnNhd (Φ := fun p : U × (ι → ℂ) =>
        F p.1 p.2) (Real.one_lt_exp_iff.mpr (by linarith)) hana C a ha

end EvTermBound

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}

/-- **The `ψ̂`-integral of the E-part at a local chart point** (P3 (4.46)-(4.47) on
`𝔹 = localB t … Y⁺` at `ϱ = 5 L M₁`, `r₀ = 4 d L³ + L`).  The old-term functional
`Φ = eTermFun 𝔹 𝔹_k(X) 𝔹_j(X) H⁻ …` of the E-part, composed with the decoupled background of the
cover of `𝔹`, the local hat lift `ψ' = cc C^{1/2}(σ w) ψ̂` and the fluctuation field of `H⁻`, and
integrated in `ψ̂` over the box `|ψ̂| ≤ c_ψ` against `γ`, is analytic on the local chart
`Ξ^c_{k+1}(𝔹; 1, ε')` times the polydisc and bounded there by `Bd γ(box)`, `Bd` the bound of the
old term on its chart `Ξ^c_j(𝔹_j(X); b, b² ε' + K₂ δ₃ + K₂ δfl)` (the test (4.37) is the hypothesis
`hE`).  Instance of `fanLocalHat_integral_cover` with `localB_coverData`,
`localB_eTermFun_analytic` and `localB_eTermFun_bound`. -/
theorem localB_eTermHat_integral {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ} (ht : t ≤ k + 1)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1)
      (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB t ht Yp (le_refl (minSep L
          (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Yp (le_refl (minSep L
      (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData
      (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖
        < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1
          × Fin N → ℂ)
        (α : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
          (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
      (L ^ m₁)))))} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB t ht Yp
      (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f
        → σ w ⟨P, hP⟩ = 1)
    {γ : Measure (unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hγ : γ {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
      → ℝ | ∀ r, |ψ r| ≤ cψ} < ⊤)
    {Bd : ℝ} (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ Bd) :
    AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (ι → ℂ) =>
        ∫ ψ in {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
          → ℝ | ∀ r, |ψ r| ≤ cψ},
          eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
            (compWeight L a₁) Fk E (F₁ (σ q.2, q.1))
        (Sol (σ q.2, flEdat (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁
          (σ q.2, q.1)) q.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ q.2))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) q.1.1 (F₁
                  (σ q.2, q.1)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ q.2))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) q.1.1 (F₁
                  (σ q.2, q.1)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
      (XiCRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
        (k + 1) 1 eps ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) ∧
    ∀ q ∈ XiCRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
      (k + 1) 1 eps ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖∫ ψ in {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
        → ℝ | ∀ r, |ψ r| ≤ cψ},
          eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
            (compWeight L a₁) Fk E (F₁ (σ q.2, q.1))
        (Sol (σ q.2, flEdat (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁
          (σ q.2, q.1)) q.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ q.2))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) q.1.1 (F₁
                  (σ q.2, q.1)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ q.2))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) q.1.1 (F₁
                  (σ q.2, q.1)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ‖ ≤
        Bd * (γ {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
          → ℝ | ∀ r, |ψ r| ≤ cψ}).toReal := by
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  exact fanLocalHat_integral_cover hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L)
    hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
    hF.hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1
    (localB_eTermFun_analytic hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq colk colj hκ hM
      hnum dsX₀ hN hj hF hFkan hFk hE)
    (fun _ ht' => localB_eTermFun_bound hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq colk
      colj hκ hM hnum dsX₀ hN hj hF hFk hEb ht') hγ

/-- **The clauses `analyticE` and `boundE` of the successor class for the E-part recomputed on
`𝔹 = localB t … Y⁺`** (P3 (4.46)-(4.47)).  The term of the polymer `Y` is the sum, over the
connected families `𝒞` of the expansion of the ambient set `G` with `Y[𝒞] = Y`, of the
coefficients `coef(·, 𝒞)` in the parameters `w` of the `ψ̂`-integrated local E-part
(`localB_eTermHat_integral`), evaluated at the cut-off `clipRaw 𝔹 (Ψ, h)` of the pair of fields.
On the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` (field `dom` of `xiFieldDom`), `ε_{k+1} ≤ ε'`, it is
analytic and bounded by `Eb γ(box) e^{-κ₀ d^{cov,1}_j(X) - 2 κ d̃^{cov}(Y)}`, the bound of the
ambient term (`eterm_expansion_hat_rawY`) times the mass of the box.  Uses the chart nesting
`analyticOnNhd_comp_clipRaw_xiFieldDom` and `evTerm_bound_analyticOnNhd_of_bd` (no locality). -/
theorem localB_eTermHat_evTerm_xiFieldDom {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Ga m₀ j' X 𝒦X)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga) (hcinj : Function.Injective cI)
    (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec) (hEb0 : 0 ≤ Eb)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ} (ht : t ≤ k + 1)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1)
      (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB t ht Yp (le_refl (minSep L
          (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Yp (le_refl (minSep L
      (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData
      (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖
        < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1
          × Fin N → ℂ)
        (α : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
          (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
      (L ^ m₁)))))} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB t ht Yp
      (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f
        → σ w ⟨P, hP⟩ = 1)
    {γ : Measure (unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hγ : γ {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
      → ℝ | ∀ r, |ψ r| ≤ cψ} < ⊤)
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps) :
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X)
          (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
          ∫ ψ in {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
            → ℝ | ∀ r, |ψ r| ≤ cψ},
            eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
              (compWeight L a₁) Fk E (F₁ (σ w, Θ))
        (Sol (σ w, flEdat (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σ w, Θ)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σ w, Θ)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) Y (clipRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) p))
      {p | (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2} ∧
    ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ‖evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X)
          (fun (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ) =>
          ∫ ψ in {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
            → ℝ | ∀ r, |ψ r| ≤ cψ},
            eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
              (compWeight L a₁) Fk E (F₁ (σ w, Θ))
        (Sol (σ w, flEdat (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σ w, Θ)) Θ.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σ w, Θ)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (Θ, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ w, Θ)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁
                  (σ w, Θ)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) Y (clipRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) p)‖ ≤
        Eb * (γ {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
          → ℝ | ∀ r, |ψ r| ≤ cψ}).toReal *
          Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y) := by
  obtain ⟨hA, hB⟩ := localB_eTermHat_integral hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk
    HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hE hmarD hαD hsm cc hcψ
    hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hγ hEb
  have hγ0 : 0 ≤ (γ {ψ : unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N
    → ℝ | ∀ r, |ψ r| ≤ cψ}).toReal := ENNReal.toReal_nonneg
  have hEv := evTerm_bound_analyticOnNhd_of_bd (c := cI)
    (U := RawData d L (N₁ * L ^ m₁) (k + 1) N)
    hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hκκ h1 hlog (mul_nonneg hEb0 hγ0) hA
    (fun u hu s hs => by
      have := hB (u, s) ⟨hu, hs⟩
      rw [mul_right_comm]
      exact this)
  exact ⟨analyticOnNhd_comp_clipRaw_xiFieldDom hεseq (hEv.2 Y),
    fun p hp => norm_comp_clipRaw_le_xiFieldDom hεseq (fun r hr => hEv.1 Y r hr) hp⟩

end LocalB

end Balaban.Localization
