/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineLocalEngine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `ψ̂`-local engine on layer-constant fluctuations

`i5_functional_hat` takes the functional `Φ` analytic, bounded and local on the realizable triples
`FlReal`, whose fluctuation `ψ'` is only known to lie in the ball `FlBall`.  A functional that
needs the fluctuation to be a block field (`IsLayerConstant`), such as the composite of an old term
with the fluctuation datum (`flDatum` requires a layer-constant perturbation), is analytic only on
the realizable triples with layer-constant fluctuation, `FlRealLC`.  The fluctuations `ψ'(s) =
liftC (cc • C^{1/2}(s) ψ̂)` of the fan are layer constant (`isLayerConstant_liftC`); so the
analyticity, locality and engine theorems hold with `FlReal` replaced by `FlRealLC`
(`fanHL_analytic`, `fanHL_local`, `i5_functional_hatLC`), by the proofs of the `FlReal` versions.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section EngineLC

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The realizable triples with layer-constant fluctuation.** -/
def FlRealLC (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) (a₁ ν BG κ eps : ℝ)
    (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (BG₂ δ₁ : ℝ) : Set (((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
    (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) :=
  {t | t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁ ∧ IsLayerConstant Hm t.2.2.2}

section Fan

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **(AE1), analyticity, with the fluctuation decoupled by the cover parameters.**  The
generalization of `fanF_analytic`: the fluctuation is `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` for the
hat variable `ψ̂ ∈ Bhat`, with `C^{1/2}(s)` the decoupled square root at the background
`F₁(s, Θ)`.  The hypothesis `hSup` (that `ψ'(s)` stays in the ball of fluctuations on the polydisc)
is INTERNAL: it is the complex-`s` sup bound of `decCovSqrt` (`decCovSqrt_supNorm`, proved
separately by W151) together with `liftC_mem_flBallLC`, and is to be discharged by it; the other
extra hypotheses are the numerical conditions `hMX`, `hmar`, `hα`, `hsm` of the covariance
analyticity on `DecDom`. -/
theorem fanHL_analytic (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (Bhat : Set (unitPts Gp × Fin N → ℂ))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
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
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D → ∀ ψh ∈ Bhat,
      hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁) :
    AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
      Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2, p.1.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2, p.1.1))
            p.1.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2) p.1.1 p.1.2))).1
        (p.1.1, hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2) p.1.1 p.1.2))
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Bhat) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) := by
  classical
  rintro ⟨⟨u, ψh⟩, s⟩ ⟨⟨⟨D, hD, rfl⟩, hψh⟩, hs⟩
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hψ0 := hSup s hs D hD ψh hψh
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ0
  set pt : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) := ((rawOf D, ψh), s) with hpt
  set g0 : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N :=
    fun p => (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2, p.1.1) with hg0
  have hext : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
      extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2) pt :=
    (analyticAt_extParams s).comp_of_eq analyticAt_snd rfl
  have ha0 : AnalyticAt ℂ g0 pt := hext.prod (analyticAt_fst.comp analyticAt_fst)
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hd0 : 0 < d := by have := hC.HBp.hd; omega
    have hc1 := one_le_xiC1 d
    have hε := hC.eps_pos
    have hδ0 : 0 < xiC1 d * eps := by positivity
    exact inUnionDomainC_of_inDomainC hC.HBp hδ0
      (hC.c7le.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hC.c7le
      (xiCData_inDomainC hC.HBp hC.small1 hD)
  have ha1 : AnalyticAt ℂ (fun p => F₁ (g0 p)) pt :=
    (hF₁an (g0 pt) ⟨hsx, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have hφ1 : AnalyticAt ℂ (fun p => (F₁ (g0 p)).1) pt := analyticAt_fst.comp ha1
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
      p.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl
  -- membership of the background in `DecDom`
  have hFpt : F₁ (g0 pt) = (φ, α) := hFeq
  have hdec : (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      (barField Gp D.Ψ φ, α)) ∈ DecDom Gp N κ δc :=
    decDom_of_isDecBg hC hsx hD hI hmar hα
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have hd0 : 0 < d := by have := hC.HBp.hd; omega
      have hε := hC.eps_pos
      have hc1 := one_le_xiC1 d
      have hδ0 : 0 < xiC1 d * eps := by positivity
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hψan : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
      hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2)
        p.1.1 p.1.2) pt := by
    have hmem' : (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) pt.2,
        (barField Gp (pt.1.1.1) (F₁ (g0 pt)).1, (F₁ (g0 pt)).2)) ∈ DecDom Gp N κ δc := by
      rw [hFpt]; exact hdec
    have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
    have hh := analyticAt_hatPsi_of_decDom (N := N) hG' hX hC.hκ.le hMX hδc hsm cc
      (sF := fun p => extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2)
      (ΨF := fun p => p.1.1.1) (φF := fun p => (F₁ (g0 p)).1) (αF := fun p => (F₁ (g0 p)).2)
      (ψh := fun p => p.1.2) (fun P => analyticAt_pi_iff.1 hext P) hΨ1
      (fun r => analyticAt_pi_iff.1 hφ1 r)
      (fun y => analyticAt_pi_iff.1 (analyticAt_snd.comp ha1) y)
      (fun r => analyticAt_pi_iff.1 (analyticAt_snd.comp analyticAt_fst) r) hmem'
    exact hh
  set ed : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → Edat Hm N :=
    fun p => flEdat Gp Hm (F₁ (g0 p)) p.1.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2) p.1.1 p.1.2) with hed
  have haed : AnalyticAt ℂ ed pt := by
    refine AnalyticAt.prod (analyticAt_barField (fun p => (F₁ (g0 p)).1) (fun p => p.1.1.1)
      (fun r => analyticAt_pi_iff.1 hφ1 r) hΨ1) (AnalyticAt.prod
      (analyticAt_flAlpha (fun p => (F₁ (g0 p)).2) (fun y => analyticAt_pi_iff.1
        (analyticAt_snd.comp ha1) y))
      (AnalyticAt.prod hψan analyticAt_const))
  have hedpt : ed pt = flEdat Gp Hm (φ, α) D.Ψ
      (hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
        (rawOf D) ψh) := by
    show flEdat Gp Hm (F₁ (g0 pt)) D.Ψ _ = _
    rw [hFpt]
  have hSolpt : AnalyticAt ℂ (fun p => Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2,
      ed p)) pt := by
    refine (hSolan (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, ed pt)
      ⟨hsx, ?_⟩).comp_of_eq (hext.prod haed) rfl
    rw [hedpt]; exact hstrict
  have hg : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
      (F₁ (g0 p), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2, ed p)).1,
        (p.1.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.2) p.1.1 p.1.2))) pt :=
    ha1.prod ((analyticAt_fst.comp hSolpt).prod
      ((analyticAt_fst.comp analyticAt_fst).prod hψan))
  have hval : (F₁ (g0 pt), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) pt.2,
      ed pt)).1, (pt.1.1, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) pt.2) pt.1.1 pt.1.2)) =
      ((φ, α), δφ, (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)) := by
    show (F₁ (g0 pt), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      ed pt)).1, _) = _
    rw [hFpt, hedpt, hSeq]
  have hΦpt := hΦ _ ⟨hmem, isLayerConstant_liftC hG hG' _⟩
  rw [← hval] at hΦpt
  exact hΦpt.comp_of_eq hg rfl


/-- **(AE2), locality, for a functional of the decoupled objects with the fluctuation decoupled by
the cover parameters.**  If `Φ` depends on the triple only through its values on a set
`Z ⊆ X₁`, the composite is local in `(Θ, ψ̂)`, with agreement of `ψ̂` on the unit points of the
thick set. -/
theorem fanHL_local (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
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
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦloc : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ psiThick Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    LocalityAEOn (Real.exp κ)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => AgHat hG' (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)) ) C) u u')
      (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  classical
  rintro C ⟨u, ψh⟩ ⟨u', ψh₂⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ ⟨⟨D', hD', rfl⟩, hψh₂⟩ s s' hs hs' hag hAg
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  set cmap : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  have hψ : hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
      (rawOf D) ψh ∈ FlBall Hm δ₁ :=
    (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hsx hD hψh).1
  have hψ₂ : hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s')
      (rawOf D') ψh₂ ∈ FlBall Hm δ₁ :=
    (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hsx' hD' hψh₂).1
  set ψ := hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
    (rawOf D) ψh with hψdef
  set ψ₂ := hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s')
    (rawOf D') ψh₂ with hψ₂def
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hFeq', hstrict', hSeq', hmem'⟩ :=
    point_facts_core hC hF₁ hSol hsx' hs1' hD' hψ₂
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ ψ)).1 (rawOf D, ψ) =
    Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s',
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
          D'.Ψ ψ₂)).1 (rawOf D', ψ₂)
  rw [hFeq, hFeq', hSeq, hSeq']
  -- notation
  set Yc : Set (CTorus d L N₁ m₁ (k + 1)) := compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := C.image cmap with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hcc_mem : ∀ i, cmap i ∈ cubeIdx Gp := fun i => i.1.2
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hPatchΩ : patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C ⊆
      ↑(Gp.Ω 1) := by
    intro x hx
    rcases hx with hx | hx
    · exact hX₁Ω hx
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact Pset_subset_Omega1 hcov (hcc_mem i) hxi
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cmap C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cmap C).1 hy.1) hadj)
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f →
      Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    intro P hP
    by_contra hnd
    have hsub := Pset_subset_of_not_disjoint (hX₁ ▸ hcov.polySetup) P.2 hnd
    unfold parCubes at hP
    rw [Finset.mem_filter] at hP
    apply hP.2
    intro y hy
    have := hsub (mem_cubeP.1 hy)
    exact Finset.mem_coe.1 this
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) ∉ C := fun hi =>
      hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨P, hPc⟩ =
        s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨P, hPc⟩ =
        s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs.1 _ hi, hs'.1 _ hi⟩
  have hsub : ∀ P ∈ 𝒞, (∀ x ∈ cubeP P, x ∈ Y) →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cmap i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub x (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨cmap i, hcc_mem i⟩ = s i from
        extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨cmap i, hcc_mem i⟩ = s' i from
        extParams_par s' i]
    exact this
  -- the data domain
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  have hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
      D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y) := by
    intro x hx y hy
    have := hAgΘ y (Or.inr ⟨x, (hmemY x).1 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    refine hsub P hP𝒞 (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    exact hSub ⟨x, Pset_subset_Omega1 hcov (hcc_mem i) (mem_cubeP.1 hx)⟩ hx
  have hYYc : (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) = Yc := by
    ext x; exact hmemY x
  have hψloc : ∀ y ∈ psiThick (↑Y : Set (CTorus d L N₁ m₁ (k + 1))), ψ y = ψ₂ y :=
    hatPsiF_local hC hk hG' cc hconn hMX hdm hα hsm hF₁ hsx hsx' hD hD' hYnn hs1E hs0E hagE
      hdata ψh ψh₂ (fun y hy i => hAgψ y (by rwa [hYYc] at hy) i)
  -- the background fields agree
  obtain ⟨hαSY, hφY⟩ := i4b_local hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hYnn
    hs1E hs0E hagE hdata hI hI'
  -- the geometry of the pair
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hC.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hcc_mem i
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hC.hPmp.mem_Ω1 hx
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hYnn
  -- the fluctuation fields agree
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ₂ with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e') hsx' hstrict'
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  have Hh : DecHyp Hm (compWeight L a₁) ν false e.2.1 e.1 e.2.2.1 e.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false e'.2.1 e'.1 e'.2.2.1 e'.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have hDA : Dec2.DataAgreeS Hm N Y (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁f 𝒞 Y)
      e.2.1 e'.2.1 e.1 e'.1 e.2.2.1 e'.2.2.1 e.2.2.2 e'.2.2.2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun y hy hxy => ?_, fun x hx i => rfl⟩
    · have := hαSY ⟨x, hsubΩ x x.2⟩ (SYF_subset_SY SL hconn' hsubΩ hYnn hx)
      show flAlpha Gp Hm α x = flAlpha Gp Hm α' x
      rw [flAlpha_of_prec hC.hPmp, flAlpha_of_prec hC.hPmp]
      exact this
    · have hxΩ := hsubΩ x x.2
      funext i
      show barField Gp D.Ψ φ x i = barField Gp D'.Ψ φ' x i
      simp only [barField, hxΩ, ↓reduceDIte]
      exact hφY ⟨x, hxΩ⟩ hx i
    · exact hψloc x (Or.inl (Finset.mem_coe.2 hx))
    · obtain ⟨x, hx, hadj⟩ := hxy
      exact hψloc y (Or.inr ⟨x, Finset.mem_coe.2 hx, hadj⟩)
  have hflloc := Dec2.i4a_local_fpS hC.hS2.fam hC.SM hC.hκ.le hC.hM2 (fun P => (hsx P).le)
    (fun P => (hsx' P).le) Hh Hh' hC.B_le hC.δ₁_le hIU hs1E hs0E
    (fun P hP hPA => hsub P hP (hAcube P hPA).2) hDA
    hfix hs6 hfix' hs6'
  have hδeq : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i) := by
    intro y hy i
    have h1 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e)).1 = δφ :=
      congrArg Prod.fst hSeq
    have h2 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e')).1 = δφ' :=
      congrArg Prod.fst hSeq'
    rw [← h1, ← h2, hfld, hfld']
    exact hflloc.2 y hy i
  have hZY : ∀ y ∈ Z, y ∈ Yc := fun y hy =>
    subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (hZ hy)
  have hXY' : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hαeq : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → α y = α' y := by
    intro y hy
    obtain ⟨z, hz, hyz, hQ, hhat⟩ := hBM y hy y.2
    refine hαSY y (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_, ?_⟩, hyz⟩)
    · intro P hP hPpar
      exact absurd hPpar (hQ P hP)
    · intro x hx
      exact hXY' _ (hhat x hx)
  refine hΦloc _ ⟨hmem, isLayerConstant_liftC hG hG' _⟩ _ ⟨hmem', isLayerConstant_liftC hG hG' _⟩ (fun y hy i => ?_) (fun y hy => hαeq y hy) (fun y hy i => ?_) ?_ ?_
  · exact hφY y ((hmemY _).2 (hZY _ hy)) i
  · exact hδeq y ((hmemY _).2 (hZY _ hy)) i
  · exact agreeOn_mono (thickSet_mono (fun y hy => hZY y hy)) hAgΘ
  · exact fun y hy => hψloc y (psiThick_mono (fun y hy => Finset.mem_coe.2 ((hmemY y).2 (hZY y hy))) hy)


end Fan

section Functional

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **Theorem I-5 for a functional of the decoupled objects, with the fluctuation decoupled by the
cover parameters** (the version of `i5_functional` for `Φ(φ_{k+1}(s), δφ(s), Θ, ψ'(s))`,
`ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)`).  Let `Φ` be analytic and bounded by `Eb` on the realizable
triples and depend only on the values on `Z ⊆ X₁`.  Then at `s = 1`
`Φ(φ_{k+1}, δφ, Θ, ψ') = ∑_{Y ⊃ X₁} Ev_Y(Θ, ψ̂)` with `ψ' = liftC (cc • C^{1/2}(1) ψ̂)`, the terms
analytic in `(Θ, ψ̂)`, depending on `Θ` through its restriction to the thickening of `Y` and on `ψ̂`
through its values at the unit points of the sites whose `(k+1)`-block meets `Y` or a neighbour of
`Y`, and bounded by `Eb e^{-κ₀ Δ - 2 κ d̃^{cov}_{k+1}(Y)}`. -/
theorem i5_functional_hatLC (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦloc : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ psiThick Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))
          (rawOf D, liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    intro σ hσ D hD ψh hψh
    have hs' : ∀ i, ‖σ i‖ < Real.exp κ := fun i => by simpa using hσ i
    exact (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁
      (norm_extParams_lt hE1 hs') hD hψh).1
  set F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ :=
    fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
      (u.1, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) with hF'
  have hana := fanHL_analytic hC hk hG hG' cc {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}
    hMX hdm hα hsm hF₁an hF₁ hSolan hSolprop hΦan hSup
  have hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    rintro ⟨u1, ψh⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
      norm_extParams_lt hE1 hs'
    have hψ := hSup s hs D hD ψh hψh
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core hC hF₁ hSolprop hsx
      (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ
    show ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ (hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh))).1
      (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)‖ ≤ _
    rw [hFeq, hSeq]
    exact hΦbd _ ⟨hmem, isLayerConstant_liftC hG hG' _⟩
  have hloc := fanHL_local hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hF₁
    hSolprop hZ hBM hΦloc
  obtain ⟨Ev, hsum, hlocY, hbound, hanY⟩ := expansion_of_AE_hat (a₁ := a₁) hC.HBp.hd hC.HBp.hL
    hG' hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hana hbd hloc
  refine ⟨Ev, fun D hD ψh hψh => ?_, hlocY, hbound, hanY⟩
  have hsum' := hsum (rawOf D, ψh) ⟨⟨D, hD, rfl⟩, hψh⟩
  rw [← hsum']
  have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
    fun P => by simpa using hE1
  have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
  have hψ1 := (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hsx hD hψh).1
  symm
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
          D.Ψ (hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh))).1
      (rawOf D, hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh) = _
  rw [extParams_one]
  set ψ' := hatPsiF Gp a₁ ν hG' cc F₁ (fun _ => 1) (rawOf D) ψh with hψ'def
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ1
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
    hνε hDom hI
  -- the fluctuation field at `s = 1`
  have hψeq : ψ' = liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
      (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
      (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
      (unitQ Gp) (unitP Gp) *ᵥ ψh)) := by
    rw [hψ'def]
    unfold hatPsiF hatSqrtF
    rw [hFeq, extS_one, hφ1, hα1]
    rfl
  rw [← hψeq]
  rw [hFeq, hSeq]
  obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
    flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
  have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
    (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
    (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
  have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = δφ := by
    have hSol1 : (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
        flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := congrArg Prod.fst hSeq
    unfold flFieldOne flField
    rw [hφ1, hα1]
    exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
      (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
      (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
      (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
      (hfld.symm.trans hSol1)
  rw [hφ1, hα1, hfl]


end Functional

end EngineLC

end Balaban.Localization
