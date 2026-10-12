/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineDom
public import Balaban.Fluctuation.HatEngineLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fan with the fluctuation decoupled by the cover parameters

The fluctuation field `ψ'(s) = β^{-1/2} C^{1/2}(s) ψ̂` is built from the decoupled square root
`decCovSqrt` at the same parameters `s` as the background objects: with `(φ, α) = F₁(s, Θ)`,
`C^{1/2}(s) = decCovSqrt Gp (compWeight L a₁) a₁ ν α (extS s) (φ̄) (unitQ) (unitP)`,
`φ̄ = barField Gp Ψ φ`, and `ψ'(s) = liftC (c • C^{1/2}(s) ψ̂)`.

* `hatSqrtF`, `hatPsiF`: these objects;
* `fanH_analytic`: analyticity of `(Θ, ψ̂, σ) ↦ Φ(F₁, Sol(s, flEdat (ψ'(s))).1, (Θ, ψ'(s)))`
  on the product of `Ξ^c`, a set of hat variables and the polydisc, generalizing
  `fanF_analytic`.  The complex-`s` sup bound of `decCovSqrt` (being proved separately) enters
  only as the explicit hypothesis `hSup` of this internal lemma, which keeps `ψ'(s)` in the ball
  of fluctuations.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Fan

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

variable (Gp a₁ ν) in
/-- **The decoupled square root** `C^{1/2}(s)` at the background `F₁(s, Θ) = (φ, α)`:
`decCovSqrt` with the multiplier `α`, the parameters `s` and the constraint field
`φ̄ = barField Gp Ψ φ`. -/
noncomputable def hatSqrtF
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ :=
  decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, Θ)).2 (extS Gp s)
    (barField Gp Θ.1 (F₁ (s, Θ)).1) (unitQ Gp) (unitP Gp)

variable (Gp a₁ ν) in
/-- **The fluctuation field** `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` (`cc = β^{-1/2}`). -/
noncomputable def hatPsiF (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  liftC hG' (cc • (hatSqrtF Gp a₁ ν F₁ s Θ *ᵥ ψh))

section Analytic

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **Analyticity of the fluctuation field in the data**: if `(s, (φ̄, α))` lies in `DecDom` at the
point `q` and `s, Ψ, φ, α, ψ̂` are analytic in `q`, then `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` is
analytic at `q`.  (Entries of `C^{1/2}` are analytic on `DecDom`, I-4c (iii).) -/
theorem analyticAt_hatPsi_of_decDom (hG' : IsLevel Gp (k + 1)) (hC : XSetting Gp (compWeight L a₁) a₁ ν)
    (hκ : 0 ≤ κ) (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδ : 0 ≤ δc)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {q : Q}
    {sF : Q → DecParams Gp} {ΨF : Q → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φF : Q → Gp.Ω 1 × Fin N → ℂ} {αF : Q → Gp.Ω 1 → ℂ} {ψh : Q → unitPts Gp × Fin N → ℂ}
    (hs : ∀ P, AnalyticAt ℂ (fun q => sF q P) q)
    (hΨ : ∀ y j, AnalyticAt ℂ (fun q => ΨF q y j) q)
    (hφ : ∀ r, AnalyticAt ℂ (fun q => φF q r) q) (hα : ∀ y, AnalyticAt ℂ (fun q => αF q y) q)
    (hψ : ∀ r, AnalyticAt ℂ (fun q => ψh q r) q)
    (hmem : (sF q, (barField Gp (ΨF q) (φF q), αF q)) ∈ DecDom Gp N κ δc) :
    AnalyticAt ℂ (fun q => liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q))) q := by
  classical
  have hbar := analyticAt_barField (Gp := Gp) φF ΨF hφ hΨ
  have he : AnalyticAt ℂ (fun q => (sF q, (barField Gp (ΨF q) (φF q), αF q))) q :=
    AnalyticAt.prod (analyticAt_pi_iff.2 hs) (hbar.prod (analyticAt_pi_iff.2 hα))
  have hU := (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
  have hent : ∀ p r, AnalyticAt ℂ (fun q => decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) p r) q := by
    intro p r
    have hg : AnalyticAt ℂ (fun e : DecData Gp N =>
        decCovSqrt Gp (compWeight L a₁) a₁ ν e.2.2 (extS Gp e.1) e.2.1 (unitQ Gp) (unitP Gp) p r)
        (sF q, (barField Gp (ΨF q) (φF q), αF q)) :=
      analyticOnNhd_decCovSqrt_entry (N := N) hC hκ hM hδ hsm hU p r _ hmem
    have hg' := hg
    exact AnalyticAt.comp (f := fun q => (sF q, (barField Gp (ΨF q) (φF q), αF q))) hg' he
  have hv : AnalyticAt ℂ (fun q => cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q)) q := by
    rw [analyticAt_pi_iff]
    intro r
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun t _ => (hent r t).mul (hψ t))
  exact analyticAt_liftC hG' hv

end Analytic

section Main

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
theorem fanH_analytic (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
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
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
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
  have hΦpt := hΦ _ hmem
  rw [← hval] at hΦpt
  exact hΦpt.comp_of_eq hg rfl

end Main

end Fan

end Balaban.Localization
