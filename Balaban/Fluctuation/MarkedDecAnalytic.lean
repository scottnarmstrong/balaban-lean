/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedDecBall

/-!
# Analyticity of the masked decoupled tangent (`MARK-AN`)

The masked decoupled tangent `markedHatPsiF … Z u t s Θ ψ̂` is analytic in the data, the hat
variable, the cut parameters and the two complex marks.

* `analyticAt_markedHatPsiF_of_decDom`: the marked analogue of `analyticAt_hatPsi_of_decDom`, with
  `u` and `t` analytic functions of the parameter;
* `analyticOnNhd_markedHatPsiF`: the joint statement on
  `((Ξ^c × Bhat) × polydisc) × (ℂ × ℂ)`, the product used by `fanH_analytic` with the factor
  `ℂ × ℂ` of marks adjoined.

`MARK-FAN`, `MARK-COUNT` (decoupled) and `MARK-PARAM` are NOT proved here; no mark family is
constructed; nothing depends on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Analytic

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **Analyticity of the masked tangent at a point of `DecDom`.**  Same hypotheses as
`analyticAt_hatPsi_of_decDom`, with the marks `u, t` analytic functions of the parameter. -/
theorem analyticAt_markedHatPsiF_of_decDom (hG' : IsLevel Gp (k + 1))
    (hC : XSetting Gp (compWeight L a₁) a₁ ν)
    (hκ : 0 ≤ κ) (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδ : 0 ≤ δc)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) (Z : Finset (unitPts Gp)) {q : Q}
    {sF : Q → DecParams Gp} {ΨF : Q → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φF : Q → Gp.Ω 1 × Fin N → ℂ} {αF : Q → Gp.Ω 1 → ℂ} {ψh : Q → unitPts Gp × Fin N → ℂ}
    {uF tF : Q → ℂ} (hu : AnalyticAt ℂ uF q) (ht : AnalyticAt ℂ tF q)
    (hs : ∀ P, AnalyticAt ℂ (fun q => sF q P) q)
    (hΨ : ∀ y j, AnalyticAt ℂ (fun q => ΨF q y j) q)
    (hφ : ∀ r, AnalyticAt ℂ (fun q => φF q r) q) (hα : ∀ y, AnalyticAt ℂ (fun q => αF q y) q)
    (hψ : ∀ r, AnalyticAt ℂ (fun q => ψh q r) q)
    (hmem : (sF q, (barField Gp (ΨF q) (φF q), αF q)) ∈ DecDom Gp N κ δc) :
    AnalyticAt ℂ (fun q => uF q • liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
        (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q)) +
      tF q • liftC hG' (maskBlock Z (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
        (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q)))) q := by
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
    exact AnalyticAt.comp (f := fun q => (sF q, (barField Gp (ΨF q) (φF q), αF q))) hg he
  have hv : AnalyticAt ℂ (fun q => cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q)) q := by
    rw [analyticAt_pi_iff]
    intro r
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun t _ => (hent r t).mul (hψ t))
  have hmv : AnalyticAt ℂ (fun q => maskBlock Z (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q))) q := by
    rw [analyticAt_pi_iff]
    intro r
    unfold maskBlock
    by_cases h : r.1 ∈ Z
    · simp only [h, ite_true]; exact analyticAt_pi_iff.1 hv r
    · simp only [h, ite_false]; exact analyticAt_const
  exact (hu.smul (analyticAt_liftC hG' hv)).add (ht.smul (analyticAt_liftC hG' hmv))

section Main

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **`MARK-AN`.**  The masked decoupled tangent is jointly analytic in
`(Θ, ψ̂, s, u, t)` at every point of `((Ξ^c × Bhat) × polydisc) × (ℂ × ℂ)`, with the cut
parameters `extParams Gp X₁f s` as in `fanH_analytic`.  The hypotheses are those of `fanH_analytic`
that concern the background and the square root (`hk`, `hMX`, `hmar`, `hα`, `hsm`, `hF₁an`, `hF₁`);
no bound on `ψ̂` is needed, because membership of the background in `DecDom` does not involve it. -/
theorem analyticOnNhd_markedHatPsiF (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (Bhat : Set (unitPts Gp × Fin N → ℂ)) (Z : Finset (unitPts Gp))
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
        F₁ (s, rawOf D) = (φ, α)) :
    AnalyticOnNhd ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) × (ℂ × ℂ) =>
      markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2)
      (((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Bhat) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) ×ˢ (Set.univ : Set (ℂ × ℂ))) := by
  classical
  rintro ⟨⟨⟨u, ψh⟩, s⟩, ⟨a, b⟩⟩ ⟨⟨⟨⟨D, hD, rfl⟩, hψh⟩, hs⟩, -⟩
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hFpt := hF₁ _ D hsx hU φ α hI
  have hdec := decDom_of_isDecBg hC hsx hD hI hmar hα
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  set pt : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) × (ℂ × ℂ) :=
    (((rawOf D, ψh), s), (a, b)) with hpt
  set g0 : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) × (ℂ × ℂ) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N :=
    fun p => (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2, p.1.1.1) with hg0
  have hext : AnalyticAt ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) ×
      (ℂ × ℂ) => extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) pt :=
    (analyticAt_extParams s).comp_of_eq (analyticAt_snd.comp analyticAt_fst) rfl
  have ha0 : AnalyticAt ℂ g0 pt :=
    hext.prod (analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst))
  have ha1 : AnalyticAt ℂ (fun p => F₁ (g0 p)) pt :=
    (hF₁an (g0 pt) ⟨hsx, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have hφ1 : AnalyticAt ℂ (fun p => (F₁ (g0 p)).1) pt := analyticAt_fst.comp ha1
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) ×
      (ℂ × ℂ) => p.1.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq
      (analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)) rfl
  have hmem' : (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      (barField Gp (rawOf D).1 (F₁ (g0 pt)).1, (F₁ (g0 pt)).2)) ∈ DecDom Gp N κ δc := by
    show _ ∈ _
    have : F₁ (g0 pt) = (φ, α) := hFpt
    rw [this]; exact hdec
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hmain := analyticAt_markedHatPsiF_of_decDom (N := N) hG' hX hC.hκ.le hMX hδc hsm cc Z
    (sF := fun p => extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2)
    (ΨF := fun p => p.1.1.1.1) (φF := fun p => (F₁ (g0 p)).1) (αF := fun p => (F₁ (g0 p)).2)
    (ψh := fun p => p.1.1.2) (uF := fun p => p.2.1) (tF := fun p => p.2.2)
    (analyticAt_fst.comp analyticAt_snd) (analyticAt_snd.comp analyticAt_snd)
    (fun P => analyticAt_pi_iff.1 hext P) hΨ1
    (fun r => analyticAt_pi_iff.1 hφ1 r)
    (fun y => analyticAt_pi_iff.1 (analyticAt_snd.comp ha1) y)
    (fun r => analyticAt_pi_iff.1
      (analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)) r) hmem'
  simp only [markedHatPsiF, hatPsiF, hatSqrtF]
  exact hmain

end Main

end Analytic

end Balaban.Localization
