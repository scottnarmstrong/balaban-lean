/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoEv
public import Balaban.Fluctuation.LocalPairReplacementLocalB
public import Balaban.Fluctuation.FlCoreCover
public import Balaban.Fluctuation.LocalHatTerm
import Mathlib.Tactic.Linarith

/-!
# The one-torus premises of the transport of the recomputed terms

The premises of `OmegaIso.evDecBg_canon_twoTorus_core` on one torus, from the standing hypotheses
of the local pair `(Gb, H⁻)` (`FlCore`, the cover base and specifications of the decoupled
background) and the defining properties of the decoupling pair `(F₁, Sol)`, at a datum of the chart
of `Gb`, a bounded hat variable and marks of the radius set:

* `evDecBg_pairPremises`: at every parameter of modulus `< e^κ`, the uniqueness property of
  `F₁`, the existence of the decoupled background, and the properties of `Sol` (field, fixed point,
  ball of radius `c₆'`, uniqueness in that ball) at the data of the masked local hat field
  (`coverBg_exists`, `markedHatPsiFBg_liftZ_mem_flBallLC_core`, `strictDataM_flEdat_cover`).
* `evDecBg_fanAnalytic`: the analyticity of the marked functional in the cut parameters on the
  polydisc (`fanLocalHatMarked_analytic_cover` on the slice of the datum).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **The premises of the decoupling pair at every parameter of the polydisc** (one torus). -/
theorem evDecBg_pairPremises {a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁) (hk : 1 ≤ k) (hHm : Hm.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {D : BgData Gb N} (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (Zm : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁) :
    (∀ σ : DecParams Gb, (∀ P, ‖σ P‖ < Real.exp κ) →
      ∀ φ α, Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) σ D φ α →
        F₁ (σ, rawOf D) = (φ, α)) ∧
    (∀ σ : DecParams Gb, (∀ P, ‖σ P‖ < Real.exp κ) →
      ∃ φ α, Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) σ D φ α) ∧
    (∀ σ : DecParams Gb, (∀ P, ‖σ P‖ < Real.exp κ) →
      let p : Dec2.DecParams (coverOf Gb) × Edat Hm N :=
        (σ, flEdat Gb Hm (F₁ (σ, rawOf D)) D.Ψ
          (markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm σ (rawOf D) (resZ Gp Gb ψh)))
      (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        (∀ δα', Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδ0 : 0 < xiC1 d * eps := by
    have := one_le_xiC1 d; have := hC.eps_pos; positivity
  have hU : InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0
      (hC.c7le.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hC.c7le
      (xiCData_inDomainC hC.HBp hC.small1 hD)
  have hF₁o : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α) := fun s D hs hD' φ α hI =>
    hF₁ s D hs hD' φ α ((dec2_isDecBg_iff Gb _ _ _ s D φ α).2 hI)
  refine ⟨fun σ hσ φ α hI => hF₁ σ D hσ hU φ α hI, fun σ hσ => ?_, fun σ hσ => ?_⟩
  · obtain ⟨φ, α, hI, -, -⟩ := coverBg_exists hS Sb hC.HBp hC.hκ.le hC.hM hC.eps_pos hC.small1
      hC.c7le hσ hD
    exact ⟨φ, α, (dec2_isDecBg_iff Gb _ _ _ σ D φ α).2 hI⟩
  · have hψ := markedHatPsiFBg_liftZ_mem_flBallLC_core hC hk hHm cc hcψ hMX hmar hα hsm hF₁o hσ hD
      (ψh := resZ Gp Gb ψh) (fun q => by
        rw [resZ_apply]
        split_ifs
        · exact hψh _
        · rw [norm_zero]; exact hcψ) Zm hW
    have hstr := strictDataM_flEdat_cover hS Sb hC.HBp hC.hκ hC.hM hC.eps_pos hC.small1 hC.c7le
      hC.phi_lt hC.δ₁_pos le_rfl hC.hPmp hF₁ hSol hσ hD hψ.1
    obtain ⟨h1, h2, h3, -, -, h6⟩ := hSol (σ, _) hσ hstr
    exact ⟨h1, h2, h3, h6⟩

/-- **The analyticity of the marked functional in the cut parameters** (one torus): at a datum of
the chart of `Gb`, a bounded hat variable of the step and marks of the radius set, the marked
functional of the canonical transport is analytic on the polydisc of radius `e^κ`, for `Φ` analytic
on the realizable triples of a frozen region `X₁g ⊆ X₁f` in the top layer of `Gb`. -/
theorem evDecBg_fanAnalytic (hk1 : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) {a₁ ν : ℝ} (ha₁ : 1 / 2 ≤ a₁)
    (ha₂ : a₁ ≤ 2) {c BG Kc Cx : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hPmp : Precedes Hm Gb) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f X₁g : Finset (CTorus d L N₁ m₁ (k + 1))} (hX₁g : ∀ x ∈ X₁g, x ∈ X₁f)
    (hX₁gtop : ∀ x ∈ X₁g, x ∈ Gb.Ω (k + 1))
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁))
    (Zm : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {D : BgData Gb N} (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    AnalyticOnNhd ℂ (FFmarkedBg Gp X₁f Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zm um tm
      (rawOf D, (BgTransport.canon Gp Gb N).res ψh))
      (polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ)) := by
  classical
  set σ : (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) →
      Dec2.DecParams (coverOf Gb) := fun w =>
    (BgTransport.canon Gp Gb N).par (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w)
    with hσdef
  have hσan : ∀ w, AnalyticAt ℂ σ w := fun w => tauExt_analyticAt (Gl := Gb) _ w
  have hσκ : ∀ w ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ := tauExt_norm_lt (Gl := Gb) _ hκ
  have hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gb).cubeIdx),
      P ∉ (coverOf Gb).parCubes X₁g → σ w ⟨P, hP⟩ = 1 :=
    tauExt_eq_one (Gl := Gb) hG' (X₁ := (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) hX₁g hX₁gtop
  have hcore := fanLocalHatMarked_analytic_cover (Gp := Gb) hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX
    hCx heps hsmall hc7 hphi hmarD hαD hsm cc hcψ hδ₁0 hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ
    hσ1 Zm hΦ
  have hres : ∀ q, ‖resZ (N := N) Gp Gb ψh q‖ ≤ cψ := fun q => by
    rw [resZ_apply]
    split_ifs
    · exact hψh _
    · rw [norm_zero]; exact hcψ
  have hcl : clipRawL Gb (rawOf D) = rawOf D := clipRaw_of_mem_rawSub Gb (rawOf_mem_rawSub D)
  intro w hw
  have hmem : (((rawOf D, resZ (N := N) Gp Gb ψh), (um, tm)), w) ∈
      ((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gb × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
          (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ) := ⟨⟨⟨⟨D, hD, rfl⟩, hres⟩, hW⟩, hw⟩
  have hmap : AnalyticAt ℂ (fun w' : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ =>
      (((rawOf D, resZ (N := N) Gp Gb ψh), (um, tm)), w')) w :=
    analyticAt_const.prod analyticAt_id
  refine ((hcore _ hmem).comp_of_eq hmap rfl).congr (Filter.Eventually.of_forall fun w' => ?_)
  show _ = FFmarkedBg Gp X₁f Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zm um tm
    (rawOf D, (BgTransport.canon Gp Gb N).res ψh) w'
  erw [FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zm um tm (rawOf D, ψh) w']
  simp only [hcl]
  rfl

end Balaban.Polymer.LocalIso
