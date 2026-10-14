/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedDecAnalytic

/-!
# Analyticity of the fan with the masked tangent (`MARK-AN`, fan level)

`fanH_analytic_marked` is `fanH_analytic` with the decoupled tangent `hatPsiF` replaced by the
masked tangent `markedHatPsiF … Z u t` (a fixed block set `Z` of unit points and complex marks
`u, t`) in the three places where the fan functional uses it: the fixed-point data
`flEdat … (markedHatPsiF … s Θ ψ̂)` and the last argument `(Θ, markedHatPsiF … s Θ ψ̂)`.  The
function is analytic jointly in the data `Θ`, the hat variable `ψ̂`, the cut parameters `s` and the
two marks `(u, t)`, at every point of `((Ξ^c × Bhat) × polydisc) × W`, for every set `W` of marks
on which the masked tangent stays in the ball of fluctuations (the hypothesis `hSup`, the landed
`hSup` with the marks added; it is `markedHatPsiF_mem_flBallLC` on the radius set).

The proof is the landed one: the pointwise facts `point_facts_core` give the background, the
selected fluctuation solution and membership in `FlReal`; the analyticity of the tangent is
`analyticOnNhd_markedHatPsiF`.  `fanH_analytic_marked_fixed` is the slice at fixed marks.

`MARK-COUNT` (decoupled), `MARK-PARAM` and the marked family are NOT proved here; nothing depends
on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Fan

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- Core of `fanH_analytic_marked`: analyticity of `Φ` is asked on a set `R` containing the points of
`FlReal` at which the fan evaluates `Φ` (`hR`). -/
theorem fanH_analytic_marked_of (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {R : Set (((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))}
    (Bhat : Set (unitPts Gp × Fin N → ℂ)) (Z : Finset (unitPts Gp)) (W : Set (ℂ × ℂ))
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
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2) R)
    (hR : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ∀ (a b : ℂ)
      (s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) (D : BgData Gp N)
      (ψh : unitPts Gp × Fin N → ℂ),
      t.2.2.2 = markedHatPsiF a₁ ν hG' cc F₁ Z a b
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh → t ∈ R)
    (hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D → ∀ ψh ∈ Bhat, ∀ w ∈ W,
      markedHatPsiF a₁ ν hG' cc F₁ Z w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁) :
    AnalyticOnNhd ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) × (ℂ × ℂ) =>
      Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2, p.1.1.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2, p.1.1.1))
            p.1.1.1.1 (markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2))).1
        (p.1.1.1, markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2))
      (((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Bhat) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) ×ˢ W) := by
  classical
  rintro ⟨⟨⟨u, ψh⟩, s⟩, ⟨a, b⟩⟩ ⟨⟨⟨⟨D, hD, rfl⟩, hψh⟩, hs⟩, hab⟩
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hψ0 := hSup s hs D hD ψh hψh (a, b) hab
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ0
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
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) ×
      (ℂ × ℂ) => p.1.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq
      (analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)) rfl
  have hFpt : F₁ (g0 pt) = (φ, α) := hFeq
  have hψan : AnalyticAt ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) ×
      (ℂ × ℂ) => markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2) pt :=
    analyticOnNhd_markedHatPsiF hC hk hG' cc Bhat Z hMX hmar hα hsm hF₁an hF₁ pt
      ⟨⟨⟨⟨D, hD, rfl⟩, hψh⟩, hs⟩, Set.mem_univ _⟩
  set ed : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) × (ℂ × ℂ) → Edat Hm N :=
    fun p => flEdat Gp Hm (F₁ (g0 p)) p.1.1.1.1 (markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2) with hed
  have haed : AnalyticAt ℂ ed pt := by
    refine AnalyticAt.prod (analyticAt_barField (fun p => (F₁ (g0 p)).1) (fun p => p.1.1.1.1)
      (fun r => analyticAt_pi_iff.1 hφ1 r) hΨ1) (AnalyticAt.prod
      (analyticAt_flAlpha (fun p => (F₁ (g0 p)).2) (fun y => analyticAt_pi_iff.1
        (analyticAt_snd.comp ha1) y))
      (AnalyticAt.prod hψan analyticAt_const))
  have hedpt : ed pt = flEdat Gp Hm (φ, α) D.Ψ
      (markedHatPsiF a₁ ν hG' cc F₁ Z a b
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh) := by
    show flEdat Gp Hm (F₁ (g0 pt)) D.Ψ _ = _
    rw [hFpt]
  have hSolpt : AnalyticAt ℂ (fun p => Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2,
      ed p)) pt := by
    refine (hSolan (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, ed pt)
      ⟨hsx, ?_⟩).comp_of_eq (hext.prod haed) rfl
    rw [hedpt]; exact hstrict
  have hg : AnalyticAt ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) ×
      (ℂ × ℂ) =>
      (F₁ (g0 p), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2, ed p)).1,
        (p.1.1.1, markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2))) pt :=
    ha1.prod ((analyticAt_fst.comp hSolpt).prod
      ((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod hψan))
  have hval : (F₁ (g0 pt), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) pt.1.2,
      ed pt)).1, (pt.1.1.1, markedHatPsiF a₁ ν hG' cc F₁ Z pt.2.1 pt.2.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) pt.1.2) pt.1.1.1 pt.1.1.2)) =
      ((φ, α), δφ, (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Z a b
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)) := by
    show (F₁ (g0 pt), (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      ed pt)).1, _) = _
    rw [hFpt, hedpt, hSeq]
  have hΦpt := hΦ _ (hR _ hmem a b s D ψh rfl)
  rw [← hval] at hΦpt
  exact hΦpt.comp_of_eq hg rfl


/-- **(`MARK-AN`) Joint analyticity of the fan with the masked tangent.**  The statement of
`fanH_analytic` with `markedHatPsiF … Z u t` in place of `hatPsiF`, on the product of the landed
domain with a set `W` of marks `(u, t)`; the function is analytic in `(Θ, ψ̂, s, u, t)`.  The
hypothesis `hSup` is the landed one for the marks in `W`. -/
theorem fanH_analytic_marked (hk : 1 ≤ k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (Bhat : Set (unitPts Gp × Fin N → ℂ)) (Z : Finset (unitPts Gp)) (W : Set (ℂ × ℂ))
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
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D → ∀ ψh ∈ Bhat, ∀ w ∈ W,
      markedHatPsiF a₁ ν hG' cc F₁ Z w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁) :
    AnalyticOnNhd ℂ (fun p : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)) × (ℂ × ℂ) =>
      Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2, p.1.1.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2, p.1.1.1))
            p.1.1.1.1 (markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2))).1
        (p.1.1.1, markedHatPsiF a₁ ν hG' cc F₁ Z p.2.1 p.2.2
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) p.1.2) p.1.1.1 p.1.1.2))
      (((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Bhat) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) ×ˢ W) := fanH_analytic_marked_of hC hk hG' cc Bhat Z W hMX hmar hα hsm hF₁an hF₁ hSolan hSol hΦ
    (fun _ ht _ _ _ _ _ _ => ht) hSup

end Fan

section Slice

/-- **A slice at fixed marks.**  If `f` is analytic on `A ×ˢ W` and `w₀ ∈ W`, then `p ↦ f (p, w₀)`
is analytic on `A`. -/
theorem analyticOnNhd_slice_marks {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Set E} {W : Set (ℂ × ℂ)} {f : E × (ℂ × ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (A ×ˢ W)) {w₀ : ℂ × ℂ} (hw : w₀ ∈ W) :
    AnalyticOnNhd ℂ (fun p : E => f (p, w₀)) A :=
  hf.comp (fun _ _ => (analyticAt_id.prod analyticAt_const))
    (fun _ hp => Set.mk_mem_prod hp hw)

end Slice

end Balaban.Localization
