/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoZero
public import Balaban.Fluctuation.NewLevelOldTermsBg
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the activities and marks of the old terms

The activity `oldActBg` of a thick label `Y` and the mark `oldMarkGBg` of an anchor `(τ, Y)`
recomputed on a local pair `(Gl, Gd)` with the canonical transport are built from the terms `evDecBg`
of the old terms `τ` whose expansion has the domain `Y`.  For local pairs carried onto each other by
the box map, the old terms of the two tori whose expansions have `Y` and `bm '' Y` as domains
correspond along a map `e` of the indices (region `X₁f (e τ) = bm '' X₁f τ`, the same level,
covering setups on both tori), and the old-term functionals agree on corresponding realizable
triples; then the activities and marks agree.

* `OmegaIso.evDecBg_oldTerm_twoTorus`: the term of one old term (`evDecBg_canon_twoTorus` with the
  frozen region `X₁f` of the old term, its image on the second torus and the image mask);
* `oldActBg_of_gate`, `sum_ite_bij`: the activity under its gate as a sum over the old terms, and the
  transport of such sums along a map bijective between the indices of the summands;
* `OmegaIso.oldTermEq_twoTorus`, `OmegaIso.oldTermDiff_twoTorus`, `OmegaIso.oldMem_twoTorus`: the
  terms of corresponding old terms in the form of the activities and marks (steps `hatStepKG`), their
  differences, and the domains of the corresponding old terms;
* `OmegaIso.oldActBg_twoTorus`: the activities of corresponding thick labels;
* `OmegaIso.oldMarkGBg_twoTorus`: the marks of corresponding anchors.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Analysis Matrix

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱb ϱb' ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "SA" => Balaban.Inhabited.LevelStep.hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k
  m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => Balaban.Inhabited.LevelStep.hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2
  k m₁ ϱ hk νS β p₁ δ

namespace OmegaIso

variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The term of one old term on two tori** (local pairs).  The old term of the second torus has
the image region `X₁f' = bm '' X₁f`, the same level `j' = j` and its covering setup; the frozen
region of the analyticity is the region `X₁f` itself (in the top layer of `Gb`), and `Φ'`, `Φ` agree
on corresponding realizable triples.  The terms `evDecBg` with the mask `Zm` and its image agree at
`bm '' Y` and `Y`. -/
theorem evDecBg_oldTerm_twoTorus (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ} (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L a₁) ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gb') × Edat Hm' N → (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
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
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gb') × Edat Hm' N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hm' (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ j j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    {X' 𝒦X' : Set (CTorus d L N₁' m₁ (k + 1))} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X₁f' : Finset (CTorus d L N₁' m₁ (k + 1))}
    (hcov : CovSetup (GA) m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ j 𝒦X)
    (hcov' : CovSetup (GB) m₀ j' X' 𝒦X')
    (hX₁' : (↑X₁f' : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ j' 𝒦X')
    (hXX : X₁f' = X₁f.image bk) (hjj : j' = j)
    (hX₁top : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1))
    {R : ℕ} (hρR : ρ ≤ R) (hX₁R : ∀ x ∈ X₁f, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} {Y' : Set (CTorus d L N₁' m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) (hYY : Y' = bk '' Y)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gb Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦ : ∀ t ∈ FlRealLC Gb Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gb' Hm' a₁ ν BG κ eps (X₁f.image bk) BG₂ δ₁,
      (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' t'.1 t'.2.1 t'.2.2 = Φ t.1 t.2.1 t.2.2)
    (Zm : Finset (unitPts Gb)) {Zm' : Finset (unitPts Gb')}
    (hZm : Zm' = Zm.map hI.unitEquiv.toEmbedding) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {D : BgData Gb N} {D' : BgData Gb' N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gb' (compWeight L a₁) ν (k + 1) 1 eps D')
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {ψh : unitPts (GA) × Fin N → ℂ} {ψh' : unitPts (GB) × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (hψh' : ∀ p, ‖ψh' p‖ ≤ cψ)
    (hhat : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, ψh' (unitPt hGB (bk x), i) = ψh (unitPt hGA x, i)) :
    evDecBg (GB) X₁f' m₀ j' 𝒦X' Gb' a₁ ν (BgTransport.canon (GB) Gb' N) cc F₁' Sol' Φ' Zm' um tm Y'
        (rawOf D', (BgTransport.canon (GB) Gb' N).res ψh') =
      evDecBg (GA) X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon (GA) Gb N) cc F₁ Sol Φ Zm um tm Y
        (rawOf D, (BgTransport.canon (GA) Gb N).res ψh) := by
  subst hXX hjj hZm hYY
  exact hI.evDecBg_canon_twoTorus hH hk hGA hGB ha₁ ha₂ hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx
    hmar hα hsm cc hcψ hF₁an hF₁ hF₁' hSolan hSol hSol' hcov hX₁ hcov' hX₁' (fun x hx => hx)
    hX₁top hρR hX₁R hYR hnS hnS' hnF hnF' hΦan hΦ Zm hW hD hD' hΨ hh hψh hψh' hhat

/-- `(‖u‖ + 0) m_R < δ₁` for `‖u‖ ≤ 1`, `m_R < δ₁` and `0 < δ₁`. -/
theorem marks_lt_of_norm_le {mR δ₁ : ℝ} {u : ℂ} (hu : ‖u‖ ≤ 1) (hrad : mR < δ₁) (hδ : 0 < δ₁) :
    (‖u‖ + ‖(0 : ℂ)‖) * mR < δ₁ := by
  rw [norm_zero, add_zero]
  rcases le_or_gt 0 mR with h | h
  · nlinarith [norm_nonneg u]
  · nlinarith [norm_nonneg u]

/-- **The activity of an old label at a parameter of the chart**: the sum over the old terms whose
expansion has the label as a domain (`oldActBg` under its gate). -/
theorem oldActBg_of_gate {ϱ' : ℝ} (S : StepSetting d L N₁ m₁ k N ϱ') {ϱg ϱd : ℝ}
    (Gg : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱg)
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱd} (Tr : BgTransport S.G' Gg N)
    (Zb : Finset (unitPts Gg)) {ι : Type*} [Fintype ι]
    (X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ : ℕ) (jL : ι → ℕ)
    (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (F₁ : ι → DecParams Gg × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gg.Ω 1 × Fin N → ℂ) × (Gg.Ω 1 → ℂ))
    (Sol : ι → Dec2.DecParams (coverOf Gg) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
    (Φ : ι → ((Gg.Ω 1 × Fin N → ℂ) × (Gg.Ω 1 → ℂ)) → (Gd.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (ρ : ℝ) (hp : 0 < S.p₁) (Ru eps : ℝ) (𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (θ : physParamBg N Gg) (Y : {Y // Y ∈ 𝒴C}) (u : ℂ) (Ψ : ∀ b, (S.blockSplit 1 hp).Ωb b)
    (h : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gg (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < Ru) :
    oldActBg S Gg Tr Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρ hp Ru eps 𝒴C θ Y u Ψ =
      ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
        (S.β : ℂ) * (evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gg S.a₁ S.ν Tr
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ) (Φ τ) Zb u 0 Y.1
            ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Tr.res (S.hatOf 1 ρ hp Ψ)) -
          evDecBg S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gg S.a₁ S.ν Tr
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ τ) (Sol τ) (Φ τ) Zb 0 0 Y.1
            ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), Tr.res (S.hatOf 1 ρ hp Ψ)))
      else 0 := by
  unfold oldActBg
  rw [ite_eq_left h]

/-- **A sum over the indices with a property, along a map bijective between the indices with the
properties.** -/
theorem sum_ite_bij {ι ι' : Type*} [Fintype ι] [Fintype ι'] {P : ι → Prop} {P' : ι' → Prop}
    {dP : DecidablePred P} {dP' : DecidablePred P'} {f : ι → ℂ} {f' : ι' → ℂ}
    (e : ι → ι') (hboth : ∀ τ, P τ → P' (e τ) ∧ f' (e τ) = f τ)
    (hinj : ∀ τ₁ τ₂, P τ₁ → P τ₂ → e τ₁ = e τ₂ → τ₁ = τ₂)
    (hsurj : ∀ τ', P' τ' → ∃ τ, P τ ∧ e τ = τ') :
    (∑ τ', @ite ℂ (P' τ') (dP' τ') (f' τ') 0) = ∑ τ, @ite ℂ (P τ) (dP τ) (f τ) 0 := by
  let _ : DecidablePred P := dP
  let _ : DecidablePred P' := dP'
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun τ _ => e τ)
    (fun τ hτ => Finset.mem_filter.2 ⟨Finset.mem_univ _, (hboth τ (Finset.mem_filter.1 hτ).2).1⟩)
    (fun τ₁ h₁ τ₂ h₂ h => hinj τ₁ τ₂ (Finset.mem_filter.1 h₁).2 (Finset.mem_filter.1 h₂).2 h)
    (fun τ' hτ' => ?_) (fun τ hτ => (hboth τ (Finset.mem_filter.1 hτ).2).2.symm)
  obtain ⟨τ, h, rfl⟩ := hsurj τ' (Finset.mem_filter.1 hτ').2
  exact ⟨τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- **The term of an old term on two tori, in the form of the activities and marks** (local pairs,
steps `hatStepKG`): the term `evDecBg` of an old term `τ` at a label `Y` of its expansion and of the
corresponding old term `τ'` (image region, the same level) at `bm '' Y`, at parameters of the two
local charts whose raw data correspond on the box, the hat variables of block variables
corresponding at the unit points of the box, the masks `Zb`, `Zb'` and the marks `(um, 0)` of the
radius set. -/
theorem oldTermEq_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : ι' → Finset (CTorus d L N₁' m₁ (k + 1))}
    {m₀ : ℕ} {jL : ι → ℕ} {jL' : ι' → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))} {XL' 𝒦X' : ι' → Set (CTorus d L N₁' m₁ (k + 1))}
    (hcov : ∀ τ, CovSetup (GA) m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ (jL τ) (𝒦X τ))
    (hcov' : ∀ τ', CovSetup (GB) m₀ (jL' τ') (XL' τ') (𝒦X' τ'))
    (hX₁' : ∀ τ', (↑(X₁f' τ') : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ (jL' τ') (𝒦X' τ'))
    {F₁ : ι → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : ι' → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ τ' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' τ' (s, rawOf D) = (φ, α))
    {Sol : ι → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : ι' → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hSol' : ∀ τ' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' τ' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Small Hm' (Sol' τ' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' τ' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' τ' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' τ' p).2))
    {Φ : ι → ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ι' → ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Zb : Finset (unitPts Gb)) {Zb' : Finset (unitPts Gb')}
    (hZb : Zb' = Zb.map hI.unitEquiv.toEmbedding)
    {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Ψ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Ψ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΨ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Ψ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Ψ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (τ : ι) (τ' : ι') {Y : Set (CTorus d L N₁ m₁ (k + 1))} {Y' : Set (CTorus d L N₁' m₁ (k + 1))}
    (hYY : Y' = bk '' Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hX₁R : ∀ x ∈ X₁f τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hX' : X₁f' τ' = (X₁f τ).image bk) (hj' : jL' τ' = jL τ)
    (hX₁top : ∀ x ∈ X₁f τ, x ∈ Gb.Ω (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ τ t.1 t.2.1 t.2.2)
        (FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f τ) BG₂ δ₁))
    (hΦ : ∀ t ∈ FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f τ) BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gb' Hm' (SA).a₁ (SA).ν BG κ eps ((X₁f τ).image bk) BG₂ δ₁,
      (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' τ' t'.1 t'.2.1 t'.2.2 = Φ τ t.1 t.2.1 t.2.2)
    {um : ℂ} (hum : (‖um‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    evDecBg (SB).G' (X₁f' τ') m₀ (jL' τ') (𝒦X' τ') Gb' (SB).a₁ (SB).ν
        (BgTransport.canon (SB).G' Gb' N) (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁' τ') (Sol' τ') (Φ' τ') Zb' um 0 Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SB).G' Gb' N).res ((SB).hatOf 1 ρh hp' Ψ')) =
      evDecBg (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb (SA).a₁ (SA).ν
        (BgTransport.canon (SA).G' Gb N) (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁ τ) (Sol τ) (Φ τ) Zb um 0 Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SA).G' Gb N).res ((SA).hatOf 1 ρh hp Ψ)) := by
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  have hΨc : FieldCorr (ρ + 1) D.Ψ D'.Ψ := by
    intro z hz
    have := hraw₁ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhc : FieldCorr (ρ + 1) D.h D'.h := by
    intro z hz
    have := hraw₂ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhat := hatOf_boxMap hGA hGB hN2 hk νS β p₁ δ 1 ρh hp hp' Ψ Ψ' hΨ
  have hb : ∀ p, ‖(SA).hatOf 1 ρh hp Ψ p‖ ≤ cψ := fun p => ((SA).hatOf_mem 1 hρh hp Ψ p).trans hρc
  have hb' : ∀ p, ‖(SB).hatOf 1 ρh hp' Ψ' p‖ ≤ cψ :=
    fun p => ((SB).hatOf_mem 1 hρh hp' Ψ' p).trans hρc
  rw [hDe, hDe']
  exact hI.evDecBg_oldTerm_twoTorus hH hk hGA hGB (by show (1 / 2 : ℝ) ≤ 1; norm_num)
    (by show (1 : ℝ) ≤ 2; norm_num) hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx hmar hα hsm _ hcψ
    (hF₁an τ) (hF₁ τ) (hF₁' τ') (hSolan τ) (hSol τ) (hSol' τ') (hcov τ) (hX₁ τ) (hcov' τ')
    (hX₁' τ') hX' hj' hX₁top hρR hX₁R hYR hYY hnS hnS' hnF hnF' hΦan hΦ Zb hZb hum hD hD' hΨc hhc
    hb hb' hhat

/-- **The domain of a corresponding old term on the second torus**: if `Y` (in the box) is a domain
of the expansion of `τ`, then `bm '' Y` is a domain of the expansion of the old term `τ'` of the second
torus with the image region and the same level. -/
theorem oldMem_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ) {ι ι' : Type*}
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : ι' → Finset (CTorus d L N₁' m₁ (k + 1))}
    {m₀ : ℕ} {jL : ι → ℕ} {jL' : ι' → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))} {XL' 𝒦X' : ι' → Set (CTorus d L N₁' m₁ (k + 1))}
    (τ : ι) (τ' : ι')
    (hcov : CovSetup (GA) m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ (jL τ) (𝒦X τ))
    (hcov' : CovSetup (GB) m₀ (jL' τ') (XL' τ') (𝒦X' τ'))
    (hX₁' : (↑(X₁f' τ') : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ (jL' τ') (𝒦X' τ'))
    (hX' : X₁f' τ' = (X₁f τ).image bk) (hj' : jL' τ' = jL τ) {R : ℕ}
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} {Y' : Set (CTorus d L N₁' m₁ (k + 1))}
    (hYY : Y' = bk '' Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hY : Y ∈ polyDom (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) :
    Y' ∈ polyDom (SB).G' (X₁f' τ') m₀ (jL' τ') (𝒦X' τ') ∧
      ∀ x ∈ X₁f τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
  subst hYY
  have hYA : Y ∈ polyDom (GA) (X₁f τ) m₀ (jL τ) (𝒦X τ) := hY
  have hX₁R : ∀ x ∈ X₁f τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hYR x (subset_polyDom hYA (by rw [← hX₁]; exact hx))
  rw [hX', hj'] at hX₁'
  rw [hj'] at hcov'
  rw [hX', hj']
  exact ⟨(mem_polyDom_boxMap_iff hcov hX₁ hcov' hX₁' hX₁R hnF hnF' Y hYR).2 hYA, hX₁R⟩

/-- **The summand of an old label on two tori** (local pairs, steps `hatStepKG`): the differences
`β (evDecBg(u, 0) − evDecBg(0, 0))` of corresponding old terms (`oldTermEq_twoTorus` at the marks
`u` and `0`), for `‖u‖ ≤ 1`. -/
theorem oldTermDiff_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : ι' → Finset (CTorus d L N₁' m₁ (k + 1))}
    {m₀ : ℕ} {jL : ι → ℕ} {jL' : ι' → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))} {XL' 𝒦X' : ι' → Set (CTorus d L N₁' m₁ (k + 1))}
    (hcov : ∀ τ, CovSetup (GA) m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ (jL τ) (𝒦X τ))
    (hcov' : ∀ τ', CovSetup (GB) m₀ (jL' τ') (XL' τ') (𝒦X' τ'))
    (hX₁' : ∀ τ', (↑(X₁f' τ') : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ (jL' τ') (𝒦X' τ'))
    {F₁ : ι → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : ι' → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ τ' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' τ' (s, rawOf D) = (φ, α))
    {Sol : ι → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : ι' → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hSol' : ∀ τ' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' τ' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Small Hm' (Sol' τ' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' τ' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' τ' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' τ' p).2))
    {Φ : ι → ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ι' → ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Zb : Finset (unitPts Gb)) {Zb' : Finset (unitPts Gb')}
    (hZb : Zb' = Zb.map hI.unitEquiv.toEmbedding)
    {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Ψ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Ψ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΨ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Ψ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Ψ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (hrad : markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (τ : ι) (τ' : ι') {Y : Set (CTorus d L N₁ m₁ (k + 1))} {Y' : Set (CTorus d L N₁' m₁ (k + 1))}
    (hYY : Y' = bk '' Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hX₁R : ∀ x ∈ X₁f τ, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hX' : X₁f' τ' = (X₁f τ).image bk) (hj' : jL' τ' = jL τ)
    (hX₁top : ∀ x ∈ X₁f τ, x ∈ Gb.Ω (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ τ t.1 t.2.1 t.2.2)
        (FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f τ) BG₂ δ₁))
    (hΦ : ∀ t ∈ FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f τ) BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gb' Hm' (SA).a₁ (SA).ν BG κ eps ((X₁f τ).image bk) BG₂ δ₁,
      (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' τ' t'.1 t'.2.1 t'.2.2 = Φ τ t.1 t.2.1 t.2.2)
    {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ((SB).β : ℂ) * (evDecBg (SB).G' (X₁f' τ') m₀ (jL' τ') (𝒦X' τ') Gb' (SB).a₁ (SB).ν
        (BgTransport.canon (SB).G' Gb' N) (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁' τ') (Sol' τ') (Φ' τ') Zb' u 0 Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SB).G' Gb' N).res ((SB).hatOf 1 ρh hp' Ψ')) -
      evDecBg (SB).G' (X₁f' τ') m₀ (jL' τ') (𝒦X' τ') Gb' (SB).a₁ (SB).ν
        (BgTransport.canon (SB).G' Gb' N) (((SB).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁' τ') (Sol' τ') (Φ' τ') Zb' 0 0 Y'
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SB).G' Gb' N).res ((SB).hatOf 1 ρh hp' Ψ'))) =
      ((SA).β : ℂ) * (evDecBg (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb (SA).a₁ (SA).ν
        (BgTransport.canon (SA).G' Gb N) (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁ τ) (Sol τ) (Φ τ) Zb u 0 Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SA).G' Gb N).res ((SA).hatOf 1 ρh hp Ψ)) -
      evDecBg (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ) Gb (SA).a₁ (SA).ν
        (BgTransport.canon (SA).G' Gb N) (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (F₁ τ) (Sol τ) (Φ τ) Zb 0 0 Y
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
          (BgTransport.canon (SA).G' Gb N).res ((SA).hatOf 1 ρh hp Ψ))) := by
  have hW0 : (‖(0 : ℂ)‖ + ‖(0 : ℂ)‖) * markedRad d L N k (SA).a₁ κ cψ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rw [norm_zero, add_zero, zero_mul]; exact hC.δ₁_pos
  have T := fun (um : ℂ) hum => oldTermEq_twoTorus hN2 hk νS β p₁ δ hI hH hGA hGB hC hC' hHm hHm'
    hS Sb Sb' hMX hMX' hCx hmar hα hsm hcψ hcov hX₁ hcov' hX₁' hF₁an hF₁ hF₁' hSolan hSol hSol' Zb
    hZb hρR hnS hnS' hnF hnF' hθ hθ' hraw₁ hraw₂ hρh hρc hp hp' Ψ Ψ' hΨ τ τ' hYY hYR hX₁R hX' hj'
    hX₁top hΦan hΦ (um := um) hum
  rw [T u (marks_lt_of_norm_le hu hrad hC.δ₁_pos), T 0 hW0]
  rfl

/-- **The activities of corresponding thick labels on two tori** (local pairs, steps `hatStepKG`).
The old terms `τ` whose expansion has the domain `Y` are carried by the map `e` bijectively onto the
old terms of the second torus whose expansion has `bm '' Y` (`heinj`, `hesurj`); for each of them
(`hτ`) the corresponding term has the image region and the same level, the region lies in the top
layer of `Gb`, the old-term functional is analytic on the realizable triples of its region and agrees
with that of `e τ` on corresponding realizable triples.  At parameters of the two local charts whose raw data
correspond on the box, block variables corresponding at the unit points of the box, and `‖u‖ ≤ 1`,
the activities `oldActBg` of the labels `bm '' Y` and `Y` agree. -/
theorem oldActBg_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hrad : markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : ι' → Finset (CTorus d L N₁' m₁ (k + 1))}
    {m₀ : ℕ} {jL : ι → ℕ} {jL' : ι' → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))} {XL' 𝒦X' : ι' → Set (CTorus d L N₁' m₁ (k + 1))}
    (hcov : ∀ τ, CovSetup (GA) m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ (jL τ) (𝒦X τ))
    (hcov' : ∀ τ', CovSetup (GB) m₀ (jL' τ') (XL' τ') (𝒦X' τ'))
    (hX₁' : ∀ τ', (↑(X₁f' τ') : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ (jL' τ') (𝒦X' τ'))
    {F₁ : ι → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : ι' → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ τ' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' τ' (s, rawOf D) = (φ, α))
    {Sol : ι → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : ι' → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hSol' : ∀ τ' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' τ' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Small Hm' (Sol' τ' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' τ' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' τ' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' τ' p).2))
    {Φ : ι → ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ι' → ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Zb : Finset (unitPts Gb)) {Zb' : Finset (unitPts Gb')}
    (hZb : Zb' = Zb.map hI.unitEquiv.toEmbedding)
    {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Ψ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Ψ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΨ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Ψ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Ψ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (Ru : ℝ) {u : ℂ} (hu : ‖u‖ ≤ 1)
    {𝒴C : Finset (Set (CTorus d L N₁ m₁ (k + 1)))} {𝒴C' : Finset (Set (CTorus d L N₁' m₁ (k + 1)))}
    (Y : {Y // Y ∈ 𝒴C}) (Y' : {Y' // Y' ∈ 𝒴C'}) (hYY : Y'.1 = bk '' Y.1)
    (hYR : ∀ y ∈ Y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (e : ι → ι')
    (heinj : ∀ τ₁ τ₂, Y.1 ∈ polyDom (SA).G' (X₁f τ₁) m₀ (jL τ₁) (𝒦X τ₁) →
      Y.1 ∈ polyDom (SA).G' (X₁f τ₂) m₀ (jL τ₂) (𝒦X τ₂) → e τ₁ = e τ₂ → τ₁ = τ₂)
    (hesurj : ∀ τ', Y'.1 ∈ polyDom (SB).G' (X₁f' τ') m₀ (jL' τ') (𝒦X' τ') →
      ∃ τ, Y.1 ∈ polyDom (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ) ∧ e τ = τ')
    (hτ : ∀ τ, Y.1 ∈ polyDom (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ) →
      X₁f' (e τ) = (X₁f τ).image bk ∧ jL' (e τ) = jL τ ∧ (∀ x ∈ X₁f τ, x ∈ Gb.Ω (k + 1)) ∧
      AnalyticOnNhd ℂ (fun t => Φ τ t.1 t.2.1 t.2.2)
        (FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f τ) BG₂ δ₁) ∧
      ∀ t ∈ FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f τ) BG₂ δ₁,
        ∀ t' ∈ FlRealLC Gb' Hm' (SA).a₁ (SA).ν BG κ eps ((X₁f τ).image bk) BG₂ δ₁,
        (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
        (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
        FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
        FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' (e τ) t'.1 t'.2.1 t'.2.2 = Φ τ t.1 t.2.1 t.2.2) :
    oldActBg (SB) Gb' (BgTransport.canon (SB).G' Gb' N) Zb' X₁f' m₀ jL' 𝒦X' F₁' Sol' Φ' ρh hp' Ru
        eps 𝒴C' θ' Y' u Ψ' =
      oldActBg (SA) Gb (BgTransport.canon (SA).G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρh hp Ru eps 𝒴C
        θ Y u Ψ := by
  by_cases hRu : ‖u‖ < Ru
  · have hc1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps ∧ ‖u‖ < Ru := ⟨hθ, hRu⟩
    have hc2 : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb' (compWeight L (SB).a₁) (SB).ν (k + 1) 1 eps ∧ ‖u‖ < Ru := ⟨hθ', hRu⟩
    rw [oldActBg_of_gate (SB) Gb' (BgTransport.canon (SB).G' Gb' N) Zb' X₁f' m₀ jL' 𝒦X' F₁'
      Sol' Φ' ρh hp' Ru eps 𝒴C' θ' Y' u Ψ' hc2, oldActBg_of_gate (SA) Gb
      (BgTransport.canon (SA).G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρh hp Ru eps 𝒴C θ Y u Ψ hc1]
    refine sum_ite_bij e (fun τ h => ?_) heinj hesurj
    obtain ⟨hX', hj', htop, han, hΦτ⟩ := hτ τ h
    obtain ⟨hm, hR⟩ := oldMem_twoTorus hN2 hk νS β p₁ δ τ (e τ) (hcov τ) (hX₁ τ) (hcov' (e τ))
      (hX₁' (e τ)) hX' hj' hnF hnF' hYY hYR h
    exact ⟨hm, oldTermDiff_twoTorus hN2 hk νS β p₁ δ hI hH hGA hGB hC hC' hHm hHm' hS Sb Sb' hMX
      hMX' hCx hmar hα hsm hcψ hcov hX₁ hcov' hX₁' hF₁an hF₁ hF₁' hSolan hSol hSol' Zb hZb hρR hnS
      hnS' hnF hnF' hθ hθ' hraw₁ hraw₂ hρh hρc hp hp' Ψ Ψ' hΨ hrad τ (e τ) hYY hYR hR hX' hj' htop
      han hΦτ hu⟩
  · unfold oldActBg
    rw [ite_eq_right (fun h => hRu h.2), ite_eq_right (fun h => hRu h.2)]

/-- **The marks of corresponding anchors on two tori** (local pairs, steps `hatStepKG`).  For an
anchor `q = (τ, Y)` of the root `z` and an anchor `q' = (τ', bm '' Y)` of the root `z'` whose old
terms correspond (`hX'`: image region, `hj'`: the same level), with the region of `τ` in the top layer
of `Gb`, the old-term functional analytic on its realizable triples (`hΦan`) and agreeing with that of
`τ'` on corresponding realizable triples (`hΦ`): at parameters of the two local charts whose raw data
correspond on the box, block variables corresponding at the unit points of the box, and `‖u‖ ≤ 1`,
the marks `oldMarkGBg` of `q'` and `q` agree. -/
theorem oldMarkGBg_twoTorus (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    {c BG κ eps Kc' Cx' c₂ BG₂ δ₁ Kc Cx : ℝ}
    (hC : FlCore N Gb Hm (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hC' : FlCore N Gb' Hm' (SA).a₁ (SA).ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hHm : Hm.Ω (k + 1) = ∅) (hHm' : Hm'.Ω (k + 1) = ∅)
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (Sb' : Dec2.CoverBase (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν Kc Cx)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX' : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))} {X₁f' : ι' → Finset (CTorus d L N₁' m₁ (k + 1))}
    {m₀ : ℕ} {jL : ι → ℕ} {jL' : ι' → ℕ}
    {XL 𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1))} {XL' 𝒦X' : ι' → Set (CTorus d L N₁' m₁ (k + 1))}
    (hcov : ∀ τ, CovSetup (GA) m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 (GA) m₀ (jL τ) (𝒦X τ))
    (hcov' : ∀ τ', CovSetup (GB) m₀ (jL' τ') (XL' τ') (𝒦X' τ'))
    (hX₁' : ∀ τ', (↑(X₁f' τ') : Set (CTorus d L N₁' m₁ (k + 1))) = X1 (GB) m₀ (jL' τ') (𝒦X' τ'))
    {F₁ : ι → DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    {F₁' : ι' → DecParams Gb' × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      (Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)}
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ τ' (s : Dec2.DecParams (coverOf Gb')) (D : BgData Gb' N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb' (bgC0 d L N) (c7 d L N BG κ) (SA).ν D → ∀ (φ : Gb'.Ω 1 × Fin N → ℂ)
        (α : Gb'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb') Gb' (compWeight L (SA).a₁) (SA).ν (rho4 d L N BG κ) s D φ α →
        F₁' τ' (s, rawOf D) = (φ, α))
    {Sol : ι → Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : ι' → Dec2.DecParams (coverOf Gb') × Edat Hm' N →
      (Hm'.Ω 1 × Fin N → ℂ) × (Hm'.Ω 1 → ℂ)}
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ τ (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (hSol' : ∀ τ' (p : Dec2.DecParams (coverOf Gb') × Edat Hm' N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm' N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' τ' p).1 = dphi Hm' (Dec2.decG (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1)
          p.2.2.1 p.2.1 (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) (Sol' τ' p).2 ∧
        Small Hm' (Sol' τ' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm' (Sol' τ' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm' (Sol' τ' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm'.Ω 1 → ℂ, Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb') Hm' (compWeight L (SA).a₁) (SA).ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm' (compWeight L (SA).a₁) p.2.2.2.1 p.2.2.2.2) δα' →
            δα' = (Sol' τ' p).2))
    {Φ : ι → ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Φ' : ι' → ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) → (Hm'.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (Zb : Finset (unitPts Gb)) {Zb' : Finset (unitPts Gb')}
    (hZb : Zb' = Zb.map hI.unitEquiv.toEmbedding)
    {R : ℕ} (hρR : ρ ≤ R)
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {θ : physParamBg N Gb} {θ' : physParamBg N Gb'}
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps)
    (hraw₁ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).1)
    (hraw₂ : FieldCorr (ρ + 1) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2
      (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N).2)
    {ρh : ℝ} (hρh : 0 < ρh) (hρc : ρh ≤ cψ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (Ψ : ∀ b, ((SA).blockSplit 1 hp).Ωb b) (Ψ' : ∀ b, ((SB).blockSplit 1 hp').Ωb b)
    (hΨ : ∀ x, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      Ψ' ((SB).cellOf 1 (unitPt hGB (bk x))) ⟨unitPt hGB (bk x), rfl⟩ =
        Ψ ((SA).cellOf 1 (unitPt hGA x)) ⟨unitPt hGA x, rfl⟩)
    (Ru : ℝ) {u : ℂ}
    {z : RootIdx d L N₁ m₁ (k + 1)} {z' : RootIdx d L N₁' m₁ (k + 1)}
    (q : {q // q ∈ markedIdx (fun _ : ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom (SA).G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z})
    (q' : {q // q ∈ markedIdx (fun _ : ι' => (Set.univ : Set (CTorus d L N₁' m₁ (k + 1))))
      (fun τ => polyDom (SB).G' (X₁f' τ) m₀ (jL' τ) (𝒦X' τ)) z'})
    (hqY : q'.1.2 = bk '' q.1.2)
    (hYR : ∀ y ∈ q.1.2, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hX' : X₁f' q'.1.1 = (X₁f q.1.1).image bk) (hj' : jL' q'.1.1 = jL q.1.1)
    (hX₁top : ∀ x ∈ X₁f q.1.1, x ∈ Gb.Ω (k + 1))
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ q.1.1 t.1 t.2.1 t.2.2)
        (FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f q.1.1) BG₂ δ₁))
    (hΦ : ∀ t ∈ FlRealLC Gb Hm (SA).a₁ (SA).ν BG κ eps (X₁f q.1.1) BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gb' Hm' (SA).a₁ (SA).ν BG κ eps ((X₁f q.1.1).image bk) BG₂ δ₁,
      (∀ x i, t'.1.1 (hI.e x, i) = t.1.1 (x, i)) → (∀ x, t'.1.2 (hI.e x) = t.1.2 x) →
      (∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i)) →
      FieldCorr (ρ + 1) t.2.2.1.1 t'.2.2.1.1 → FieldCorr (ρ + 1) t.2.2.1.2 t'.2.2.1.2 →
      FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2 → Φ' q'.1.1 t'.1 t'.2.1 t'.2.2 = Φ q.1.1 t.1 t.2.1 t.2.2)
    (hum : ‖u‖ * markedRad d L N k (SA).a₁ κ cψ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁) :
    oldMarkGBg (SB) Gb' (BgTransport.canon (SB).G' Gb' N) Zb' X₁f' m₀ jL' 𝒦X' F₁' Sol' Φ' ρh hp'
        Ru eps z' θ' q' u Ψ' =
      oldMarkGBg (SA) Gb (BgTransport.canon (SA).G' Gb N) Zb X₁f m₀ jL 𝒦X F₁ Sol Φ ρh hp Ru eps
        z θ q u Ψ := by
  by_cases hRu : ‖u‖ < Ru
  swap
  · unfold oldMarkGBg
    rw [ite_eq_right (fun h => hRu h.2), ite_eq_right (fun h => hRu h.2)]
  have hc1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L (SA).a₁) (SA).ν (k + 1) 1 eps ∧ ‖u‖ < Ru := ⟨hθ, hRu⟩
  have hc2 : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb' (compWeight L (SB).a₁) (SB).ν (k + 1) 1 eps ∧ ‖u‖ < Ru := ⟨hθ', hRu⟩
  obtain ⟨D, hD, hDe⟩ := hθ
  obtain ⟨D', hD', hDe'⟩ := hθ'
  have hΨc : FieldCorr (ρ + 1) D.Ψ D'.Ψ := by
    intro z hz
    have := hraw₁ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhc : FieldCorr (ρ + 1) D.h D'.h := by
    intro z hz
    have := hraw₂ z hz
    rw [hDe, hDe'] at this
    exact this
  have hhat := hatOf_boxMap hGA hGB hN2 hk νS β p₁ δ 1 ρh hp hp' Ψ Ψ' hΨ
  have hb : ∀ p, ‖(SA).hatOf 1 ρh hp Ψ p‖ ≤ cψ := fun p => ((SA).hatOf_mem 1 hρh hp Ψ p).trans hρc
  have hb' : ∀ p, ‖(SB).hatOf 1 ρh hp' Ψ' p‖ ≤ cψ :=
    fun p => ((SB).hatOf_mem 1 hρh hp' Ψ' p).trans hρc
  have hq : q.1.2 ∈ polyDom (GA) (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) :=
    (mem_markedIdx.1 q.2).1
  have hX₁R : ∀ x ∈ X₁f q.1.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hYR x (subset_polyDom hq (by rw [← hX₁ q.1.1]; exact hx))
  unfold oldMarkGBg
  rw [ite_eq_left hc1, ite_eq_left hc2]
  show ((SB).β : ℂ) * _ = ((SA).β : ℂ) * _
  refine congrArg₂ (· * ·) rfl ?_
  refine Filter.EventuallyEq.deriv_eq ?_
  have hopen : IsOpen {t : ℂ | (‖u‖ + ‖t‖) * markedRad d L N k (SA).a₁ κ cψ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁} :=
    isOpen_lt (by fun_prop) continuous_const
  have h0 : (0 : ℂ) ∈ {t : ℂ | (‖u‖ + ‖t‖) * markedRad d L N k (SA).a₁ κ cψ
      (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁} := by
    show (‖u‖ + ‖(0 : ℂ)‖) * _ < δ₁
    rw [norm_zero, add_zero]
    exact hum
  filter_upwards [hopen.mem_nhds h0] with t ht
  rw [hDe, hDe']
  exact hI.evDecBg_oldTerm_twoTorus hH hk hGA hGB (by show (1 / 2 : ℝ) ≤ 1; norm_num)
    (by show (1 : ℝ) ≤ 2; norm_num) hC hC' hHm hHm' hS Sb Sb' hMX hMX' hCx hmar hα hsm _ hcψ
    (hF₁an q.1.1) (hF₁ q.1.1) (hF₁' q'.1.1) (hSolan q.1.1) (hSol q.1.1) (hSol' q'.1.1)
    (hcov q.1.1) (hX₁ q.1.1) (hcov' q'.1.1) (hX₁' q'.1.1) hX' hj' hX₁top hρR hX₁R hYR hqY
    hnS hnS' hnF hnF' hΦan hΦ Zb hZb ht hD hD' hΨc hhc hb hb' hhat

end OmegaIso

end Balaban.Polymer.LocalIso
