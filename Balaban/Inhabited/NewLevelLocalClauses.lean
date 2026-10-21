/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystemLocality
public import Balaban.Inhabited.NewLevelSystemRot
public import Balaban.Fluctuation.NewLevelOldTermsBgLocal
public import Balaban.Inhabited.NewLevelOldTermsBgRot
public import Balaban.Inhabited.NewLevelSystemAnalytic
public import Balaban.Inhabited.NewLevelSystemRead

/-!
# The clauses (A1)–(A5) of the recomputed family with the old terms given by their settings

Route R-LOC, L5: the forms of the clauses (A1)–(A5) of `localFamily_of_coeff` for the coefficient
recomputed on a local generating set `Gl` from the labels inside the polymer `T`, with the
locality and the covariance of the terms of the old terms derived from their settings at the step
(`evDecBg_canon_local_eTerm`, `evDecBg_canon_rot_eTerm`) in place of the hypotheses `holdloc`,
`holdrot` of `coeffLoc_local_of`, `coeffLoc_rot_of`.

* `NewLevelSystem.clause_local_of`, `NewLevelSystem.clause_rot_of`,
  `NewLevelSystem.clause_analytic_of` (the old functionals analytic and bounded on the realizable
  triples of `Gl` from their settings, `eTermFun_analytic_bound_of_top`);
* `NewLevelSystem.clause_rot_full_of`: (A4) with the old functionals and the parts of the
  coefficient derived from the settings and the decoupling pairs;
* `NewLevelSystem.clauses_of`: the five clauses (A1)–(A5) of `localFamily_of_coeff` for one polymer,
  at the mask of the block of the root and the reference configuration `0`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset MeasureTheory Matrix
  Balaban.Inhabited.MarkBudgetAudit

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl ϱl' : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr) {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
  (F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (F₁L' : NS.O.ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (SolL' : NS.O.ι → Dec2.DecParams (coverOf Gl) × Edat Gd N →
    (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
  (F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
  (Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))

open Classical in
/-- **The clause (A3) of the recomputed family** (P3 pp. 78-79 and Lemma 4.2 at `Gl`, (AE2)): under
the hypotheses of `coeffLoc_local_of` with the locality of the terms of the old terms given by their
settings at the gate radius `ε′` (`evDecBg_canon_local_eTerm`), the coefficient recomputed from the
labels inside `T` takes the same value at two parameters with zero sources of the chart of radius
`ε_loc ≤ ε′` whose raw data agree on a set `Y⁺ ⊇ thickSet S.G' (sitesOf T)`. -/
theorem clause_local_of (hS1 : S.a₁ = 1) (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    {eps' : ℝ} {c c₂ Kc Cx : ℝ}
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps' Kc Cx c₂ NS.BG₂ t)
    (hHm : Gd.Ω (k + 1) = ∅) (hHmtop : ∀ y ∈ Gl.Ω (k + 1), y ∈ Gd.Ω 1)
    (hrow : RowInHat (coverOf Gl) Gd (compWeight L S.a₁) S.ν) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    -- the old terms
    {cL c₂L KcL CxL : ℝ}
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps' KcL CxL c₂L NS.O.BG₂ NS.O.δ₁)
    {cψL : ℝ} (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hMXL : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) (hcψL : 0 ≤ cψL)
    -- the settings of the old terms at the gate radius
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (hdk : Gd.Ω k = Gl.Ω k)
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    {r₀ δ₃ δfl ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ eps' δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs}
    {Kf Cf c₂f : ℝ}
    (hFo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG eps' δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ)) (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱl - 1)
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps'))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    -- the zero-source and bridge pairs of `(Gl, Gd)`
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps'))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps'))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the polymer and the chart of the locality
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) {Ypl : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYpl : thickSet S.G' (sitesOf T) ⊆ Ypl) {εloc : ℝ} (hεloc : εloc ≤ eps') :
    ∀ θb θb' : physParamBg N Gl,
      (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 εloc →
      (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 εloc → θb.2 = 0 → θb'.2 = 0 →
      (∀ x ∈ Ypl, (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x =
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x ∧
        (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x =
          (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x) →
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T =
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T := by
  intro θb θb' hθ hθ' _ _ hag
  have hk1 := S.hk1
  have hF₁Ln : ∀ τ (s : DecParams Gl) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ),
        IsDecBg Gl (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α) := fun τ s D hs hD φ α hI =>
    hF₁L' τ s D hs hD φ α ((dec2_isDecBg_iff Gl _ _ _ s D φ α).2 hI)
  refine NS.coeffLoc_local_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1 SpG hC hHm hHmtop hrow hcψ hMX hδc
    hdm hα hsm hρ₀c hRu hCL hρL hρcL ht₀ hRt (fun τ um tm hW Y hYm u hu u' hu' hAg => ?_) hF₂s'
    hSol₂' hF₁b' hSolb' Zb Φ₀ T hTm (xiCRaw_mono_radius hεloc hθ) (xiCRaw_mono_radius hεloc hθ')
    fun x hx => hag x (hYpl hx)
  exact evDecBg_canon_local_eTerm hCL hk1 S.hG' hHm hHmtop hdk hrow _ hcψL hMXL hdmL hαL hsmL
    (hcovL τ) (hX₁L τ) (hF₁Ln τ) (hSolL' τ) (hBo τ) (hFo τ) hGs HB' hrb (NS.O.FkL τ)
    (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) (maskPre S.hG' Gl (S.blockU z)) um tm hW Y hYm u hu u'
    hu' hAg

open Classical in
/-- **The clause (A4) of the recomputed family** (P3 pp. 78-79): under the hypotheses of
`coeffLoc_rot_of` with the covariance of the terms of the old terms given by their settings at the
analyticity radius `ε` (`evDecBg_canon_rot_eTerm`, the old terms invariant under the real rotations
on their charts), the coefficient recomputed from the labels inside `T` is invariant under the real
rotations on the chart of `Gl` of radius `ε`. -/
theorem clause_rot_of (hS1 : S.a₁ = 1) {eps eps' : ℝ} (hle : eps ≤ eps')
    {c c₂ Kc Cx Kf Cf : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kf Cf c₂ NS.BG₂ t)
    (hHm : Gd.Ω (k + 1) = ∅) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    -- the old terms
    {cψL : ℝ} (hρpL : S.p₁ ≤ NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hδ₁L : 0 < NS.O.δ₁)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    -- the settings of the old terms at the analyticity radius
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {cL c₂L : ℝ}
    (hSL : Dec2.DecSpecs d L Kc Cx cL NS.O.BG)
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps Kc Cx c₂L NS.O.BG₂ NS.O.δ₁)
    (hdk : Gd.Ω k = Gl.Ω k) (hAl : CubeAligned Gl m₁) (hSS : SupSep Gl m₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁) (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (hMXL : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) {δcL : ℝ}
    (hmarL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) (hcψL : 0 ≤ cψL)
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    {cB r₀ δ₃ δfl ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cB NS.O.BG NS.O.κ r₀ eps δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs}
    {Kf Cf c₂f : ℝ}
    (hFo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG eps δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ)) (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱl - 1)
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    -- the zero-source and bridge pairs of `(Gl, Gd)`
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the polymer and the bundled activities
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) {εH κH κ0 Kc' : ℝ}
    (A : physParamBg N Gl → ℂ → LabelAct NS.Lab (S.blockSplit 1 NS.hp).Ωb εH κH κ0 Kc')
    (hAH : ∀ θb u y Φ, (A θb u).H y Φ =
      locAct NS.Lab T Φ₀ (NS.actBg F₂' Sol₂' F₁L' SolL' eps) θb u y Φ) :
    ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps, ∀ θb' ∈ physVBg N Gl S.a₁ S.ν eps,
      (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
        rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T =
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T := by
  intro Q hQ θb hθb θb' _ hrot
  have hk1 := S.hk1
  have hF₁Ln : ∀ τ (s : DecParams Gl) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ),
        IsDecBg Gl (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α) := fun τ s D hs hD φ α hI =>
    hF₁L' τ s D hs hD φ α ((dec2_isDecBg_iff Gl _ _ _ s D φ α).2 hI)
  refine NS.coeffLoc_rot_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1 hle hS Sb hC hHm hcψ hMX hδc hdm hα
    hsm hρ₀c hρp hRu hQ hρpL hρcL ht₀ hδ₁L hRt
    (fun τ um tm hW Y hYm D hD ψh hψh => ?_) hF₂s' hSol₂' hF₁b' hSolb' Zb Φ₀ hΦ₀ T hTm A hAH
    hθb.1 hrot
  exact evDecBg_canon_rot_eTerm S hb₁ hbC hSL Sb hCL hk1 hHm hdk hAl hSS hMM _ hcψL hMXL hmarL
    hαL hsmL (hX₁L τ) (hF₁Ln τ) (hSolL' τ) (hBo τ) (hFo τ) hGs HB' hrb
    (fun D hD => NS.O.hFkL τ D hD) hQ (hEr τ Q hQ) (maskPre S.hG' Gl (S.blockU z)) hW hYm hD hψh

/-- **The functionals of the old terms on the realizable triples of `Gl`** (the hypotheses `hΦ`,
`hΦbd` of `coeffLoc_analytic_bound_of`): for an old term whose frozen region lies in the top layer
of `Gl`, with the step's settings at the radius `ε` and the old term analytic and bounded on its
chart, the functional `eTermFun Gl …` is analytic and bounded on the realizable triples of `Gl`
(`eTermFun_analytic_bound_of_top`). -/
theorem oldFun_fields_of {eps : ℝ} (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (hdk : Gd.Ω k = Gl.Ω k) (hHm : Gd.Ω (k + 1) = ∅)
    {cL c₂L KcL CxL : ℝ}
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps KcL CxL c₂L NS.O.BG₂ NS.O.δ₁)
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ eps δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs}
    {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG eps δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ)) (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱl - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    {Eb : NS.O.ι → ℝ} {κdec : ℝ} {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))) :
    ∀ τ, (∀ x ∈ NS.O.X₁f τ, x ∈ Gl.Ω (k + 1)) →
      AnalyticOnNhd ℂ (fun t' : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) × (Gd.Ω 1 × Fin N → ℂ) ×
          (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
        eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2)
        (FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁) ∧
      ∀ t' ∈ FlRealLC Gl Gd S.a₁ S.ν NS.O.BG NS.O.κ eps (NS.O.X₁f τ) NS.O.BG₂ NS.O.δ₁,
        ‖eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
          (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) t'.1 t'.2.1 t'.2.2‖ ≤
          Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)) :=
  fun τ htop => eTermFun_analytic_bound_of_top_gen hb₁ hbC (hBo τ) S.hG' (hFLo τ) hGs S.hk1
    hCL.Sp HB' hrb hCL hdk hHm (fun x hx => htop x ((hBo τ).dep x hx x (self_mem_composeDep x)))
    (hFkan τ) (NS.O.hFkL τ) (hEan τ) (hEbd τ)

open Classical in
/-- **The clauses (A1), (A2) of the recomputed family** (P3 (4.46), (4.47) and Lemma 4.2 at `Gl`):
under the hypotheses of `coeffLoc_analytic_bound_of` with the functionals of the old terms analytic
and bounded on the realizable triples of `Gl` by their settings at the analyticity radius `ε`
(`eTermFun_analytic_bound_of_top`, the old terms analytic and bounded on their charts), the
coefficient recomputed from the labels inside `T` is analytic on `physVBg Gl ε` and bounded there by
a nonnegative constant. -/
theorem clause_analytic_of (hS1 : S.a₁ = 1) {eps eps' : ℝ} (hle : eps ≤ eps')
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (hd : 3 ≤ d)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    -- the zero-source and bridge pairs, and the determinant part
    {c c₂ Kc Cx : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kc Cx c₂ NS.BG₂ t)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (hMX' : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hmarD : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hBG₂ : 0 ≤ NS.BG₂) (hdk : Gd.Ω k = Gl.Ω k) (hHm : Gd.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gl.Ω (k + 1), y ∈ Gd.Ω 1)
    (hrow : RowInHat (coverOf Gl) Gd (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    (hρc : NS.p₁ ≤ cψ)
    (hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    {R₁ r : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    (hF₂an : ∀ b, AnalyticOnNhd ℂ (F₂' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂an : ∀ b, AnalyticOnNhd ℂ (Sol₂' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁ban : ∀ b, AnalyticOnNhd ℂ (F₁b' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolban : ∀ b, AnalyticOnNhd ℂ (Solb' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the old terms
    {cL c₂L KcL CxL : ℝ} (hSL : Dec2.DecSpecs d L KcL CxL cL NS.O.BG)
    (SbL : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν KcL CxL)
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps KcL CxL c₂L NS.O.BG₂ NS.O.δ₁)
    (hMXL : Dec2.cstarX d L CxL * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) (hCxL : 0 ≤ CxL)
    {δcL : ℝ} (hmarDL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps) < δcL)
    (hαDL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hF₁Lan : ∀ τ, AnalyticOnNhd ℂ (F₁L' τ) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.O.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolLan : ∀ τ, AnalyticOnNhd ℂ (SolL' τ) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2})
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ)
    -- the settings of the old terms at the analyticity radius
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ eps δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs}
    {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG eps δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ)) (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱl - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    -- the bounds in the class form
    {εH κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    -- the numerical conditions of Theorem 3.4
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    -- the determinant part
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    -- the polymer
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) :
    ∃ bT : ℝ, 0 ≤ bT ∧
      AnalyticOnNhd ℂ (fun θb => NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T)
        (physVBg N Gl S.a₁ S.ν eps) ∧
      ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps,
        ‖NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T‖ ≤ bT := by
  have hΦ' := NS.oldFun_fields_of HB' hdk hHm hCL hb₁ hbC hBo hFLo hGs hrb hFkan hEan hEbd
  have key := NS.coeffLoc_analytic_bound_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1 hle HB' hd SpG hS Sb
    hC hMX hCx hMX' hδc hmarD hαD hsm hcψ hBG₂ hdk hHm hHmtop hrow hκ₀ hκdec hκκ h1 hlog hρc hδ₁c
    hR₁ hr hrays hR hRR hUR hU hF₂an hF₂s' hSol₂an hSol₂' hF₁ban hF₁b' hSolban hSolb' hSL SbL hCL
    hMXL hCxL hmarDL hαDL hsmL hcψL hκκL h1L hlogL hρL hρcL hRuL hca haL ht₀ hRt hF₁Lan hF₁L'
    hSolLan hSolL' hcovL hX₁L hoptL hEb (fun τ h => (hΦ' τ h).1) (fun τ h => (hΦ' τ h).2) hκH hεz
    hεo hFb hFo hεpos hι
    hF0 hκ' hκ hε hz Zb Φ₀ T hTm
  exact ⟨max 0 (
          Zb.card * ((1 / 2 : ℝ) * N * covBLog d L (compWeight L S.a₁ k) (S.a₁ / (L : ℝ) ^ 2)
            NS.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ)) *
            Real.exp (-((NS.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt T)) +
          CPE d L (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 + rootUnionK d L 1 m₁ NS.Z.κ0) +
              rootUnionK d L 1 m₁ NS.Z.κ0) κH NS.Z.κ0 κ' *
            (∑ i, F0 i * Real.exp (-NS.Z.κ0 * NS.Lab.dl (NS.y0 i))) * Real.exp (-κ' * dExt T)),
    le_max_left _ _, key.1, fun θb hθb => (key.2 θb hθb).trans (le_max_right _ _)⟩

open Classical in
/-- **The clause (A4) of the recomputed family from the fields of its parts**: under the
hypotheses of `clause_analytic_of` (with the old pairs on the same cover base) and the covariance of
the old terms on their charts, the coefficient recomputed from the labels inside `T` (reference
configuration `0`) is invariant under the real rotations on `physVBg Gl ε`; the bundled family of
`clause_rot_of` is `exists_bundled_actBg_of_parts` of the fields of `zeroAct_fields_of`,
`oldAct_fields_of`, `marks_fields_of`. -/
theorem clause_rot_full_of (hS1 : S.a₁ = 1) {eps eps' : ℝ} (hle : eps ≤ eps')
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν) (hd : 3 ≤ d)
    (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    -- the zero-source and bridge pairs, and the determinant part
    {c c₂ Kc Cx : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c NS.BG)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν Kc Cx)
    (hC : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps Kc Cx c₂ NS.BG₂ t)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (hMX' : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hmarD : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N NS.BG NS.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hBG₂ : 0 ≤ NS.BG₂) (hdk : Gd.Ω k = Gl.Ω k) (hHm : Gd.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gl.Ω (k + 1), y ∈ Gd.Ω 1)
    (hrow : RowInHat (coverOf Gl) Gd (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    (hρc : NS.p₁ ≤ cψ)
    (hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    {R₁ r : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    (hF₂an : ∀ b, AnalyticOnNhd ℂ (F₂' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂an : ∀ b, AnalyticOnNhd ℂ (Sol₂' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁ban : ∀ b, AnalyticOnNhd ℂ (F₁b' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolban : ∀ b, AnalyticOnNhd ℂ (Solb' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2})
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    -- the old terms
    {cL c₂L : ℝ} (hSL : Dec2.DecSpecs d L Kc Cx cL NS.O.BG)
    (hCL : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps Kc Cx c₂L NS.O.BG₂ NS.O.δ₁)
    (hMXL : Dec2.cstarX d L Cx * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    {δcL : ℝ} (hmarDL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps) < δcL)
    (hαDL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    (hF₁Lan : ∀ τ, AnalyticOnNhd ℂ (F₁L' τ) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.O.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolLan : ∀ τ, AnalyticOnNhd ℂ (SolL' τ) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2})
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ)
    -- the settings of the old terms at the analyticity radius
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ eps δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs}
    {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG eps δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ)) (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱl - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    -- the bounds in the class form
    {εH κH : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i)
    -- the covariance
    (hρ₀c : 2 * NS.p₁ ≤ cψ) (hρp : S.p₁ ≤ NS.p₁) (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hAl : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    -- the polymer
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) :
    ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ θb ∈ physVBg N Gl S.a₁ S.ν eps, ∀ θb' ∈ physVBg N Gl S.a₁ S.ν eps,
      (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
        rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T =
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T := by
  have hΦ' := NS.oldFun_fields_of HB' hdk hHm hCL hb₁ hbC hBo hFLo hGs hrb hFkan hEan hEbd
  obtain ⟨h0m, h0b, h0h, h0c⟩ := NS.zeroAct_fields_of F₂' Sol₂' hS1 HB' hS Sb hC hMX hCx hmarD hαD
    hsm hcψ hBG₂ hdk hHm hκ₀ hκdec hκκ h1 hlog hδ₁c hR₁ hr hrays hF₂an hF₂s' hSol₂an hSol₂' hεz hκH
    T hTm
  obtain ⟨h1m, h1b, h1h, h1c⟩ := NS.oldAct_fields_of F₁L' SolL' hS1 HB' hHm hκ₀ hκdec hSL Sb hCL
    hMXL hCx hmarDL hαDL hsmL hcψL hκκL h1L hlogL hρL hρcL hRuL hca haL hF₁Lan hF₁L' hSolLan hSolL'
    hcovL
    hX₁L hoptL hEb (fun τ h => (hΦ' τ h).1) (fun τ h => (hΦ' τ h).2) hεo T hTm
  obtain ⟨hGm, hGb, hGh, hGc⟩ := NS.marks_fields_of F₁L' SolL' F₁b' Solb' hS1 HB' hd SpG hS Sb hC
    hMX hCx hMX' hmarD hαD hsm hcψ hBG₂ hdk hHm hHmtop hrow hκ₀ hκdec hκκ h1 hlog hρc hR hRR hUR hU
    hF₁ban hF₁b' hSolban hSolb' hSL Sb hCL hMXL hCx hmarDL hαDL hsmL hcψL hκκL h1L hlogL hρL hρcL
    ht₀ hRt hF₁Lan hF₁L' hSolLan hSolL' hcovL hX₁L hoptL hEb (fun τ h => (hΦ' τ h).1)
    (fun τ h => (hΦ' τ h).2) hFb hFo T hTm
  have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) corrU := by
    intro s hs
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    norm_num [corrU]
    linarith [hs.2]
  obtain ⟨A, hAH⟩ := NS.exists_bundled_actBg_of_parts F₂' Sol₂' F₁L' SolL' F₁b' Solb' HB' Φ₀ T
    Metric.isOpen_ball hseg (isCompact_physCarrier S 1 NS.hp) (measurableSet_physCarrier S 1 NS.hp)
    (ae_mem_physCarrier S 1 NS.hp) h0m h0b h0h h0c h1m h1b h1h h1c hGm hGb hGh hGc hεpos hF0
  exact NS.clause_rot_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1 hle hS Sb hC hHm hcψ hMX' hδc hmarD
    hαD hsm hρ₀c hρp hRu hρpL hρcL ht₀ hCL.δ₁_pos hRt hb₁ hbC hSL hCL hdk hAl hSS hMM HB' hMXLn
    hmarDL hαDL hsmL hcψL hX₁L hBo hFLo hGs hrb hEr hF₁L' hSolL' hF₂s' hSol₂' hF₁b' hSolb' Zb Φ₀ hΦ₀
    T hTm A hAH

open Classical in
/-- **The five clauses of the recomputed family on a local pair** (route R-LOC, L5): under the
hypotheses of `clause_analytic_of`, `clause_rot_full_of`, `clause_local_of` and `coeffLoc_read_of`
(the cover constants `mixedKc`, `Cchi`; the fluctuation cores of `(Gl, Gd)` at the analyticity
radius `t` and at the gate radius `ε′`, with the constants of the system and of the old terms; the
settings of the old terms at both radii; the decoupling pairs of `(Gl, Gd)` pinned at the level of
the gate radius), the coefficient recomputed on `Gl` from the labels inside `T` (mask of the block
of the root, reference configuration `0`) has the clauses of `localFamily_of_coeff` for the polymer
`T`: analyticity and a nonnegative bound on `physVBg Gl t`, locality on the chart of radius
`ε_loc` with respect to `Y⁺ ⊇ thickSet S.G' (sitesOf T)`, invariance under the real rotations, and
the replacement identity at the pairs of the step chart of radius `ε ≤ t`. -/
theorem clauses_of (hS1 : S.a₁ = 1) (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
        (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (hd : 3 ≤ d) (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    -- the radii
    {eps' : ℝ} (hle : t ≤ eps')
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    {ε : ℝ} (hεt : ε ≤ t) {εloc : ℝ} (hεloc : εloc ≤ eps')
    -- the local pair
    (hAl : CubeAligned Gl m₁)
    (hSS : SupSep Gl m₁)
    (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k)
    (hdtop : Gd.Ω (k + 1) = ∅)
    (hHmtop : ∀ y ∈ Gl.Ω (k + 1), y ∈ Gd.Ω 1)
    (hrow : RowInHat (coverOf Gl) Gd (compWeight L S.a₁) S.ν)
    (Sb : Dec2.CoverBase (coverOf Gl) Gl (compWeight L S.a₁) S.ν (Dec2.mixedKc d L) (Cchi d L))
    -- the zero-source and bridge pairs
    {c c₂ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG)
    (hCz : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ t (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂ t)
    (hCz' : FlCore N Gl Gd S.a₁ S.ν c NS.BG NS.κ eps' (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂ t)
    (hMXd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
        (hCx : 0 ≤ Cchi d L)
    (hMXn : cstarX d L * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδc : 0 ≤ δc)
    (hdm : decDomMargin d L N NS.BG NS.κ (xiC1 d * t) < δc)
    (hα : K4 d L N NS.BG NS.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdm' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hα' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρ₀c : 2 * NS.p₁ ≤ cψ)
        (hρp : S.p₁ ≤ NS.p₁)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hBG₂ : 0 ≤ NS.BG₂)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.κ) (h1 : 1 ≤ (NS.κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (NS.κ / 2 - 1) / 2)
    {R₁ r : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r) (hrays : (2 * R₁ + r) * NS.p₁ ≤ cψ)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U)
    -- the old terms
    {cL c₂L : ℝ} (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL NS.O.BG)
    (hCo : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ t (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂
      NS.O.δ₁)
    (hCo' : FlCore N Gl Gd S.a₁ S.ν cL NS.O.BG NS.O.κ eps' (Dec2.mixedKc d L) (Cchi d L) c₂L
      NS.O.BG₂ NS.O.δ₁)
    (hMXLd : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXLn : cstarX d L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) {δcL : ℝ}
    (hdmL : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * t) < δcL)
    (hαL : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t) < coerciveConst d / 2)
    (hdmL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hcψL : 0 ≤ cψL)
    (hκκL : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ NS.O.κ) (h1L : 1 ≤ (NS.O.κ / 2 - 1) / 2)
    (hlogL : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ NS.O.m₀) ^ d : ℕ) : ℝ)) ≤
      (NS.O.κ / 2 - 1) / 2)
    (hρL : 0 < NS.O.ρ) (hρcL : NS.O.ρ ≤ cψL) (hρpL : S.p₁ ≤ NS.O.ρ)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    {a : ℝ} (hca : corrU ≤ a)
    (haL : a * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hRt : (corrU + t₀) *
      markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁)
    -- the settings of the old terms
    (hNm : L ^ NS.O.m₀ ∣ N₁) {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hoptL : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) W₀ ∧
        bondCost (scaleW L NS.O.m₀ m₁ (NS.O.jL τ)) E₀ = treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ))
    {Eb : NS.O.ι → ℝ} (hEb : ∀ τ, 0 ≤ Eb τ) {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {r₀ δ₃ δfl δ₃' δfl' ϱs : ℝ} {X₀ : NS.O.ι → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hBo : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ t δ₃
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ))
    {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs} {Kf Cf c₂f : ℝ}
    (hFLo : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG t δ₃ Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl (NS.O.X₁f τ))
    -- the numerical conditions of the settings of the old terms at the gate radius
    (hCN' : ChainNum d L N m₁ NS.O.BG NS.O.κ r₀ eps' δ₃')
    (hFN' : FlNum d L N NS.O.BG NS.O.BG₂ NS.O.κ eps' δ₃' NS.O.δ₁ δfl')
    (hGs : IsLevel Hs k)
    (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱl - 1)
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (NS.O.FkL τ) {p | ∃ D : BgData (NS.O.Gk τ) N,
      InUnionDomainC (NS.O.Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hEan : ∀ τ, AnalyticOnNhd ℂ (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
      (XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖(S.β : ℂ)⁻¹ * NS.O.Eτ τ r‖ ≤
        Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne NS.O.m₀ (NS.O.jL τ) (XL τ)))
    (hEr : ∀ τ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
      ∀ r ∈ XiCRaw (NS.O.Gj τ) (compWeight L S.a₁) S.ν (NS.O.jL τ) b
        (b ^ 2 * t + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        (S.β : ℂ)⁻¹ * NS.O.Eτ τ (rotRaw (cmat Q) r) = (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)
    -- the decoupling pairs of `(Gl, Gd)`
    (hF₂an : ∀ b, AnalyticOnNhd ℂ (F₂' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₂s' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' b (s, rawOf D) = (φ, α))
    (hSol₂an : ∀ b, AnalyticOnNhd ℂ (Sol₂' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps'))) t p.2})
    (hSol₂' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps'))) t p.2 →
        (Sol₂' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small Gd (Sol₂' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hF₁ban : ∀ b, AnalyticOnNhd ℂ (F₁b' b) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    (hSolban : ∀ b, AnalyticOnNhd ℂ (Solb' b) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps'))) t p.2})
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps'))) t p.2 →
        (Solb' b p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Solb' b p).2 ∧
        Small Gd (Solb' b p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Solb' b p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Solb' b p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Solb' b p).2))
    (hF₁Lan : ∀ τ, AnalyticOnNhd ℂ (F₁L' τ) {q | (∀ P, ‖q.1 P‖ < Real.exp NS.O.κ) ∧
      ∃ D : BgData Gl N, InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    (hSolLan : ∀ τ, AnalyticOnNhd ℂ (SolL' τ) {p | (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) ∧
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps'))) NS.O.δ₁ p.2})
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false (2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps'))) NS.O.δ₁ p.2 →
        (SolL' τ p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (SolL' τ p).2 ∧
        Small Gd (SolL' τ p).2 (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) ∧
        Small Gd (SolL' τ p).2 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        SupBounds Gd (SolL' τ p).1 (cK2' d L N (famConst d L NS.O.BG₂ NS.O.κ) * NS.O.δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα' (c6' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (SolL' τ p).2))
    -- the bounds in the class form and the numerical conditions of Theorem 3.4
    {εH κH κ' : ℝ} (hκH : κH ≤ 2 * κdec - 1)
    {F0 : ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) → ℝ}
    (hεz : 8 * (|S.β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
      ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t
        (rho4 d L N NS.BG NS.κ)‖ / r ^ 3)) ≤ εH)
    (hεo : ∀ Y ∈ NS.𝒴C, corrU / a * (|S.β| * (∑ τ, if Y ∈ polyDom S.G' (NS.O.X₁f τ) NS.O.m₀
        (NS.O.jL τ) (NS.O.𝒦X τ) then 2 * (Eb τ * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL τ)
          (XL τ) - 2 * κdec * treeLenCov S.G' NS.O.m₀ Y)) else 0)) ≤
      εH * Real.exp (-κH * treeLenCovOne 1 (k + 1) Y))
    (hFb : ∀ i, ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) t (rho4 d L N NS.BG NS.κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) ≤ F0 (Sum.inl i))
    (hFo : ∀ q, |S.β| * (Eb q.1.1 * Real.exp (-κ₀ * treeLenCovOne NS.O.m₀ (NS.O.jL q.1.1)
        (XL q.1.1) - 2 * κdec * treeLenCov S.G' NS.O.m₀ q.1.2) / t₀) ≤
      F0 (Sum.inr q) * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)))
    (hεpos : 0 < εH)
    (hι : Nonempty ({Y' // Y' ∈ bridgeFamily 1
      (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}))
    (hF0 : ∀ i, 0 < F0 i) (hκ' : 0 ≤ κ')
    (hκ : κ' + 3 * NS.Z.κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * (2 * (K0 d L NS.Z.κ0 + 1) + (K0 d L NS.Z.κ0 +
      rootUnionK d L 1 m₁ NS.Z.κ0) + rootUnionK d L 1 m₁ NS.Z.κ0) ^ 3 * c1 d L *
      Real.exp ((κH - 2 * NS.Z.κ0) * cG d L + c1 d L + κ' * cG d L)))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp NS.κ) < 1)
    -- the polymer, the chain's family and the read datum
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) (hΦ₀ : ∀ b u, Φ₀ b u = 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) {Ypl : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYpl : thickSet S.G' (sitesOf T) ⊆ Ypl)
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, e θ T = NS.coeff θ T)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (πb : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N Gl)
    (hπb : ∀ r (h : r ∈ rawSub N Gl), πb r = ⟨r, h⟩)
    (hdetT : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t D →
      newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) (S.blockU z)
          (⟨rawOf D, rawOf_mem_rawSub D⟩, 0) T =
        newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ)
            (maskPre S.hG' Gl (S.blockU z))
          (πb (clipRaw Gl (rawOf D)), 0) T) :
    ∃ bT : ℝ, 0 ≤ bT ∧
      AnalyticOnNhd ℂ
          (fun θb => NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps'
          (maskPre S.hG' Gl (S.blockU z)) Φ₀ θb T)
        (physVBg N Gl S.a₁ S.ν t) ∧
      (∀ θb ∈ physVBg N Gl S.a₁ S.ν t, ‖NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps'
          (maskPre S.hG' Gl (S.blockU z)) Φ₀ θb T‖ ≤ bT) ∧
      (∀ θb θb' : physParamBg N Gl,
        (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 εloc →
        (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 εloc → θb.2 = 0 → θb'.2 = 0 →
        (∀ x ∈ Ypl, (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x =
            (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x ∧
          (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x =
            (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x) →
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' (maskPre S.hG' Gl (S.blockU z)) Φ₀ θb T =
            NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps'
            (maskPre S.hG' Gl (S.blockU z)) Φ₀ θb' T) ∧
      (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ θb ∈ physVBg N Gl S.a₁ S.ν t, ∀ θb' ∈ physVBg N Gl S.a₁ S.ν t,
        (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
          rotRaw (cmat Q) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) →
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' (maskPre S.hG' Gl (S.blockU z)) Φ₀ θb' T =
            NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps'
            (maskPre S.hG' Gl (S.blockU z)) Φ₀ θb T) ∧
      (∀ q : Def6.Fld d L N₁ m₁ (k + 1) N × Def6.Fld d L N₁ m₁ (k + 1) N,
        Def6.XiDom S.G' (compWeight L S.a₁) S.ν (k + 1) ε q.1 q.2 →
        NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' (maskPre S.hG' Gl (S.blockU z)) Φ₀
            (πb (clipRaw Gl q), 0) T = e (π (clipRaw S.G' q), 0) T) := by
  have hk1 := S.hk1
  -- the settings of the old terms at the gate radius and the read condition of their data sites
  have hBo' : ∀ τ, BgSetting N S.G' (NS.O.Gk τ) (NS.O.Gj τ) S.a₁ S.ν cL NS.O.BG NS.O.κ r₀ eps' δ₃'
      (X₀ τ) (NS.O.X₁f τ) (NS.O.jL τ) := fun τ => { hBo τ with num := hCN' }
  have hFLo' : ∀ τ, FlSetting N S.G' (NS.O.Gk τ) Hs S.a₁ S.ν NS.O.κ NS.O.BG eps' δ₃' Kf Cf c₂f
      NS.O.BG₂ NS.O.δ₁ δfl' (NS.O.X₁f τ) := fun τ => { hFLo τ with num := hFN' }
  have hkX : ∀ τ, ∀ x ∈ dataSites (NS.O.Gk τ), x ∈ X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) :=
    fun τ x hx => by
      rw [← hX₁L τ]
      exact Finset.mem_coe.2 ((hBo τ).dep x hx x (self_mem_composeDep x))
  have hd0 : 0 < d := by omega
  have ha₁ : 1 / 2 ≤ S.a₁ := by rw [hS1]; norm_num
  have ha₂ : S.a₁ ≤ 2 := by rw [hS1]; norm_num
  have hρc : NS.p₁ ≤ cψ := by linarith [NS.Z.hp₁]
  have hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t := by
    have h := mul_lt_of_le_of_mul_lt (a := 1) (by norm_num [corrU]) hRu hCz.eps_pos zero_le_one
    rwa [one_mul] at h
  have hξ : 0 ≤ xiC1 d := by linarith [one_le_xiC1 d]
  have hK : 0 ≤ K4 d L N NS.BG NS.κ := (K4_pos (L := L) (N := N) (κ := NS.κ) hS.fam.2.1 hd0).le
  have hKL : 0 ≤ K4 d L N NS.O.BG NS.O.κ :=
    (K4_pos (L := L) (N := N) (κ := NS.O.κ) hSL.fam.2.1 hd0).le
  have h0' : 0 ≤ 2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps')) := by
    have := hCz'.eps_pos; positivity
  have h0L' : 0 ≤ 2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps')) := by
    have := hCz'.eps_pos; positivity
  have hle0 : 2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t)) ≤
      2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps')) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hξ) hK)
      (by norm_num)
  have hle0L : 2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t)) ≤
      2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps')) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hξ) hKL)
      (by norm_num)
  obtain ⟨bT, hbT, han, hbd⟩ := NS.clause_analytic_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1
    hle HB' hd SpG hS Sb hCz hMXd hCx hMXn hδc hdm hα hsm hcψ hBG₂ hdk hdtop
    hHmtop hrow hκ₀ hκdec hκκ h1 hlog hρc hδ₁c hR₁ hr hrays hR hRR hUR hU hF₂an hF₂s'
        (fun b => (hSol₂an b).mono fun _ hp => ⟨hp.1, strictDataM_mono_left hle0 hp.2⟩)
    (fun b p hp hs => hSol₂' b p hp (strictDataM_mono_left hle0 hs)) hF₁ban hF₁b'
        (fun b => (hSolban b).mono fun _ hp => ⟨hp.1, strictDataM_mono_left hle0 hp.2⟩)
        (fun b p hp hs => hSolb' b p hp (strictDataM_mono_left hle0 hs)) hSL Sb hCo hMXLd hCx hdmL
        hαL hsmL hcψL hκκL h1L hlogL
    hρL hρcL hRuL hca haL ht₀ hRt hF₁Lan hF₁L'
        (fun τ => (hSolLan τ).mono fun _ hp => ⟨hp.1, strictDataM_mono_left hle0L hp.2⟩)
        (fun τ p hp hs => hSolL' τ p hp (strictDataM_mono_left hle0L hs)) hcovL hX₁L hoptL hEb hb₁
        hbC hBo hFLo hGs
    hrb hFkan hEan hEbd hκH hεz hεo hFb hFo hεpos hι hF0 hκ' hκ hε hz (maskPre S.hG' Gl (S.blockU z)) Φ₀
    T hTm
  refine ⟨bT, hbT, han, hbd, ?_, ?_, ?_⟩
  · exact NS.clause_local_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1 SpG hCz' hdtop hHmtop hrow hcψ hMXn
      hδc hdm' hα' hsm hρ₀c hRu hCo' hρL hρcL ht₀ hRt hMXLn hdmL' hαL' hsmL hcψL HB' hdk hcovL hX₁L
      hBo' hFLo' hGs hrb hF₁L' hSolL' hF₂s' hSol₂' hF₁b' hSolb' (maskPre S.hG' Gl (S.blockU z)) Φ₀
      T hTm hYpl hεloc
  · exact NS.clause_rot_full_of F₂' Sol₂' F₁L' SolL' F₁b' Solb' hS1 hle HB' hd SpG
      hS Sb hCz hMXd hCx hMXn hδc hdm hα hsm hcψ hBG₂ hdk hdtop hHmtop hrow hκ₀ hκdec hκκ h1 hlog
      hρc hδ₁c hR₁ hr hrays hR hRR hUR hU hF₂an hF₂s'
          (fun b => (hSol₂an b).mono fun _ hp => ⟨hp.1, strictDataM_mono_left hle0 hp.2⟩)
          (fun b p hp hs => hSol₂' b p hp (strictDataM_mono_left hle0 hs)) hF₁ban hF₁b'
          (fun b => (hSolban b).mono fun _ hp => ⟨hp.1, strictDataM_mono_left hle0 hp.2⟩)
      (fun b p hp hs => hSolb' b p hp (strictDataM_mono_left hle0 hs)) hSL hCo hMXLd hdmL hαL hsmL
          hcψL hκκL h1L hlogL hρL hρcL hRuL hca haL ht₀ hRt hF₁Lan hF₁L'
      (fun τ => (hSolLan τ).mono fun _ hp => ⟨hp.1, strictDataM_mono_left hle0L hp.2⟩)
          (fun τ p hp hs => hSolL' τ p hp (strictDataM_mono_left hle0L hs)) hcovL hX₁L hoptL hEb hb₁
          hbC hBo hFLo hGs hrb hFkan hEan hEbd hκH hεz hεo hFb
      hFo hεpos hF0 hρ₀c hρp hρpL hRu hAl hSS hM hMXLn hEr (maskPre S.hG' Gl (S.blockU z)) Φ₀ hΦ₀ T
      hTm
  · exact NS.coeffLoc_read_of hAl hSS hPd hdk hdtop hN hm₁ hM hag
      hagl hagd HB HB' ha₁ ha₂ hS hCz.hκ hCz.hM hMXd hCz'.hS2.fam hCz'.hM2 h0' hCz.eps_pos hCz.B_le
      hCz'.B_le hCz.δ₁_le hCz.small1 hCz.c7le hCz.phi_lt hεr hCz'.small1 hCz'.c7le hCz'.phi_lt
      le_rfl hdm' hα' hsm hρ₀c hRu hSL hCo.hκ hCo.hM hMXLd hCo'.hS2.fam hCo'.hM2 h0L' hCo.δ₁_pos
      hCo.B_le hCo'.B_le hCo.δ₁_le hCo.c7le hCo.phi_lt hCo'.c7le hCo'.phi_lt le_rfl hdmL' hαL' hsmL
      hρL hρcL hRuL hNm hcovL hX₁L hkX hF₂s' hSol₂' hF₁L' hSolL' hF₁b' hSolb' T hTm e he π hπ πb hπb
      (maskPre S.hG' Gl (S.blockU z)) Φ₀ hdetT hεt

end NewLevelSystem

end Balaban.Inhabited
