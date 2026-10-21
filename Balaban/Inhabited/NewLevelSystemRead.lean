/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystemLoc
public import Balaban.Fluctuation.LocalClassChart

/-!
# The replacement identity for the coefficient recomputed from the labels inside the polymer

Route R-LOC, L5, the clause (A5) of `newLabels_castInputs_of_localFamily` (P3 p. 79): the
coefficient of the system recomputed on a local generating set `Gl` from the labels inside the
polymer `T` (`NewLevelSystem.coeffLoc`), read at the pair `q` of the step chart through the datum
of `Gl` (`clipRaw Gl q`, projected onto the data of `Gl` by a retraction `π_b`, zero sources),
equals the coefficient `e (π (clipRaw S.G' q), 0) T` of the chain's family, when `e` is the
coefficient of the system on the step chart (`NewLevelFormula`) and the determinant parts agree at
the read data (`newLevelDetBg_castG_canon` for the cast local sets).

* `NewLevelSystem.coeffLoc_read_of`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.LargeField Balaban.Polymer Finset MeasureTheory
  Balaban.Inhabited.MarkBudgetAudit

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl ϱl' : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr) {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}

/-- **The replacement identity (A5) for the recomputed family** (P3 p. 79; route R-LOC, L5): under
the hypotheses of `agree_canon` (the decoupling pairs of `(Gl, Gd)` given by their specifications,
the margin of the sites of `T` in the top layer of `Gl`), if `e` is the coefficient of the system on
the step chart of radius `t`, `π`, `π_b` are retractions onto the data of `S.G'` and of `Gl`, and
the determinant parts agree at the data of the step chart, then at every pair `q` of the step chart
of radius `ε ≤ t` the coefficient recomputed on `Gl` from the labels inside `T` at the datum read
from `q` equals `e (π (clipRaw S.G' q), 0) T`. -/
theorem coeffLoc_read_of
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    (HB : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν)
    (HB' : BgHyp d L (k + 1) ϱl (compWeight L S.a₁) S.ν)
    (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    -- the constants of the zero-source and bridge pairs
    {c c₂ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c NS.BG) (hκ : 0 < NS.κ)
    (hMc : c * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁)
    (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ NS.BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * NS.κ) ≤ (L : ℝ) ^ m₁) {δ₀' : ℝ} (h0' : 0 ≤ δ₀') (ht : 0 < t)
    (hδ₀ : 2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t)) ≤
      deltaStar' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8))
    (hδ₁ : t ≤ deltaStar' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8))
    {eps' : ℝ} (hsmall : (4 * d + 6) * ((2 * d + 1) * t) ≤ 1)
    (hc7 : xiC1 d * t ≤ c7 d L N NS.BG NS.κ)
    (hphi : (3 + K4 d L N NS.BG NS.κ) * (xiC1 d * t) < 1 / 2)
    (hεr : (2 * bgK1 d L N + 2) * xiC1 d * t ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1)
    (hc7' : xiC1 d * eps' ≤ c7 d L N NS.BG NS.κ)
    (hphi' : (3 + K4 d L N NS.BG NS.κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N NS.BG NS.κ * (xiC1 d * eps')) ≤ δ₀')
    {δc : ℝ} (hmarD' : decDomMargin d L N NS.BG NS.κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N NS.BG NS.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L NS.κ ≤ 1 / 4) {cψ : ℝ} (hρ₀c : 2 * NS.p₁ ≤ cψ)
    (hRu : corrU * markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t)
    -- the constants of the pairs of the old terms
    {cL c₂L : ℝ} (hSL : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) cL NS.O.BG)
    (hκL : 0 < NS.O.κ) (hMcL : cL * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hMXL : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁)
    (hF₂L : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂L NS.O.BG₂)
    (hM₂L : c₂L * Real.exp (N0 d L * NS.O.κ) ≤ (L : ℝ) ^ m₁) {δ₀L' : ℝ} (h0L' : 0 ≤ δ₀L')
    (h1L : 0 < NS.O.δ₁)
    (hδ₀L : 2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t)) ≤
      deltaStar' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8))
    (hδ₀L' : δ₀L' ≤ deltaStar' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8))
    (hδ₁L : NS.O.δ₁ ≤ deltaStar' d L N (famConst d L NS.O.BG₂ NS.O.κ) (gamma1 d / 8))
    (hc7L : xiC1 d * t ≤ c7 d L N NS.O.BG NS.O.κ)
    (hphiL : (3 + K4 d L N NS.O.BG NS.O.κ) * (xiC1 d * t) < 1 / 2)
    (hc7L' : xiC1 d * eps' ≤ c7 d L N NS.O.BG NS.O.κ)
    (hphiL' : (3 + K4 d L N NS.O.BG NS.O.κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀eL : 2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps')) ≤ δ₀L')
    {δcL : ℝ} (hmarDL' : decDomMargin d L N NS.O.BG NS.O.κ (xiC1 d * eps') < δcL)
    (hαDL' : K4 d L N NS.O.BG NS.O.κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsmL : δcL ^ 2 * smallConstX d L NS.O.κ ≤ 1 / 4) {cψL : ℝ} (hρL : 0 < NS.O.ρ)
    (hρcL : NS.O.ρ ≤ cψL)
    (hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁)
    -- the read conditions of the old terms
    (hNm : L ^ NS.O.m₀ ∣ N₁) {XL : NS.O.ι → Set (CTorus d L N₁ m₁ (k + 1))}
    (hcovL : ∀ τ, CovSetup S.G' NS.O.m₀ (NS.O.jL τ) (XL τ) (NS.O.𝒦X τ))
    (hX₁L : ∀ τ, (↑(NS.O.X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) =
      X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    (hkX : ∀ τ, ∀ x ∈ dataSites (NS.O.Gk τ), x ∈ X1 S.G' NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ))
    -- the decoupling pairs of `(Gl, Gd)`
    {F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₂s' : ∀ z (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₂' z (s, rawOf D) = (φ, α))
    {Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSol₂' : ∀ z (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false δ₀' t p.2 →
        (Sol₂' z p).1 = dphi Gd (Dec2.decG (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z p).2 ∧
        Small Gd (Sol₂' z p).2 (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) ∧
        Small Gd (Sol₂' z p).2 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        SupBounds Gd (Sol₂' z p).1 (cK2' d L N (famConst d L NS.BG₂ NS.κ) * t) ∧
        (∀ δα' : Gd.Ω 1 → ℂ, Small Gd δα' (c6' d L N (famConst d L NS.BG₂ NS.κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Gd (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Gd (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' z p).2))
    {F₁L' : NS.O.ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁L' : ∀ τ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp NS.O.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.O.BG NS.O.κ) S.ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ) (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl
        (compWeight L S.a₁) S.ν (rho4 d L N NS.O.BG NS.O.κ) s D φ α →
        F₁L' τ (s, rawOf D) = (φ, α))
    {SolL' : NS.O.ι → Dec2.DecParams (coverOf Gl) × Edat Gd N →
      (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolL' : ∀ τ (p : Dec2.DecParams (coverOf Gl) × Edat Gd N),
      (∀ P, ‖p.1 P‖ < Real.exp NS.O.κ) →
      StrictDataM Gd N false δ₀L' NS.O.δ₁ p.2 →
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
    {F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁b' : ∀ b (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl (compWeight L S.a₁) S.ν
          (rho4 d L N NS.BG NS.κ) s D φ α → F₁b' b (s, rawOf D) = (φ, α))
    {Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ)}
    (hSolb' : ∀ b (p : Dec2.DecParams (coverOf Gl) × Edat Gd N), (∀ P, ‖p.1 P‖ < Real.exp NS.κ) →
      StrictDataM Gd N false δ₀' t p.2 →
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
    -- the read datum and the polymer
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTmar : ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    -- the family of the chain, its projection, and the retraction onto the data of `Gl`
    (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1
      (k + 1) Set.univ) → ℂ)
    (he : ∀ θ ∈ physV S S.a₁ S.ν t, e θ T = NS.coeff θ T)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hπ : ∀ r (h : r ∈ rawSub N S.G'), π r = ⟨r, h⟩)
    (πb : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N Gl)
    (hπb : ∀ r (h : r ∈ rawSub N Gl), πb r = ⟨r, h⟩) (Zb : Finset (unitPts Gl))
    (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    -- the determinant parts at the read data
    (hdetT : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t D →
      newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) (S.blockU z)
          (⟨rawOf D, rawOf_mem_rawSub D⟩, 0) T =
        newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb
          (πb (clipRaw Gl (rawOf D)), 0) T)
    {ε : ℝ} (hεt : ε ≤ t) :
    ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      XiDom S.G' (compWeight L S.a₁) S.ν (k + 1) ε q.1 q.2 →
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ (πb (clipRaw Gl q), 0) T =
        e (π (clipRaw S.G' q), 0) T := by
  intro q hq
  have hqS : clipRaw S.G' q = q := clipRaw_of_isLevel S.hG' q
  obtain ⟨D, hD, hDq⟩ := clipRaw_mem_xiCRaw_of_xiDom hεt hq
  have hDq' : rawOf D = q := by rw [← hDq, hqS]
  set θ : physParam N S := (π (clipRaw S.G' q), 0) with hθdef
  have hθ1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D := by
    show ((π (clipRaw S.G' q) : rawSub N S.G') : RawData d L (N₁ * L ^ m₁) (k + 1) N) = _
    rw [hπ _ (by rw [hDq]; exact rawOf_mem_rawSub D)]
    exact hDq
  have hθV : θ ∈ physV S S.a₁ S.ν t := by
    refine ⟨⟨D, hD, hθ1⟩, ?_⟩
    show ∑ x, ∑ i, ‖(0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) x i‖ < 1
    simp
  have hread : clipRaw Gl (rawOf D) ∈ rawSub N Gl :=
    BgTransport.reads_canon (Gb := Gl) (N := N) S.hG' D
  have hθb : ((πb (clipRaw Gl q), (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)).1 :
      RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D) := by
    show ((πb (clipRaw Gl q) : rawSub N Gl) : RawData d L (N₁ * L ^ m₁) (k + 1) N) = _
    rw [← hDq', hπb _ hread]
  obtain ⟨hA', hG'⟩ := NS.agree_canon hA hSS hPd hdk hdtop hN hm₁ hM hag hagl hagd HB HB' ha₁ ha₂ hS
    hκ hMc hMX hF₂ hM₂ h0' ht hδ₀ hδ₀' hδ₁ hsmall hc7 hphi hεr hsmall' hc7' hphi' hδ₀e hmarD' hαD'
    hsm hρ₀c hRu hSL hκL hMcL hMXL hF₂L hM₂L h0L' h1L hδ₀L hδ₀L' hδ₁L hc7L hphiL hc7L' hphiL' hδ₀eL
    hmarDL' hαDL' hsmL hρL hρcL hRuL hNm hcovL hX₁L hkX hF₂s' hSol₂' hF₁L' hSolL' hF₁b' hSolb' hD θ
    hθV hθ1 (πb (clipRaw Gl q), 0) hθb T hTmar
  have hdet : newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) (S.blockU z) θ T =
      newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb
        (πb (clipRaw Gl q), 0) T := by
    have hθeq : θ = (⟨rawOf D, rawOf_mem_rawSub D⟩, 0) := Prod.ext (Subtype.ext hθ1) rfl
    rw [hθeq, ← hDq']
    exact hdetT D hD
  rw [he θ hθV]
  exact (NS.coeff_eq_coeffLoc_of_agree F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θ _ T hdet hA'
    hG').symm

end NewLevelSystem

end Balaban.Inhabited
