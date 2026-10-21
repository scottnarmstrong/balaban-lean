/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelCoeffBgClassCast
public import Balaban.Inhabited.NewLevelSystem
public import Balaban.Fluctuation.NewLevelCoeffLoc

/-!
# The system of the new level recomputed on a local generating set (`NewLevelSystemCanon`)

P3 pp. 78-79, (4.44)-(4.47): the class chain returns the coefficient of the new level as the
coefficient `NS.coeff` of a `NewLevelSystem` (W1147).  Here the same system is recomputed on a local
generating set `Gl` with the canonical transport: the zero-source activities `zeroActBg`, the
activities `oldActBg` and marks `oldMarkGBg` of the old terms and the bridge marks
`e1MarkGParamGBgOn`, with decoupling pairs `(F₂′, Sol₂′)`, `(F₁L′, SolL′)`, `(F₁b′, Solb′)` of
`(Gl, Gd)`, the expansion (labels, anchors) of the system.

* `NewLevelSystem.coeffBg`: the coefficient of the system recomputed on `Gl` at a parameter of `Gl`
  (the formula `newLevelCoeffBg` with `classActFun` of the recomputed activities);
* `NewLevelSystem.zeroAct_eq_zeroActBg`: the zero-source family of the system is `zeroActBg` at the
  step's own set (`zeroSourceAct_labelActFamilyOn_H_eq` with the formula `hT` of the system and
  `zeroTermBg_self`);
* `NewLevelSystem.coeff_eq_coeffBg_canon_of_det`: **the replacement identity (A5) for the system**:
  at the datum read from a datum of the step chart, the coefficient of the system equals the
  coefficient recomputed on `Gl`, when the determinant parts agree
  (`newLevelCoeffBg_class_canon_eq_of_det_gen`; the pins, formulas and equations of the system give
  its hypotheses `h0eq`, `h1eq`, `hG₁eq`, and the locality of the marks `NewLevelSystem.G_dep` its
  hypothesis `hGdep`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.LargeField Balaban.Polymer Finset MeasureTheory
  Balaban.Inhabited.MarkBudgetAudit

namespace NewLevelSystem

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱl ϱl' : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {C : StepClass d L N₁ m₁ k N ϱ}
  {z : RootIdx d L N₁ m₁ (k + 1)} {t pp : ℝ} {Jr : S.JointRep t pp}
  (NS : NewLevelSystem S C z Jr) {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
  {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}

/-- **The activities of the system recomputed on a local generating set `Gl`** (P3 pp. 78-79,
(4.44)-(4.47)) as functions of a parameter of `Gl`: the zero-source activities `zeroActBg` (pairs
`F₂′`, `Sol₂′` per block) on the zero-source labels, the activities `oldActBg` of the old terms
(pairs `F₁L′`, `SolL′`) on the thick labels, `0` on the root-union labels; canonical transport, gate
radius `ε′`. -/
noncomputable def actBg
    (F₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
    (Sol₂' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
    (F₁L' : NS.O.ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
    (SolL' : NS.O.ι → Dec2.DecParams (coverOf Gl) × Edat Gd N →
      (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
    (eps' : ℝ) : physParamBg N Gl → ℂ →
      NS.Lb1 ⊕ RootUnionLb 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) →
      (∀ b, (S.blockSplit 1 NS.hp).Ωb b) → ℂ :=
  classActFun
    (fun θb u (Y : {Y // Y ∈ NS.Z.I.𝒴}) Φ => zeroActBg S Gl (BgTransport.canon S.G' Gl N)
      (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
      (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 F₂' Sol₂' taylorWeight NS.p₁
      NS.hp eps' θb u Y.1 Φ)
    (fun θb u Y Φ => oldActBg S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps' NS.𝒴C θb Y u Φ)

/-- **The marks of the system recomputed on a local generating set `Gl`** (P3 pp. 78-79,
(4.44)-(4.47)) as functions of a parameter of `Gl`: the bridge marks `e1MarkGParamGBgOn` (pairs
`F₁b′`, `Solb′`) and the marks `oldMarkGBg` of the old terms (pairs `F₁L′`, `SolL′`); canonical
transport, mask `maskPre` of the block of the root, gate radius `ε′`. -/
noncomputable def markBg
    (F₁L' : NS.O.ι → Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
    (SolL' : NS.O.ι → Dec2.DecParams (coverOf Gl) × Edat Gd N →
      (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
    (F₁b' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ))
    (Solb' : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gl) × Edat Gd N → (Gd.Ω 1 × Fin N → ℂ) × (Gd.Ω 1 → ℂ))
    (eps' : ℝ) (θb : physParamBg N Gl) :
    ({Y' // Y' ∈ bridgeFamily 1 (fun _ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
      (Set.univ : Set (CTorus d L N₁ m₁ (k + 1)))) (e1DomG S) z} ⊕
      {q // q ∈ markedIdx (fun _ : NS.O.ι => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ)) z}) →
      ℂ → (∀ b, (S.blockSplit 1 NS.hp).Ωb b) → ℂ :=
  Sum.elim
    (fun i u Φ => e1MarkGParamGBgOn S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' NS.p₁ NS.hp z Gl eps' θb i u Φ)
    (oldMarkGBg S Gl (BgTransport.canon S.G' Gl N) (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f
      NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL'
      (fun τ => eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
        (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) NS.O.ρ NS.hp corrU eps' z θb)

/-- **The coefficient of the system recomputed on a local generating set `Gl`** (P3 pp. 78-79,
(4.44)-(4.47)) at a parameter `θ_b` of `Gl`: the formula `newLevelCoeffBg` on `Gl` with the
labels and anchors of the system, the zero-source activities `zeroActBg` (pairs `F₂′`, `Sol₂′` per
block), the activities `oldActBg` and marks `oldMarkGBg` of the old terms (pairs `F₁L′`, `SolL′`),
and the bridge marks `e1MarkGParamGBgOn` (pairs `F₁b′`, `Solb′`), all with the canonical transport,
the mask `maskPre` of the block of the root and the gate radius `ε′`; `Zb` the mask of the
determinant part. -/
noncomputable def coeffBg
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
    (eps' : ℝ) (Zb : Finset (unitPts Gl)) (θb : physParamBg N Gl)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    ℂ :=
  newLevelCoeffBg Gl (S.blockSplit 1 NS.hp).μ (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb
    NS.Lab (NS.actBg F₂' Sol₂' F₁L' SolL' eps') NS.y0 (NS.markBg F₁L' SolL' F₁b' Solb' eps') θb T

/-- **The coefficient of the system recomputed on a local generating set `Gl` from the labels
inside the polymer** (P3 pp. 78-79, (4.44)-(4.47); route R-LOC, the recomputed family): the local
formula `newLevelCoeffLoc` on `Gl` with the recomputed activities `actBg` and marks `markBg`, the
activities and marks of the labels and anchors inside `T` evaluated at the configuration restricted
to the blocks of their label (reference configuration `Φ₀` off them). -/
noncomputable def coeffLoc
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
    (eps' : ℝ) (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (θb : physParamBg N Gl)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ)) :
    ℂ :=
  newLevelCoeffLoc Gl (S.blockSplit 1 NS.hp).μ (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb
    NS.Lab Φ₀ (NS.actBg F₂' Sol₂' F₁L' SolL' eps') NS.y0 (NS.markBg F₁L' SolL' F₁b' Solb' eps') θb T

/-- **The zero-source family of the system is the formula at the step's own set**: for a
parameter `θ` of the step chart (`θ ∈ physV`) and `‖u‖ < 2`, the activity of the label `Y` of the
zero-source family `NS.Z.A₀` is `zeroActBg` at `S.G'` with `BgTransport.self` and the pairs
`F₂`, `Sol₂` of the system. -/
theorem zeroAct_eq_zeroActBg {θ : physParam N S} (hθV : θ ∈ physV S S.a₁ S.ν t) {u : ℂ}
    (hu : ‖u‖ < 2) (Y : {Y // Y ∈ NS.Z.I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b) :
    (NS.Z.A₀ θ u).H Y Φ =
      zeroActBg S S.G' (BgTransport.self S.hG')
        (fun b => LocalCover.nbhdF 1 (LocalCover.blockSite k b)) (fun _ => k)
        (fun b => LocalCover.fam 1 (LocalCover.blockSite k b)) 1 NS.Z.F₂ NS.Z.Sol₂ taylorWeight
        NS.p₁ NS.hp t θ u Y.1 Φ := by
  have hV0 : ((θ.1, 0) : physParam N S) ∈ physVq S S.a₁ S.ν t 1 := by
    rw [physVq_one]
    refine ⟨hθV.1, ?_⟩
    show ∑ x, ∑ i, ‖(0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) x i‖ < 1
    simp
  exact zeroSourceAct_labelActFamilyOn_H_eq S NS.Z.hF NS.Z.hN NS.Z.hp₁ NS.Z.hεU NS.Z.hκ0
    (by have := K0_pos d L NS.Z.κ0; linarith) _ _ _ NS.Z.F₂ NS.Z.Sol₂ taylorWeight
    (fun Y x w σ Θ => (NS.Z.hT Y x w σ Θ).trans (zeroTermBg_self S _ _ _ 1 NS.Z.F₂ NS.Z.Sol₂
      taylorWeight Y x.1 w.1 σ Θ).symm) θ hV0 hθV.1 hu Y Φ

/-- **The replacement identity (A5) for the system, label by label** (P3 pp. 78-79, (4.44)-(4.47)).
Under the hypotheses of `coeff_eq_coeffBg_canon_of_det` (without the determinant part): at the step's
parameter `θ` with the datum `D` of the step chart and the parameter `θ_b` of `Gl` with the read
datum, the activities of the system agree with the recomputed activities `actBg` on the labels whose
blocks lie in `T`, and its marks with the recomputed marks `markBg` on the anchors whose blocks lie
in `T`, for `s ∈ [0, 1]`. -/
theorem agree_canon
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
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t D)
    (θ : physParam N S) (hθV : θ ∈ physV S S.a₁ S.ν t)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTmar : ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1)) :
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite y) ⊆ T →
      (NS.A θ (s : ℂ)).H y = NS.actBg F₂' Sol₂' F₁L' SolL' eps' θb (s : ℂ) y) ∧
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i,
      blocksOf 1 (k + 1) Set.univ (NS.Lab.ysite (NS.y0 i)) ⊆ T →
      NS.G θ i (s : ℂ) = NS.markBg F₁L' SolL' F₁b' Solb' eps' θb i (s : ℂ)) := by
  classical
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have h0 : 0 ≤ 2 * (K4 d L N NS.BG NS.κ * (xiC1 d * t)) := by
    have := K4_pos (L := L) (N := N) (κ := NS.κ) hS.fam.2.1 hd0
    positivity
  have h0L : 0 ≤ 2 * (K4 d L N NS.O.BG NS.O.κ * (xiC1 d * t)) := by
    have := K4_pos (L := L) (N := N) (κ := NS.O.κ) hSL.fam.2.1 hd0
    positivity
  have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖(s : ℂ)‖ < 2 := fun s hs => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    linarith [hs.2]
  have h := newLevelCoeffBg_class_canon_agree S S.hG hA hSS hPd hdk hdtop hN hm₁ hM hag hag
    hagl hagd hS HB HB' ha₁ ha₂ hκ hMc hMX hF₂ hM₂ h0 h0' ht hδ₀ hδ₀' hδ₁ ht hsmall hc7 hphi le_rfl
    hεr hsmall' hc7' hphi' le_rfl hδ₀e hmarD' hαD' hsm NS.Z.hp₁ hρ₀c hρL NS.hp
    (by norm_num [corrU]) hRu NS.Z.hN NS.hL NS.Z.I.𝒴 NS.Z.I.dom
    (fun b => LocalCover.covSetup S.hG' NS.Z.hN (le_refl (k + 1)) (LocalCover.blockSite k b))
    (fun b => LocalCover.coe_nbhdF_eq_X1 S.hG' NS.Z.hN (le_refl (k + 1)) (LocalCover.blockSite k b))
    (fun b x hx => by
      rw [← LocalCover.coe_nbhdF_eq_X1 S.hG' NS.Z.hN (le_refl (k + 1))]
      exact LocalCover.blockSites_subset_nbhdF 1 (le_refl (k + 1)) b (Finset.mem_coe.2 hx))
    (fun b s D hs hDd φ α hI => NS.Z.hF₂ b s D hs hDd φ α
      ((dec2_isDecBg_iff S.G' _ _ _ s D φ α).1 hI)) hF₂s' NS.Z.hSol₂ hSol₂' taylorWeight hNm
    hcovL hX₁L NS.O.Gk NS.O.Gj hkX (compWeight L S.a₁) NS.O.FkL
    (fun τ r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r) hSL hκL hMcL hMXL hF₂L hM₂L h0L h0L' h1L hδ₀L hδ₀L'
    hδ₁L hc7L hphiL hc7L' hphiL' le_rfl hδ₀eL hmarDL' hαDL' hsmL hρcL hRuL
    (fun τ s D hs hDd φ α hI => NS.O.hF₁L τ s D hs hDd φ α
      ((dec2_isDecBg_iff S.G' _ _ _ s D φ α).1 hI)) hF₁L' NS.O.hSolL hSolL' NS.𝒴C NS.h𝒴dj
    NS.hdomC
    (fun b s D hs hDd φ α hI => NS.hF₁ b s D hs hDd φ α
      ((dec2_isDecBg_iff S.G' _ _ _ s D φ α).1 hI)) hF₁b' NS.hSol hSolb' z NS.hdomE NS.Z.A₀
    NS.AC NS.y1 (fun _ => rfl) NS.G₁ hD θ hθ θb hθb
    (fun s hs Y Φ => NS.zeroAct_eq_zeroActBg hθV (hseg s hs) Y Φ)
    (fun s _ Y Φ => by rw [NS.hAC θ hθV]; exact NS.hH θ Y s Φ)
    (fun s _ q Φ => NS.hG₁ θ q s Φ) T hTmar
  exact ⟨commonAct_sum_H_agree NS.Z.A₀ NS.AC NS.Z.hN NS.hL _ _ NS.hdomC _ _ NS.hdomE NS.hεC
    (le_max_of_le_right NS.hεC) NS.hκ02 θ _ _ θb T h.1 h.2.1, fun s hs i hi => h.2.2 s hs i hi⟩

/-- **The replacement identity (A5) for the system of the new level, reduced to the determinant
part** (P3 pp. 78-79, (4.44)-(4.47)).  Let `Gl` be cube aligned and sup-separated, `Gd ≺ Gl` with the
layer `k` of `Gl` and no layer `k + 1`, and let the decoupling pairs of `(Gl, Gd)` be given by their
specifications: `(F₂′, Sol₂′)` and `(F₁b′, Solb′)` per block with the constants `κ, BG, BG₂` of the
system (levels `(δ₀′, t)`), `(F₁L′, SolL′)` per old term with the constants of the inherited levels
(levels `(δ₀L′, δ₁)`).  For a datum `D` of the step chart of radius `t`, the step's parameter
`θ ∈ physV` with the datum `D` and the parameter `θ_b` of `Gl` with the read datum, if the sites of
`T` have the margin `2 M₁ L^{k+1}` in the top layer of `Gl`, the coefficient of the system equals its coefficient recomputed on `Gl`
(`NewLevelSystem.coeffBg`), when the determinant parts agree.  The hypotheses on `ε′`, `R_u = 17/16`
and the radii are smallness conditions against absolute constants. -/
theorem coeff_eq_coeffBg_canon_of_det
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
    {D : BgData S.G' N} (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 t D)
    (θ : physParam N S) (hθV : θ ∈ physV S S.a₁ S.ν t)
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = rawOf D) (θb : physParamBg N Gl)
    (hθb : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw Gl (rawOf D))
    (Zb : Finset (unitPts Gl))
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTmar : ∀ x ∈ sitesOf T, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1))
    (hdet : newLevelDetBg S.G' (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) (S.blockU z) θ T =
      newLevelDetBg Gl (compWeight L 1) 1 S.ν (rho4 d L N NS.BG NS.κ) Zb θb T) :
    NS.coeff θ T = NS.coeffBg F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb θb T := by
  obtain ⟨hA', hG'⟩ :=
    NS.agree_canon hA hSS hPd hdk hdtop hN hm₁ hM hag hagl hagd HB HB' ha₁ ha₂ hS hκ hMc hMX hF₂
      hM₂ h0' ht hδ₀ hδ₀' hδ₁ hsmall hc7 hphi hεr hsmall' hc7' hphi' hδ₀e hmarD' hαD' hsm hρ₀c hRu
      hSL hκL hMcL hMXL hF₂L hM₂L h0L' h1L hδ₀L hδ₀L' hδ₁L hc7L hphiL hc7L' hphiL' hδ₀eL hmarDL'
      hαDL' hsmL hρL hρcL hRuL hNm hcovL hX₁L hkX hF₂s' hSol₂' hF₁L' hSolL' hF₁b' hSolb' hD θ hθV
      hθ θb hθb T hTmar
  exact newLevelCoeffBg_eq_of_agree Gl (S.blockSplit 1 NS.hp).μ S.G' (compWeight L 1) 1 S.ν
    (rho4 d L N NS.BG NS.κ) (S.blockU z) Zb NS.Lab (NS.A θ) NS.y0 (NS.G θ) θ
    (NS.actBg F₂' Sol₂' F₁L' SolL' eps') (NS.markBg F₁L' SolL' F₁b' Solb' eps') θb T hdet
    (NS.G_dep θ) hA' hG'

end NewLevelSystem

end Balaban.Inhabited
