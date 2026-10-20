/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelSystemLoc
public import Balaban.Inhabited.NewLevelObjectsBgLocal
public import Balaban.Fluctuation.NewLevelDetBgLocal
public import Balaban.Inhabited.NewLevelBridgeMarksBgFields
public import Balaban.Fluctuation.NewLevelOldTermsBgFields

/-!
# Locality of the coefficient recomputed from the labels inside the polymer

Route R-LOC, L5, the clause (A3) of `newLabels_castInputs_of_localFamily` (P3 pp. 78-79 and
Lemma 4.2 at `Gl`, (AE2)): the coefficient of the system recomputed on a local generating set `Gl`
from the labels inside the polymer `T` (`NewLevelSystem.coeffLoc`, gate radius `ε′`) takes the same
value at two parameters of the chart of `Gl` of radius `ε′` whose raw data agree on
`thickSet S.G' (sitesOf T)`, when the sites of `T` have the label margin in `Gl`.

The determinant part is local by `newLevelDetBg_local_of_margin`, the zero-source activities by
`zeroActBg_canon_local`, the bridge marks by `e1MarkGParamGBgOn_congr_of_terms` with the locality of
the block-energy terms (`evDecBg_canon_local_blockEnergy`), the old activities and marks by
`oldActBg_congr_of_terms`, `oldMarkGBg_congr_of_terms` from the locality of the terms of the old
terms (`holdloc`, the conclusion of the agreement theorem of the old terms at `Gl`).

* `NewLevelSystem.coeffLoc_local_of`.
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
/-- **Locality of the coefficient recomputed from the labels inside `T`** (P3 pp. 78-79 and
Lemma 4.2 at `Gl`, (AE2); the form of (A3)).  Let `(Gl, Gd)` have the fluctuation core at the gate
radius `ε′` with the constants of the system (`hC`, determinant, zero-source and bridge pairs) and
with those of the old terms (`hCL`), `Gd` without layer `k + 1` covering the top layer of `Gl`, the
decoupling pairs of `(Gl, Gd)` given by their specifications, and the terms of the old terms local
at `Gl` (`holdloc`).  For a polymer `T` whose sites have the label margin in `Gl`, the coefficients
recomputed at two parameters of the chart of radius `ε′` whose raw data agree on
`thickSet S.G' (sitesOf T)` are equal. -/
theorem coeffLoc_local_of (hS1 : S.a₁ = 1) (SpG : DGSetting S.G' (compWeight L S.a₁) S.ν)
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
    (holdloc : ∀ τ (um tm : ℂ), (‖um‖ + ‖tm‖) *
        markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ →
      ∀ Y, LabelMargin Gl Y → ∀ u ∈ XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps' ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψL},
      ∀ u' ∈ XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps' ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψL},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) Gl S.a₁ S.ν
            (BgTransport.canon S.G' Gl N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L' τ)
            (SolL' τ) (eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
              (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) (maskPre S.hG' Gl (S.blockU z)) um tm Y
            (u.1, (BgTransport.canon S.G' Gl N).res u.2) =
          evDecBg S.G' (NS.O.X₁f τ) NS.O.m₀ (NS.O.jL τ) (NS.O.𝒦X τ) Gl S.a₁ S.ν
            (BgTransport.canon S.G' Gl N) ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L' τ)
            (SolL' τ) (eTermFun Gl (NS.O.Gk τ) (NS.O.Gj τ) Gd (compWeight L S.a₁) (NS.O.FkL τ)
              (fun r => (S.β : ℂ)⁻¹ * NS.O.Eτ τ r)) (maskPre S.hG' Gl (S.blockU z)) um tm Y
            (u'.1, (BgTransport.canon S.G' Gl N).res u'.2))
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
    -- the polymer and the two parameters
    (Zb : Finset (unitPts Gl)) (Φ₀ : ∀ b, (S.blockSplit 1 NS.hp).Ωb b)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hTm : LabelMargin Gl (sitesOf T)) {θb θb' : physParamBg N Gl}
    (hθ : (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps')
    (hθ' : (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gl (compWeight L S.a₁) S.ν (k + 1) 1 eps')
    (hag : agreeOn (thickSet S.G' (sitesOf T)) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) :
    NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb T =
      NS.coeffLoc F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ θb' T := by
  have ht : 0 < t := hC.δ₁_pos
  have hL2 : 2 ≤ L := NS.hL
  -- labels inside `T` lie in the sites of `T`: the margin and the agreement descend
  have hsub : ∀ {Y : Set (CTorus d L N₁ m₁ (k + 1))}, Y ⊆ sitesOf T →
      LabelMargin Gl Y ∧ agreeOn (thickSet S.G' Y) (θb.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        (θb'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) := fun hY =>
    ⟨labelMargin_of_subset hY hTm, agreeOn_mono (thickSet_mono hY) hag⟩
  -- the cover of the blocks
  have hcovB := fun b => LocalCover.covSetup S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  have hX₁B := fun b => LocalCover.coe_nbhdF_eq_X1 S.hG' NS.Z.hN (le_refl (k + 1))
    (LocalCover.blockSite k b)
  have hZB : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      readSites Gd k b ⊆ ↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)) := fun b =>
    LocalCover.readSites_subset_nbhdF Gd hL2 1 le_rfl b
  have hBMB : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      BlockMargin S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b))
        (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))) := fun b =>
    LocalCover.blockMargin SpG S.hG' le_rfl _ (LocalCover.blockSites_subset_cell 1 le_rfl b)
  -- the pins at the level of the fluctuation core
  have hF₂n : ∀ b (s : DecParams Gl) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), IsDecBg Gl (compWeight L S.a₁) S.ν (rho4 d L N NS.BG NS.κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α) := fun b s D hs hD φ α hI =>
    hF₂s' b s D hs hD φ α ((dec2_isDecBg_iff Gl _ _ _ s D φ α).2 hI)
  have hF₁n : ∀ b (s : DecParams Gl) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp NS.κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N NS.BG NS.κ) S.ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), IsDecBg Gl (compWeight L S.a₁) S.ν (rho4 d L N NS.BG NS.κ) s D φ α →
        F₁b' b (s, rawOf D) = (φ, α) := fun b s D hs hD φ α hI =>
    hF₁b' b s D hs hD φ α ((dec2_isDecBg_iff Gl _ _ _ s D φ α).2 hI)
  -- the radii of the marks
  have hδ₁c : markedRad d L N k S.a₁ NS.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < t := by
    have h := mul_lt_of_le_of_mul_lt (a := 1) (by norm_num [corrU]) hRu ht zero_le_one
    rwa [one_mul] at h
  have hRuL : corrU * markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) <
      NS.O.δ₁ :=
    mul_lt_of_le_of_mul_lt (by linarith) hRt hCL.δ₁_pos (by norm_num [corrU])
  have hboxL : ∀ Ψ : (∀ b, (S.blockSplit 1 NS.hp).Ωb b), ∀ q',
      ‖S.hatOf 1 NS.O.ρ NS.hp Ψ q'‖ ≤ cψL :=
    fun Ψ q' => (S.hatOf_mem 1 hρL NS.hp Ψ q').trans hρcL
  have hbox : ∀ Ψ : (∀ b, (S.blockSplit 1 NS.hp).Ωb b), ∀ q',
      ‖S.hatOf 1 NS.p₁ NS.hp Ψ q'‖ ≤ cψ :=
    fun Ψ q' => (S.hatOf_mem 1 NS.Z.hp₁ NS.hp Ψ q').trans (by linarith [NS.Z.hp₁])
  refine NS.coeffLoc_congr_of_parts F₂' Sol₂' F₁L' SolL' F₁b' Solb' eps' Zb Φ₀ T ?_
    (fun s _ Y hY Φ => ?_) (fun s _ Y hY Φ => ?_) (fun s _ i hi Φ => ?_) (fun s _ q hq Φ => ?_)
  · -- the determinant part
    have h := newLevelDetBg_local_of_margin hC S.hk1 hδc hMX hsm hdm hα S.hG' NS.Z.hN Zb T hTm
      hθ hθ' hag
    rw [hS1] at h
    exact h
  · -- the zero-source activities
    obtain ⟨hYm, hYag⟩ := hsub (Y := Y.1)
      (ysite_subset_sitesOf NS.Z.hN NS.Lab (Sum.inl (Sum.inl Y)) hY)
    exact zeroActBg_canon_local S hC hHm hHmtop hrow hcψ hMX hdm hα hsm hcovB hX₁B hF₂n hSol₂'
      hZB hBMB hδ₁c taylorWeight NS.Z.hp₁ hρ₀c NS.hp hYm hθ hθ' hYag (s : ℂ) Φ
  · -- the old activities
    obtain ⟨hYm, hYag⟩ := hsub (Y := Y.1) (ysite_subset_sitesOf NS.Z.hN NS.Lab
      (Sum.inl (Sum.inr (Sum.inl Y))) hY)
    refine oldActBg_congr_of_terms S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL' _ NS.O.ρ
      NS.hp corrU eps' NS.𝒴C hθ hθ' Y Φ Φ (fun τ _ um hum => ?_) (by norm_num [corrU]) (s : ℂ)
    exact holdloc τ um 0 (mem_markedRad_of_le hCL.δ₁_pos hRuL hum.le) Y.1 hYm
      (θb.1, S.hatOf 1 NS.O.ρ NS.hp Φ) ⟨hθ, hboxL Φ⟩ (θb'.1, S.hatOf 1 NS.O.ρ NS.hp Φ)
      ⟨hθ', hboxL Φ⟩ ⟨hYag, fun _ _ _ => rfl⟩
  · -- the bridge marks
    have hiT : i.1 ⊆ sitesOf T := ysite_subset_sitesOf NS.Z.hN NS.Lab (NS.y0 (Sum.inl i)) hi
    refine e1MarkGParamGBgOn_congr_of_terms S (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) F₁b' Solb' NS.p₁ NS.hp z eps' (δ₁ := t) hRu ht hθ hθ' i Φ
      Φ (fun q hqm hbr v w hvw => ?_) (s : ℂ)
    have hbT : bridge 1 z q.2 ⊆ sitesOf T := by rw [hbr]; exact hiT
    obtain ⟨hYm, hYag⟩ := hsub (Y := q.2) ((subset_bridge z q.2).trans hbT)
    exact evDecBg_canon_local_blockEnergy hC S.hk1 S.hG' hHm hHmtop hrow _ hcψ hMX hdm hα hsm
      (hcovB q.1) (hX₁B q.1) (hF₁n q.1) (hSolb' q.1) q.1 (hZB q.1) (hBMB q.1)
      (maskPre S.hG' Gl (S.blockU z)) v w hvw q.2 hYm (θb.1, S.hatOf 1 NS.p₁ NS.hp Φ)
      ⟨hθ, hbox Φ⟩ (θb'.1, S.hatOf 1 NS.p₁ NS.hp Φ) ⟨hθ', hbox Φ⟩ ⟨hYag, fun _ _ _ => rfl⟩
  · -- the old marks
    have hqT : bridge 1 z q.1.2 ⊆ sitesOf T :=
      ysite_subset_sitesOf NS.Z.hN NS.Lab (NS.y0 (Sum.inr q)) hq
    obtain ⟨hYm, hYag⟩ := hsub (Y := q.1.2) ((subset_bridge z q.1.2).trans hqT)
    refine oldMarkGBg_congr_of_terms S Gl (BgTransport.canon S.G' Gl N)
      (maskPre S.hG' Gl (S.blockU z)) NS.O.X₁f NS.O.m₀ NS.O.jL NS.O.𝒦X F₁L' SolL' _ NS.O.ρ
      NS.hp corrU eps' z hθ hθ' q ht₀ Φ Φ (fun um hum w hw => ?_) (s : ℂ)
    have hW : (‖um‖ + ‖w‖) *
        markedRad d L N k S.a₁ NS.O.κ cψL ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < NS.O.δ₁ :=
      mul_lt_of_le_of_mul_lt (by linarith) hRt hCL.δ₁_pos (by positivity)
    exact holdloc q.1.1 um w hW q.1.2 hYm (θb.1, S.hatOf 1 NS.O.ρ NS.hp Φ) ⟨hθ, hboxL Φ⟩
      (θb'.1, S.hatOf 1 NS.O.ρ NS.hp Φ) ⟨hθ', hboxL Φ⟩ ⟨hYag, fun _ _ _ => rfl⟩

end NewLevelSystem

end Balaban.Inhabited
