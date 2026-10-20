/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelZeroSourceBgCanon
public import Balaban.Inhabited.E1MarkParamCommonG
public import Balaban.Inhabited.DecMarkCorrFamilyFromTower

/-!
# The fields of the bridge marks recomputed on a background generating set

P3 pp. 78-79 and Lemma 4.2 at `Gb` for the marks of the bridge labels of the energy record
recomputed on a background generating set `Gb` with the canonical transport (route R-LOC, L4-3;
R8-AUDIT D2: per label inside the top layer).

* `blockEvBg_canon_R8`: for the block energy of one block, the four hypotheses of the R8 field
  lemmas at `Gg = Gb` (`decMarkCorrBg_fields_of_gen`): the locality `hloc`
  (`evDecBg_canon_local_blockEnergy`), the Cauchy estimate `hcau` with the bound
  `E_sc e^{-2 κ_dec d̃(Y)} / t₀`, and the analyticity statements `hJ2`, `hJ4`
  (`evDecBg_canon_fields`) for the labels with the margin; when the frozen region of the block
  leaves the top layer, the terms of these labels vanish (`evDecBg_eq_zero_of_not_top`);
* `e1MarkGParamGBgOn_canon_fields`: for a bridge label with the margin, the mark of the label on
  `Gb` is measurable, local in the blocks of the label on `physVBg Gb`, bounded by
  `F₀ e^{-(2 κ_dec - 1) d(Y′)}`, analytic on `physVBg Gb × {‖u‖ < 17/16}` and continuous in the
  configuration (`e1MarkGParamGBgOn_fields_label` with the rooted outputs on the labels with the
  margin: `markedOutDecCorrBg_fields_of_gen`, `corrected_markedOutDecBg_bound_on`,
  `continuous_markedOutDec_decMarkCorrTermBg_on`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.LargeField Balaban.Polymer Finset Metric

section R8

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {Kc Cx : ℝ}

/-- **The hypotheses of the R8 field lemmas at `Gb` for the block energy of one block.**  For a
block `z` whose block sites lie in the frozen region `X₁` of its expansion, with the read sites in
`X₁` and the block margin for the step, and for the decoupling pairs `F₁`, `Sol` of `(Gb, H⁻)` pinned
and analytic: the terms `evDecBg … Y` of the block energy recomputed on `Gb` with the canonical
transport satisfy, for every label `Y` with `LabelMargin Gb Y`, the locality `hloc`, the Cauchy
estimate with the bound `E_sc e^{-2 κ_dec d̃(Y)} / t₀` (`E_sc` the scale-uniform block-energy
majorant), and the analyticity statements `hJ2`, `hJ4` on the chart of `Gb`. -/
theorem blockEvBg_canon_R8 (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {c₂ δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hBG₂ : 0 ≤ BG₂) (hPmp : Precedes Hm Gb)
    (hHm : Hm.Ω (k + 1) = ∅)
    (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Hm.Ω k = Gb.Ω k) (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L S.a₁) S.ν)
    (hMX' : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hBM : BlockMargin S.G' X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hzX : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X₁f) (Zb : Finset (unitPts Gb)) :
    (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir S.hG' Y u u' →
        evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
            (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y
            (u.1, (BgTransport.canon S.G' Gb N).res u.2) =
          evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
            (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y
            (u'.1, (BgTransport.canon S.G' Gb N).res u'.2)) ∧
    (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, LabelMargin Gb Y → ∀ u ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
          (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um t Y
          (u.1, (BgTransport.canon S.G' Gb N).res u.2)) 0‖ ≤
        energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ) * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) / t₀) ∧
    (∀ Y, LabelMargin Gb Y → AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
            (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb p.2.1 p.2.2 Y
            (p.1.1, (BgTransport.canon S.G' Gb N).res p.1.2))
        ((XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁})) ∧
    (∀ Y, LabelMargin Gb Y → ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b →
        (a + b) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ => deriv (fun t : ℂ =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
            ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
            (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
              (BgTransport.canon S.G' Gb N).res ψh)) 0)
          (physVBg N Gb S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  have hEb0 := energyBdScaled_nonneg_of (N := N) HBb S.hk1 (Nat.le_succ k) hS.fam.2.1 hBG₂ hδ₁0
    (κ := κ)
  refine ⟨evDecBg_canon_local_blockEnergy hC S.hk1 S.hG' hHm hHmtop hrow _ hcψ hMX' hmarD hαD hsm
    hcov hX₁ (fun s D hs hD φ α hI => hF₁ s D hs hD φ α ((dec2_isDecBg_iff Gb _ _ _ s D φ α).2 hI))
    hSol z hZ hBM Zb, ?_⟩
  by_cases htop : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1)
  · obtain ⟨hcau, hJ2, hJ4⟩ := evDecBg_canon_fields S S.hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps
      hsmall hc7 hphi hmarD hαD hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hδ₁0 hPmp hHm hF₁an
      hF₁ hSolan hSol hcov hX₁ hopt hκ₀ hκdec hκκ h1 hlog hEb0 (X₁g := X₁f) (fun x hx => hx) htop
      (Φ := blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z)
      ((blockEnergyFun_analytic (compWeight L S.a₁) S.ν k z).mono (Set.subset_univ _))
      (fun t ht => by
        rw [hΔ, mul_zero, Real.exp_zero, mul_one]
        exact blockEnergyFun_bound_scaled_of_block HBb hS.fam.2.1 hBG₂ hδ₁0 S.hk1 le_rfl z
          (fun x hx => blockLayers_of_top S.hk1 hdk hHm (htop x (hzX x hx))) ht.1)
      Zb
    refine ⟨fun a b t₀ ha hb ht htb hab um hum Y _ u hu =>
      (hcau a b t₀ ha hb ht htb hab um hum Y u hu).trans_eq ?_, fun Y _ => hJ2 Y,
      fun Y _ => hJ4 Y⟩
    rw [hΔ]
    ring_nf
  · have h0 : ∀ Y, LabelMargin Gb Y → ∀ (um tm : ℂ)
        (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gb × Fin N → ℂ)),
        evDecBg S.G' X₁f m₀ j 𝒦X Gb S.a₁ S.ν (BgTransport.canon S.G' Gb N)
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Sol
          (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) Zb um tm Y u = 0 :=
      fun Y hY um tm u => evDecBg_eq_zero_of_not_top _ hX₁ htop hY _ F₁ Sol _ Zb um tm u
    refine ⟨fun _ _ _ _ _ ht _ _ _ _ Y hY _ _ => ?_, fun Y hY p _ => ?_,
      fun Y hY _ _ _ _ _ _ _ p _ => ?_⟩
    · simp only [h0 Y hY, deriv_const, norm_zero]
      exact div_nonneg (mul_nonneg hEb0 (Real.exp_pos _).le) ht.le
    · simp only [h0 Y hY]
      exact analyticAt_const
    · simp only [h0 Y hY, deriv_const]
      exact analyticAt_const

end R8

section Bridge

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {Kc Cx : ℝ}

/-- `LabelMargin Gb` is inherited by subsets. -/
theorem labelMargin_of_subset {Y Y' : Set (CTorus d L N₁ m₁ (k + 1))} (h : Y ⊆ Y')
    (hm : LabelMargin Gb Y') : LabelMargin Gb Y :=
  fun x hx => hm x (h hx)

open Classical in
/-- **The fields of the bridge marks recomputed on `Gb` with the canonical transport** (P3
pp. 78-79 and Lemma 4.2 at `Gb`; R8-AUDIT D2).  Let the block covers be those of the step
(`hcovV`, `hX₁V`, `hoptV`, `d^{cov,1}(X) = 0`, the read sites and the block sites in `X₁`, the block
margin for the step), the decoupling pairs `F₁ b`, `Sol b` of `(Gb, H⁻)` pinned and analytic, and the
radii `0 < R`, `(R + R) m_R < δ₁`, `2 U ≤ R`, `17/16 ≤ U`.  For a bridge label `Y′` of the root `z`
with `LabelMargin Gb Y′`, the mark `e1MarkGParamGBgOn … θ Y′ u` on `Gb` is measurable for every
parameter and mark, depends only on the blocks of `Y′` for `θ ∈ physVBg Gb`, is bounded by
`F₀ e^{-(2 κ_dec - 1) d(Y′)}` with
`F₀ = |β| 4 |E_sc| U² / R³ · c₁ M^d · n_Fibre e^{(2 κ_dec - 1) c_Br}`, is analytic on
`physVBg Gb × {‖u‖ < 17/16}`, and is continuous in the configuration for `θ ∈ physVBg Gb`,
`‖u‖ < 17/16`. -/
theorem e1MarkGParamGBgOn_canon_fields (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {c₂ δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hBG₂ : 0 ≤ BG₂) (hPmp : Precedes Hm Gb)
    (hHm : Hm.Ω (k + 1) = ∅)
    (hC : FlCore N Gb Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hdk : Hm.Ω k = Gb.Ω k) (hHmtop : ∀ y ∈ Gb.Ω (k + 1), y ∈ Hm.Ω 1)
    (hrow : RowInHat (coverOf Gb) Hm (compWeight L S.a₁) S.ν)
    (hMX' : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hd : 3 ≤ d) (hN : L ^ 1 ∣ N₁)
    (hcovV : ∀ b, CovSetup S.G' 1 k (LocalCover.cube 1 k (LocalCover.blockSite k b))
      (LocalCover.fam 1 (LocalCover.blockSite k b)))
    (hX₁V : ∀ b, (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)) :
      Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ LocalCover.cube 1 k (LocalCover.blockSite k b)) ∧
        MeetsOne 1 k (LocalCover.fam 1 (LocalCover.blockSite k b)) W₀ ∧
        bondCost (scaleW L 1 m₁ k) E₀ =
          treeLenCovOne 1 k (LocalCover.cube 1 k (LocalCover.blockSite k b)))
    (hΔV : ∀ b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      treeLenCovOne 1 k (LocalCover.cube 1 k (LocalCover.blockSite k b)) = 0)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(LocalCover.nbhdF 1 (LocalCover.blockSite k b)))
    (hBMV : ∀ b, BlockMargin S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b))
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hzXV : ∀ b, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k b,
      x ∈ LocalCover.nbhdF 1 (LocalCover.blockSite k b))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ 1) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκ1 : 1 ≤ 2 * κdec)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : ∀ b, AnalyticOnNhd ℂ (F₁ b) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData Gb N, InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ b (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : ∀ b, AnalyticOnNhd ℂ (Sol b) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ b (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small Hm (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (Zb : Finset (unitPts Gb)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {R U : ℝ} (hR : 0 < R)
    (hRR : (R + R) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hUR : 2 * U ≤ R) (hU : 17 / 16 ≤ U) (z : RootIdx d L N₁ m₁ (k + 1))
    (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
    (hYm : LabelMargin Gb i.1) :
    (∀ (θ : physParamBg N Gb) (u : ℂ),
      Measurable (e1MarkGParamGBgOn S Gb (BgTransport.canon S.G' Gb N) Zb F₁ Sol ρ hp z Gb eps
        θ i u)) ∧
    (∀ θ ∈ physVBg N Gb S.a₁ S.ν eps, ∀ u : ℂ,
      DepOn (blocksOf 1 (k + 1) Set.univ i.1)
        (e1MarkGParamGBgOn S Gb (BgTransport.canon S.G' Gb N) Zb F₁ Sol ρ hp z Gb eps θ i u)) ∧
    (∀ (θ : physParamBg N Gb) (u : ℂ) Φ,
      ‖e1MarkGParamGBgOn S Gb (BgTransport.canon S.G' Gb N) Zb F₁ Sol ρ hp z Gb eps θ i u Φ‖ ≤
        ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ * U ^ 2 / R ^ 3 *
          (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (k + 1) i.1)) ∧
    (∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
      AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ =>
          e1MarkGParamGBgOn S Gb (BgTransport.canon S.G' Gb N) Zb F₁ Sol ρ hp z Gb eps p.1 i p.2 Φ)
        (physVBg N Gb S.a₁ S.ν eps ×ˢ Metric.ball (0 : ℂ) (17 / 16 : ℝ))) ∧
    (∀ θ ∈ physVBg N Gb S.a₁ S.ν eps, ∀ u ∈ Metric.ball (0 : ℂ) (17 / 16 : ℝ),
        Continuous (e1MarkGParamGBgOn S Gb (BgTransport.canon S.G' Gb N) Zb F₁ Sol ρ hp z Gb eps
          θ i u)) := by
  have hR8 := fun b => blockEvBg_canon_R8 S ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps hsmall hc7 hphi
    hmarD hαD hsm hcψ hδ₁0 hBG₂ hPmp hHm hC hdk hHmtop hrow hMX' (hcovV b) (hX₁V b) (hoptV b)
    (hΔV b) hκ₀ hκdec hκκ h1 hlog (hF₁an b) (hF₁ b) (hSolan b) (hSol b) b (hZV b) (hBMV b)
    (hzXV b) Zb
  have hfld := fun b => decMarkCorrBg_fields_of_gen (Gg := Gb) S (hR8 b).1 (hR8 b).2.1
    (hR8 b).2.2.1 (hR8 b).2.2.2 hρ hρc hp hδ₁0
  have hrad : ∀ um : ℂ, ‖um‖ < (17 / 16 : ℝ) → (‖um‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := fun um hum =>
    mem_markedRadiusSet_of_pos hδ₁0 hRR (show ‖um‖ ≤ R by linarith) (by simpa using hR.le)
  obtain ⟨hmeasO, hdepO, hholO⟩ := markedOutDecCorrBg_fields_of_gen S Gb S.hG' hd hN hcovV hoptV
    z F₁ Sol hp (S.β : ℂ) (LabelMargin Gb) (fun _ _ h hm => labelMargin_of_subset h hm)
    (fun b Y Y' hY hYY' hY' Θ hΘ um hum => (hfld b).1 Y Y' hY hYY' hY' Θ hΘ um hum)
    (fun b Y hY Θ hΘ um hum => ((hfld b).2.1 Y hY Θ hΘ um hum).2)
    (fun b Y hY Φ a b' ha hb' hab => (hfld b).2.2.2 Y hY Φ a b' ha hb' hab)
  have hF₀ : 0 ≤ ‖(S.β : ℂ)‖ * 4 * ‖energyBdScaled d L N (compWeight L S.a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ * U ^ 2 / R ^ 3 *
      (c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d) *
      ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    have hnF : (0 : ℝ) ≤ (nFibre d L : ℝ) := by unfold nFibre; positivity
    positivity
  exact e1MarkGParamGBgOn_fields_label S Gb (BgTransport.canon S.G' Gb N) Zb F₁ Sol ρ hp z Gb eps
    hF₀ (isOpen_physVBg Gb S.a₁ S.ν eps HBb) i
    (fun Θ hΘ um hum => hmeasO i.1 hYm Θ hΘ um (hrad um hum))
    (fun Θ hΘ um hum => hdepO i.1 i.2 hYm Θ hΘ um (hrad um hum))
    (fun Θ hΘ um hum Φ => corrected_markedOutDecBg_bound_on S S.hG' hd hcovV hX₁V hoptV hZV
      hκ1 z F₁ Sol hp (S.β : ℂ) Θ hR Φ (LabelMargin Gb)
      (fun _ _ h hm => labelMargin_of_subset h hm)
      (fun b Y hY => (hfld b).2.2.1 Y hY Θ hΘ R U hR hRR hUR um (by linarith) Φ) i.1 hYm)
    (fun Θ hΘ um hum => continuous_markedOutDec_decMarkCorrTermBg_on S F₁ Sol ρ hp (S.β : ℂ) Θ
      um z i.1 (LabelMargin Gb) (fun _ _ h hm => labelMargin_of_subset h hm) hYm
      (fun b Y hY => ((hfld b).2.1 Y hY Θ hΘ um (hrad um hum)).1))
    (fun Φ => (hholO i.1 hYm Φ R R hR hR hRR).mono
      (Set.prod_mono subset_rfl (Metric.ball_subset_ball (by linarith))))

end Bridge

end Balaban.Inhabited
