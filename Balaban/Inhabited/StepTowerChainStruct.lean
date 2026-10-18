/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelBase
public import Balaban.Inhabited.StepTowerSmall
public import Balaban.Inhabited.StepTowerChainStructAmp
public import Balaban.Inhabited.MarkedFamilyFromTower
public import Balaban.Inhabited.MarkCorrBudget
public import Balaban.Fluctuation.MarkedCommonLabels
public import Balaban.Inhabited.MarksNumericsFromTower

/-!
# The class chain at a tower with the structural premises discharged

`e0CoeffFamily_class_exists_tower_struct`: the conclusion of
`e0CoeffFamily_class_exists_tower_base` without the premises produced by landed theorems of the
step and the tower:

* the scale record `StepScaleData` (`StepTower.scale`), `0 < S.p₁`, the cutoff `c_ψ = p₁` and the source radius `ρ = p₁` (so `ρ ≤ c_ψ`, `ρ < 2 p₁`,
  `S.p₁ ≤ ρ`);
* `HatConn`, `RowInHat` of the step (`StepTower.hatConn_step`, `StepTower.rowInHat_step`);
* the maps `F₁L`, `SolL`, `FkL` with analyticity and defining properties
  (`i4b_analytic`, `Dec2.i4a_analytic`, `theorem72_analytic`, from `StepScaleData.core` and the
  `BgSetting` of the base theorem);
* the marked radius: `bb = corrR`, `0 < markedRad`, `2 U markedRad < T.t`,
  `(U + bb) markedRad < T.t` (`corrR_pos`, `two_corrR_mul_decMR_lt`, `exists_beta0_corrR`);
* the maps `G₁`, `H`, the finite set `𝒴C` and the constant `εC` (definitions of the proof);
* the first entry of the numerical condition of the composed activity
  (`StepTower.exists_beta0_amp`, with `β₀` enlarged).

Left as premises (see `notes/phase1/WIDEGEN.md`, W998): the class data, `hdom`, the chart
condition `hchart`, the per-label bounds of the irrelevant parts with their constants, the
analyticity of the old densities along the path, and the smallness of the class constants against
the marked radius.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The coefficient family of the class chain at a tower with the numerical premises
discharged.**  See the module doc-string. -/
theorem e0CoeffFamily_class_exists_tower_struct (m₀ : ℕ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ (κmin : ℝ) (_ : stepHullMin ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ), ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ T.m₁ (k + 1) × Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ T.m₁ (k + 1) 2 (rhoSep T.m₁)}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1)
            (rhoSep T.m₁), (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld 3 3 N₁ T.m₁ (k + 1) 2, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock 3 3 (N₁ * 3 ^ T.m₁) (k + 1) j x = jBlock 3 3 (N₁ * 3 ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide 3 C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => 3 / 2 * cellSide 3 C.m₀ T.m₁ τ.1.1) (3 * cellSide 3 C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : C.m₀ = m₀),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ 324 T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ T.t δfl (X₁f τ)) ∧
        ∀
        -- the chart of the label generators lies in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν τ.1.1 bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the smallness of the class constants against the marked radius
      (corrU / (T.t / (2 * markedRad 3 3 2 k S.a₁ T.κ p₁
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 T.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤
          1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
            rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
            Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3))) →
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := 2) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                (physIncl 2 S θ) =
              physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl 2 S θ') →
            e θ T' = e θ' T') ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
            27 * covBLogMax 3 3 T.κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) *
                Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                  dExt T') +
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  classical
  obtain ⟨κmin, hlo, T, δ₃, δfl, κdec, hnB, hnF, hκ, hr⟩ :=
    exists_stepTower_base_rate m₀ stepHullMin
  obtain ⟨βc, hRU⟩ := exists_beta0_corrR T hA p
  have hK0 := T.marks_K0_pos
  have hrU : 0 ≤ rootUnionK 3 3 1 T.m₁ T.κ0 := rootUnionK_nonneg 1 T.κ0
  obtain ⟨βa, -, Hamp⟩ := T.exists_beta0_amp hA p
    (Kc' := (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
      rootUnionK 3 3 1 T.m₁ T.κ0) / 2) (by linarith)
  obtain ⟨βray, -, Hscale⟩ := T.scale hA p
  obtain ⟨βb, hβb, HC⟩ := e0CoeffFamily_class_fromTower_of_irrelBounds_base T hlo hA p
  refine ⟨κmin, hlo, T, δ₃, δfl, κdec, max (max (max βb βc) βa) βray,
    hβb.trans (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)), ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ S hS
  obtain ⟨⟨⟨hβb', hβc'⟩, hβa'⟩, hβr'⟩ : ((βb ≤ β ∧ βc ≤ β) ∧ βa ≤ β) ∧ βray ≤ β := by
    simpa only [max_le_iff] using hβ
  obtain ⟨Dt⟩ := Hscale k hk N₁ h3N hN₁ ν hν0.le hν β hβr' p₁ hp0 hp₁
  subst hS
  have hp : 0 < (T.step k hk N₁ ν β p₁).p₁ := hp0
  obtain ⟨Jr, HC'⟩ := HC k hk N₁ h3N hN₁ ν hν0 hν β hβb' p₁ hp0 hp₁ Dt _ rfl hp
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom bL hb₁ hbC hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hCm
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, HG⟩ := @HC' C z 𝒯E h𝒯 P Dom δ₃ δfl bL hb₁ hbC hm hcl
    hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hnB hnF
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hE hεnum
  have hC := Dt.core
  have hd0 : 0 < 3 := by norm_num
  have ht0 := T.t_pos
  have hc1 := one_le_c1 3 3
  have hβ0 : 0 < β := by linarith
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hδ0 : 0 < xiC1 3 * T.t := by have := hC.eps_pos; have := one_le_xiC1 3; positivity
  have hB0 : 0 ≤ 2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := 2) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  have hFk : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ Fk : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
      ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ),
      AnalyticOnNhd ℂ Fk {p | ∃ D : BgData (Gk τ) 2,
        InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) (T.step k hk N₁ ν β p₁).ν D ∧
          p = (D.Ψ, D.h)} ∧
      ∀ D : BgData (Gk τ) 2,
        InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) (T.step k hk N₁ ν β p₁).ν D →
        Fk (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
          (T.step k hk N₁ ν β p₁).ν (bgC0 3 3 2) D,
          bgMultC (Gk τ) (compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
            (T.step k hk N₁ ν β p₁).ν (bgC0 3 3 2) D) :=
    fun τ => theorem72_analytic (G := Gk τ) (a := compWeight 3 (T.step k hk N₁ ν β p₁).a₁)
      (ν := (T.step k hk N₁ ν β p₁).ν) (hBs τ).HBk
  choose FkL hFkan hFkeq using hFk
  have hRU' := hRU k hk β hβc' p₁ hp0 hp₁
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * 3 ^ k := hatStepK_betaU k T.m₁ hk ν β p₁ T.δ
  have hmrEq : markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) = decMR T k (β * 3 ^ k) p₁ := by
    rw [hbU]; exact markedRad_eq T k hb0.le p₁
  obtain ⟨hRpos, hdec, hsa0, hab0⟩ := T.marked_numerics hk hb0 hp0 hRU'
  have hU := corrU_pos
  have hmr0 : 0 < markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) := by rw [hmrEq]; exact hdec
  have hsa : 2 * corrU * markedRad 3 3 2 k (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) < T.t := by
    rw [hmrEq]; exact hsa0
  have hab : (corrU + corrR T k (β * 3 ^ k) p₁) * markedRad 3 3 2 k
      (T.step k hk N₁ ν β p₁).a₁ T.κ p₁
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) < T.t := by
    rw [hmrEq]; exact hab0
  have hfirst := Hamp k hk β hβa' p₁ hp0 hp₁
  rw [show 2 * ((2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
    rootUnionK 3 3 1 T.m₁ T.κ0) / 2) = 2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 +
    rootUnionK 3 3 1 T.m₁ T.κ0) + rootUnionK 3 3 1 T.m₁ T.κ0 by ring] at hfirst
  have hεex : ∃ εC : ℝ, εC = corrU / (T.t / (2 * markedRad 3 3 2 k
      (T.step k hk N₁ ν β p₁).a₁ T.κ p₁ ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 T.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) := ⟨_, rfl⟩
  obtain ⟨εC, hεCdef⟩ := hεex
  have hεC0 : 0 ≤ εC := by
    rw [hεCdef]; exact epsC_nonneg hmr0 ht0 hE₀ hCI hKL hα₃ T.marks_K0_pos
  exact @HG p₁ hp0.le (StepTower.hatConn_step T hk) (StepTower.rowInHat_step T hk hN₁ hν0.le hν)
    κdec hκ hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL (by rw [hCm]; exact hr)
    (fun _ => F₁) (fun _ => hF₁an) (fun _ => hF₁) (fun _ => Sol) (fun _ => hSolan)
    (fun _ => hSolprop) FkL hFkan hFkeq p₁ hp0 le_rfl (by linarith) (corrR T k (β * 3 ^ k) p₁)
    hRpos hab _ (fun _ _ _ _ => rfl) le_rfl _ rfl _ (fun _ _ _ _ => rfl) εC hεC0 hmr0 hsa
    hεCdef.ge hE (max_le hfirst (by rw [← hεCdef] at hεnum; exact hεnum))
