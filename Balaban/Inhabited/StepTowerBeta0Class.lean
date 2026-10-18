/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityValTower
public import Balaban.Inhabited.StepTowerBeta0Amp
public import Balaban.Inhabited.StepTowerBeta0Marks
import Mathlib.Tactic.Linarith

/-!
The class chain at the base: the coefficient family of the new energy density of a general class at every tower radius

`e0CoeffFamily_class_fromTower_agree`: the statement of `e0CoeffFamily_class_fromTower` for all
towers that agree with a reference tower `T₀` on `m₁, BG, BG₂, κ, δ` and every radius
`t ≥ c 3^{-α(k+1)}` (`2 α < 1`), beyond one threshold `β₀`.  The threshold of the proof is that of
`exists_beta0_e1_agree`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit

open Classical in
/-- The class chain at the base: the coefficient family of the new energy density of a general class at every tower radius -/
theorem e0CoeffFamily_class_fromTower_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (Dt : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (hS : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
          Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
          Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
      ∀ (Jr : S.JointRep T.t (2 * p₁)) (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (z : RootIdx 3 3 N₁ T.m₁ (k + 1)) (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb)
        (εH κH Kc : ℝ)
        (A : physParam 2 S → ℂ →
          LabelAct (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS))
            (S.blockSplit 1 hp).Ωb εH κH T.κ0 Kc)
        (ι₁ : Type) [Fintype ι₁] (y1 : ι₁ → Lb ⊕ RootUnionLb 1 (fun _ => Set.univ) (e1Dom S))
        (G₁ : physParam 2 S → ι₁ → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ) (F1 : ι₁ → ℝ),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- (M1) the activity family of the class
      (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
        (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
        (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) →
      (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
        ContinuousOn ((A θ u).H y) (physCarrier S 1 hp)) →
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
        DifferentiableOn ℂ (fun u => (A θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) →
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
          physRestrict (sitesOf T') (physIncl 2 S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
          (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite y ⊆
            Yhat Set.univ (sitesOf T') →
          (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y) →
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          Jr.W1 C (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
            ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) →
      -- (M2) the marks of the inherited energy
      (∀ θ j u, Measurable (G₁ θ j u)) →
      (∀ θ j u, DepOn (blocksOf 1 (k + 1) Set.univ
        ((commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
          (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite (y1 j))) (G₁ θ j u)) →
      (∀ θ j u Φ, ‖G₁ θ j u Φ‖ ≤ F1 j * Real.exp (-(2 * T.κdec - 1) *
        (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
          (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).dl (y1 j))) →
      (∀ j, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
        (fun r : physParam 2 S × ℂ => G₁ r.1 j r.2 Φ)
        (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) →
      (∀ j, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
        ContinuousOn (G₁ θ j u) (physCarrier S 1 hp)) →
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ j Φ,
        DifferentiableOn ℂ (fun u => G₁ θ j u Φ) (Metric.ball (0 : ℂ) corrU)) →
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
          physRestrict (sitesOf T') (physIncl 2 S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j,
          (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite (y1 j) ⊆
            Yhat Set.univ (sitesOf T') →
          G₁ θ j (s : ℂ) = G₁ θ' j (s : ℂ)) →
      (∀ j, rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
        ((commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
          (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite (y1 j))) →
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          (fderiv ℂ (fun w : S.EC => Jr.EJ C (rawOf D, w)) ((s : ℂ) • Balaban.Fluctuation.yhat x))
              ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ Balaban.Fluctuation.yhat x)) =
            ∑ j, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) j (s : ℂ)
              ((S.blockSplit 1 hp).restr x)) →
      -- the constants of the class activity and of the inherited marks
      (∀ j, 0 < F1 j) → 0 < εH → K0 3 3 T.κ0 + 1 ≤ Kc → κH ≤ 2 * T.κdec - 1 →
      T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ κH →
      εH ≤ 1 / (8 * Kc ^ 3 * c1 3 3 *
        Real.exp ((κH - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) →
      ∃ c e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
        (∀ θ T', c θ T' = gsumCoeff (S.blockSplit 1 hp).μ
          (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)) (A θ)
          (Sum.elim (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z) y1)
          (Sum.elim (fun i u Φ => e1MarkGParam S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u Φ) (G₁ θ)) T') ∧
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          (AnalyticOnNhd ℂ (fun θ => c θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                physRestrict (sitesOf T') (physIncl 2 S θ') → c θ T' = c θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖c θ T'‖ ≤
              CPE 3 3 Kc κH T.κ0 T.κ' *
                ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
                    corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                  ∑ j, F1 j * Real.exp (-T.κ0 *
                    (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                      (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).dl (y1 j))) *
                Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, c θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T') ∧
              dExt T' = sizeJ 1 (k + 1) (sitesOf T'))) ∧
          (AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
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
                CPE 3 3 Kc κH T.κ0 T.κ' *
                  ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
                      corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                    ∑ j, F1 j * Real.exp (-T.κ0 *
                      (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                        (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).dl (y1 j))) *
                  Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E1locJ C z (rawOf D) = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E1locH C z = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, H1⟩ := exists_beta0_e1_agree T₀ hA p hcR hαR 3
  refine ⟨β₀, (le_max_left _ _).trans hβ₀, fun T hm₁ hBG hBG₂ hκ _ => ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp₁ Dt S hS hp
  subst hS
  have hp0 : 0 < p₁ := hp
  have hβ3 : 3 ≤ β := ((le_max_left _ _).trans hβ₀).trans hβ
  have hβpos : 0 < β := by linarith
  have hRU := (H1 T hm₁ hBG hBG₂ hκ).1 k hk β hβ hct p₁ hp0 hp₁
  obtain ⟨F₁, Sol, hF⟩ := e1MarkParam_pairs_fromTower T Dt h3N hN hν0.le hν hβpos hp hRU
  refine ⟨F₁, Sol, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A ι₁ _ y1 G₁ F1 hE hAhol hAcont hAdiff hAloc hW hG1meas
    hG1dep hG1bd hG1hol hG1cont hG1diff hG1loc hroot₁ hF₁ hF1 hεpos hKc hκG hκ hε
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hP, hne, hmeas, hdb, hhol, hcont, hspec⟩ := hF z
  obtain ⟨hdep0, hbd0⟩ := hdb Lb Lab
  have hopen : IsOpen (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
      (T.step k hk N₁ ν β p₁).ν T.t) :=
    isOpen_physV _ _ _ _ (bgHyp_lv (k := k) T.m₁ hν0.le hν)
  have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ Metric.ball (0 : ℂ) corrU := by
    intro s hs
    rw [mem_ball_zero_iff]
    refine norm_ofReal_lt_of_mem hs ?_
    unfold corrU
    norm_num
  have hfam := paramMarkFamily_sum_elim ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
    (A := A) (y0 := commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z)
    (y1 := y1)
    (G₀ := fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) (G₁ := G₁)
    (F0 := fun _ => corrF0 T k β p₁) (F1 := F1) hopen Metric.isOpen_ball hseg
    (isCompact_physCarrier _ 1 hp) (measurableSet_physCarrier _ 1 hp)
    (ae_mem_physCarrier _ 1 hp) hAhol hAcont hmeas hbd0 (fun i Φ _ => hhol i Φ) hcont
    hG1meas hG1bd hG1hol hG1cont
  have hholG₀ : ∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
      (T.step k hk N₁ ν β p₁).ν T.t, ∀ i Φ, DifferentiableOn ℂ
      (fun u => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) (Metric.ball (0 : ℂ) corrU) := by
    intro θ hθ i Φ u hu
    have ha := (hhol i Φ (θ, u) ⟨hθ, hu⟩).differentiableAt
    have hpr : DifferentiableAt ℂ (fun v : ℂ => (θ, v)) u :=
      DifferentiableAt.prodMk (differentiableAt_const θ) differentiableAt_id
    exact (ha.comp u hpr).differentiableWithinAt
  have hlt : (T.step k hk N₁ ν β p₁).p₁ < 2 * p₁ := by
    change p₁ < 2 * p₁
    linarith
  have hroot₀ : ∀ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
      (e1Dom (T.step k hk N₁ ν β p₁)) z},
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ
        ((commonLabels Lab hN1 (by norm_num) (fun _ => Set.univ)
          (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T Dt)).ysite
          (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)) :=
    fun i => (bridgeFamily_spec hN1 (by norm_num) (e1Dom_isDj T Dt) z i.2).2.1
  obtain ⟨hcl, hval⟩ := StepSetting.JointRep.classE1Family_of_marks Jr C hp hlt.le
    (commonLabels Lab hN1 (by norm_num) (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁))
      (e1Dom_isDj T Dt)) hN1 hne
    (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z) y1
    (fun _ => corrF0 T k β p₁) F1 A
    (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
      (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) G₁ hfam hdep0 hG1dep hAdiff hholG₀ hG1diff
    T.marks_hκ0 hKc hεpos (fun _ => corrF0_pos T hk hβpos hp0) hF1 T.marks_hκ' hκG hκ hε z
    hroot₀ hroot₁ hAloc
    (fun T' => e1Mark_hG_rawY_fromTower T Dt hN hν0.le hν hβpos hp hRU F₁ Sol z hspec Lab hN1 T')
    hG1loc hE hW
    (fun D hX s hs x hx => e1_param_marks_eq_raw_deriv T Dt _ rfl Jr hp hlt
      (fun b => F₁ (z, b)) (fun b => Sol (z, b)) z hP D hX s hs x hx)
    hF₁
  obtain ⟨E, -⟩ := (detExpansionLocC_scale_fromTower T k hk N₁ h3N hN hν0.le hν β p₁).1 z
  obtain ⟨dz, hdz1, hdz2⟩ := detParamFamily (N := 2) E (bgHyp_lv (k := k) T.m₁ hν0.le hν)
  let c : physParam 2 (T.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
      (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ := fun θ T' =>
    gsumCoeff ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
      (commonLabels Lab hN1 (by norm_num) (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁))
        (e1Dom_isDj T Dt)) (A θ)
      (Sum.elim (commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z) y1)
      (Sum.elim (fun i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
        (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) (G₁ θ)) T'
  have hβS : 0 < (T.step k hk N₁ ν β p₁).β := hβpos
  have hval0 : ∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
      XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
        (k + 1) 1 T.t D →
      Jr.E0locJ C z (rawOf D) =
        ∑ T', (dz ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' +
          c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T') := by
    intro D hX
    have hroot : Jr.rootTraceJ z (rawOf D) =
        ∑ T', dz ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' := by
      unfold StepSetting.JointRep.rootTraceJ
      rw [Jr.F₀_eq D hX, E.sum_eq D hX]
      exact Finset.sum_congr rfl fun T' _ => (hdz1 D hX _ T').symm
    unfold StepSetting.JointRep.E0locJ
    rw [hroot, hval D hX, Finset.sum_add_distrib]
  refine ⟨c, fun θ T' => dz θ T' + c θ T', fun θ T' => rfl, fun T' => ⟨?_, ?_⟩,
    fun D hX => ?_, fun ε hε q hq => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hcl T'
    exact ⟨h1, h2, h3, h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hcl T'
    refine ⟨(hdz2 T').1.add h1, fun θ hθ θ' hθ' h => ?_, fun θ hθ =>
      (norm_add_le _ _).trans (add_le_add ((hdz2 T').2.2.1 θ hθ) (h3 θ hθ)), fun θ hθ => ?_⟩
    · have hsub : sitesOf T' ⊆ thickSet (T.step k hk N₁ ν β p₁).G'
          (Yhat Set.univ (sitesOf T')) :=
        fun x hx => Or.inl (by rw [Yhat_univ]; exact hx)
      have h' : physRestrict (N := 2) (sitesOf T') (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
          physRestrict (sitesOf T') (physIncl 2 (T.step k hk N₁ ν β p₁) θ') :=
        funext fun x => congrFun h ⟨x.1, hsub x.2⟩
      exact congrArg₂ (· + ·) ((hdz2 T').2.1 θ hθ θ' hθ' h) (h2 θ hθ θ' hθ' h')
    · by_cases h0 : dz θ T' = 0
      · have hc0 : c θ T' ≠ 0 := by
          intro h1'
          exact hθ (show dz θ T' + c θ T' = 0 by rw [h0, h1', add_zero])
        exact ⟨(h4 θ hc0).1, (h4 θ hc0).2.1⟩
      · exact (hdz2 T').2.2.2 θ h0
  · have hE1 := hval D hX
    have hE1H : ((T.step k hk N₁ ν β p₁).withDatumH D).E1locH C z =
        ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' := by
      rw [← Jr.E1locJ_datum C ((T.step k hk N₁ ν β p₁).withDatumH D) hX Dt.core T.large_block
        T.dom_margin T.coer_margin T.δc_small hβS hp hlt.le (hE D hX) z]
      exact hE1
    refine ⟨hE1, hE1H, hval0 D hX, ?_⟩
    rw [← Jr.E0locJ_datum C ((T.step k hk N₁ ν β p₁).withDatumH D) hX Dt.core T.large_block
      T.dom_margin T.coer_margin T.δc_small hβS hp hlt.le (hE D hX) z]
    exact hval0 D hX
  · exact Jr.densE0_rootSite_eq_sum_of_root C z (fun θ T' => dz θ T' + c θ T') hval0 hε hq

end Balaban.Inhabited
