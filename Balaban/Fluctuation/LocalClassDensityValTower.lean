/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityValClass
public import Balaban.Inhabited.E1CoeffFamily
public import Balaban.Inhabited.E1LabelsBudget
public import Balaban.Inhabited.OffFibreE1Activity
import Mathlib.Tactic.Linarith

/-!
# The coefficient family of the new energy density of a general class at the tower

At a scale of the tower `T` (`d = L = 3`, `N = 2`), for a class member `C` of the step, the
Theorem 3.1 (a) expansion of `ℰ₀^{(k+1)}(z) = -½ Σ tr 𝕃 + ℰ₁^{(k+1)}(z)` at every datum of the
chart (any field) is assembled from:

* the landed parts, chosen before the class: the decoupling pairs `(F₁, Sol)` and the marks
  `e1MarkGParam` of the zero class (`e1MarkParam_pairs_fromTower`: measurable, block-local,
  bounded, analytic in `(θ, u)`, continuous on the carrier; `e1Mark_hG_rawY_fromTower`: local on
  `sitesOf T`; `e1_param_marks_eq_raw_deriv`: their sum is the localized derivative of `W₁^0` at
  every chart datum), and the determinant family (`detExpansionLocC_scale_fromTower`,
  `detParamFamily`: the PARAM-DET-LOCAL input, analytic, local on the thickening, bounded, rooted,
  summing to `-½ Σ tr 𝕃` at every chart datum; it does not depend on the class);
* two inputs of the class, which are hypotheses here: (M1) one activity family `A θ` on the common
  labels whose label sum is the class exponent `W₁^C(rawOf D, s ψ̂)` at every chart datum `D`, analytic
  in `(θ, u)`, continuous on the carrier, holomorphic in `u` and local on `sitesOf T`; (M2) one
  family of marks `G₁ θ` of the inherited energy whose sum is the localized derivative of `ℰ_k` at
  every chart datum, with the fields of `ParamMarkFamily`, block-local, local on `sitesOf T`, and
  with the root cube in every anchor label;
* the analyticity of the old densities `ℰ^{(j)}` at the composed pairs of the path (`hE`).

`e0CoeffFamily_class_fromTower`: from these, the coefficient family `c θ T` of `ℰ₁` (analytic,
sharp-local, bounded, rooted) and `e = d_z + c` of `ℰ₀` (analytic, local on the thickening,
bounded, rooted), with `E1locJ C z = ∑ c`, `E1locH C z = ∑ c`, `E0locJ C z = ∑ e`,
`E0locH C z = ∑ e` at every chart datum (any field), and the input `hval` of
`finsum_polysAt_eq_of_rootedSum` on the whole class domain: `densE0 (rootSite z) q = ∑_T e (q̄, 0) T`
for every pair `q` of `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ t`, `q̄` the cut-off of `q`
(`densE0_rootSite_eq_sum_of_root`).  For the zero class the inputs (M1), (M2) are the zero-source
activity and no inherited marks: `e0CoeffFamily_zeroClass_of_class_fromTower` discharges every
hypothesis of `e0CoeffFamily_class_fromTower` for the zero class (the landed zero-source activity
`zeroSourceActivity_common_fromTower`, its value at every chart datum
`e1_common_activity_freeDatum_of_directTerms`, its locality `commonAct_zeroSourceAct_hA_rawY`, and the
empty family of inherited marks), so the hypotheses are not contradictory.  For a class with
non-zero inherited terms neither family is constructed.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit

/-- The label domains of a step equal to the step of the tower are domains of the level `k + 1`. -/
theorem e1Dom_isDj_of_eq {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ}
    [NeZero N₁] {ν β p₁ : ℝ} (Dt : StepScaleData T k hk N₁ ν β p₁)
    {S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)} (hS : S = T.step k hk N₁ ν β p₁) :
    ∀ b, ∀ Y ∈ e1Dom S b, IsDj 1 (k + 1) Y := by
  subst hS
  exact e1Dom_isDj T Dt

open Classical in
/-- **The coefficient family of the new energy density of a general class at the tower**, from the
class activity family (M1) and the inherited-energy marks (M2).  See the module doc-string. -/
theorem e0CoeffFamily_class_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
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
  obtain ⟨β₀, hβ₀, hR, -⟩ := exists_beta0_e1 T hA p 3
  refine ⟨β₀, (le_max_left _ _).trans hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  subst hS
  have hp0 : 0 < p₁ := hp
  have hβ3 : 3 ≤ β := ((le_max_left _ _).trans hβ₀).trans hβ
  have hβpos : 0 < β := by linarith
  have hRU := hR k hk β hβ p₁ hp0 hp₁
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

/-- For the zero class the inherited energy `ℰ_k` vanishes identically. -/
theorem _root_.Balaban.Fluctuation.StepSetting.JointRep.EJ_zeroClass {d L N₁ m₁ k N : ℕ}
    [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ} {S : StepSetting d L N₁ m₁ k N ϱ}
    (Jr : S.JointRep eps pp) (q : RawData d L (N₁ * L ^ m₁) (k + 1) N × S.EC) :
    Jr.EJ (zeroClass d L N₁ m₁ k N ϱ) q = 0 := by
  unfold StepSetting.JointRep.EJ
  exact Finset.sum_eq_zero fun j _ => Edens_zero _ _ _ _

open Classical in
/-- **The hypotheses of `e0CoeffFamily_class_fromTower` are satisfiable: the zero class.**  With
the zero-source activity of `zeroSourceActivity_common_fromTower` as the class activity (M1) and the
empty family of inherited marks (M2), `e0CoeffFamily_class_fromTower` applies to the zero class:
beyond a threshold, for one joint representative `Jr` and every root `z`, there is a family `e`
analytic on `physV` with `E0locJ z = ∑_T e (rawOf D, 0) T` at every datum `D` of the chart. -/
theorem e0CoeffFamily_zeroClass_of_class_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ → 0 < (T.step k hk N₁ ν β p₁).p₁ →
      ∃ Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁),
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
      ∃ e : physParam 2 (T.step k hk N₁ ν β p₁) → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁)
          (m₁ := T.m₁) (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
        (∀ T', AnalyticOnNhd ℂ (fun θ => e θ T')
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)) ∧
        ∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
          XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
            (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D →
          Jr.E0locJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z (rawOf D) =
            ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' := by
  obtain ⟨β₁, h31, H1⟩ := e0CoeffFamily_class_fromTower T hA p
  obtain ⟨β₂, CE, CF, -, -, -, H2⟩ := zeroSourceActivity_common_fromTower T hHull hA p
  refine ⟨max β₁ β₂, h31.trans (le_max_left _ _), ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁ Dt hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨F₁, Sol, HC⟩ := H1 k hk N₁ h3N hN ν hν0 hν β ((le_max_left _ _).trans hβ) p₁ hp₁ Dt
    (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨Jr, val, I, hF, hεU, hval, hεpos, -, -, hε, A, hAeq, -, -, hcom⟩ :=
    H2 k hk N₁ h3N hN ν hν0 hν β ((le_max_right _ _).trans hβ) p₁ hp0 hp₁ 1 one_pos le_rfl Dt
      (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨A₀, hA0eq, hAhol, hAdiff, hAcont, hsum, -, -, -, -⟩ :=
    hcom (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T Dt)
  refine ⟨Jr, fun z => ?_⟩
  have hU2 : Metric.ball (0 : ℂ) corrU ⊆ Metric.ball (0 : ℂ) 2 :=
    Metric.ball_subset_ball (by unfold corrU; norm_num)
  have hW := fun D hX => e1_common_activity_freeDatum_of_directTerms T k hk N₁ h3N ν hν0 hν β
    p₁ hp0 Dt (T.step k hk N₁ ν β p₁) rfl hp Jr val hval I hF hεU A hAeq A₀ hsum D hX
  subst hA0eq
  subst hAeq
  have hAloc := fun T' => commonAct_zeroSourceAct_hA_rawY (T.step k hk N₁ ν β p₁) 1 _ hF hN1
    hp0 zero_le_two hεU T.κ0_ent T.marks_K0_le (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁))
    (e1Dom_isDj T Dt) (by norm_num) (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU))
    T.κ0_two one_pos T'
  obtain ⟨c, e, -, hprop, hvals, -⟩ := HC Jr (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z
    {Y // Y ∈ I.𝒴} (thickLabels I.𝒴 I.dom) _ (2 * T.κdec - 1) T.marksKc' _ Empty
    (fun j => j.elim) (fun _ j => j.elim) (fun j => j.elim)
    (fun D _ s _ x _ j _ => StepSetting.analyticAt_Edens_zeroClass j _)
    (fun y Φ _ => (hAhol y Φ).mono (Set.prod_mono (subset_refl _) hU2))
    (fun y θ hθ u hu => (hAcont y θ hθ u (hU2 hu)).continuousOn)
    (fun θ hθ y Φ => (hAdiff θ hθ y Φ).mono hU2) hAloc hW
    (fun _ j => j.elim) (fun _ j => j.elim) (fun _ j => j.elim) (fun j => j.elim)
    (fun j => j.elim) (fun _ _ j => j.elim) (fun _ _ _ _ _ _ _ _ j => j.elim)
    (fun j => j.elim)
    (fun D _ s _ => Filter.Eventually.of_forall fun x => by
      have h0 : (fun w => Jr.EJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (rawOf D, w)) =
          fun _ => 0 := funext fun w => Jr.EJ_zeroClass _
      rw [h0, fderiv_const_apply]
      simp)
    (fun j => j.elim) hεpos T.marks_hKc le_rfl T.marks_hκ (by unfold stepTheta at hε; exact hε)
  exact ⟨e, fun T' => (hprop T').2.1, fun D hX => (hvals D hX).2.2.1⟩

end Balaban.Inhabited
