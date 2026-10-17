/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActM1
public import Balaban.Fluctuation.LocalClassDensityFamilyTower
public import Balaban.Inhabited.ZeroSourceActivityCommon
public import Balaban.Inhabited.E1ParamRawLocal
public import Balaban.Inhabited.RootTermZeroClass
public import Balaban.Fluctuation.LocalClassDensityFamilyGenLabelAct

/-!
# A class with inherited labels at the tower, both families (`LocalClassDensityFamilyActTower`)

* `zeroSourceFamily_fields_fromTower`: the zero-source activity of the tower
  (`zeroSourceActivity_common_fromTower` at `q = 1`) as a family `A⁰` on its own labels with the
  fields (M1) of the zero class: analyticity, continuity and holomorphy from the common-label
  package, locality `commonAct_zeroSourceAct_hA_rawY`, and the label sum `W₁^0 = ∑ A⁰`
  (`e1_common_activity_freeDatum_of_directTerms`).
* `e0CoeffFamily_class_fromTower_of_families`: `e0CoeffFamily_class_fromTower_of_labels` with the
  input (M1) discharged as well.  The activity family of the class is
  `commonAct (A⁰.sum (commonAct A_C …))`, `A_C` the activity family of the inherited energy on the
  domains `𝒴C` of the class (`classE1_M1_of_family`); the label system is
  `Lab⁰ ⊕ (thickLabels 𝒴C ⊕ rootUnionLabels (polyDom …))`; the labels of the rooted pairs of (M2)
  are the bridges `bridge 1 z Y` among the root-union labels of the class domains, so `hy1` holds
  by definition.  The joint representative `Jr` is the one of the zero-source package.

Named hypotheses: the per-label settings, maps and numerics of the inherited labels (as in
`e0CoeffFamily_class_fromTower_of_labels`), the activities `H` by their formula (`hH`), the bound
condition `hnumH` of the activities (the per-label bound
`∑_{τ : Y ∈ polyDom τ} 2 E₀ e^{-κ₀ d(X_τ) - 2κ_dec d^cov_{C.m₀}(Y)}` is at most
`ε_C e^{-(2κ_dec^T - 1) d^cov_1(Y)}`), the analyticity `hE` of the old densities along the path,
and the smallness of the composed amplitude `max(ε⁰, ε_C)` against the composed entropy constant
`2(K₀ + 1) + (K₀ + K_ru) + K_ru` (the last hypothesis of `e0CoeffFamily_class_fromTower` in this
form).  Conclusion: the coefficient family `e` of `ℰ₀` (analytic, local on the thickening, bounded
by the determinant part plus `B e^{-κ′ d_Ω(T)}`, rooted), `E0locJ = ∑ e`, `E0locH = ∑ e` at every
chart datum, and `hval` on the class domain: `densE0 (rootSite z) q = ∑_T e(q̄, 0) T`.  The constant
`B` is the bound of `e0CoeffFamily_class_fromTower_of_labels` (`CPE` times the root and mark sums),
existentially quantified here together with the label system.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The zero-source activity of the tower as a family on its own labels, with the fields (M1) of
the zero class.**  From `zeroSourceActivity_common_fromTower` (at `q = 1`): beyond a threshold, for
every step of the tower there are a joint representative `Jr`, labels `Lab₀` of the block index
`1` and an activity family `A₀` on them (amplitude `ε⁰ = 2² · 2 β ε_η`, rate `2κ_dec - 1`,
entropy constant `2(K₀ + 1)`; `A₀` is the zero-source family `zeroSourceAct`) which is analytic in
`(θ, u)` on `physV × {‖u‖ < corrU}`, continuous on the carrier, holomorphic in `u`, local on
`sitesOf T` (`commonAct_zeroSourceAct_hA_rawY`), with `W₁^0(rawOf D, s ψ̂) = ∑ A₀` almost surely at
every chart datum (`e1_common_activity_freeDatum_of_directTerms`), and `ε⁰ > 0`. -/
theorem zeroSourceFamily_fields_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ → ∀ (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ (hp : 0 < S.p₁),
      ∃ (Jr : S.JointRep T.t (2 * p₁)) (Lb₀ : Type) (_ : Fintype Lb₀)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb₀)
        (A₀ : physParam 2 S → ℂ → LabelAct Lab₀ (S.blockSplit 1 hp).Ωb
          (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))))
          (2 * T.κdec - 1) T.κ0 (2 * (K0 3 3 T.κ0 + 1))),
        0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) ∧
        (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
          (fun r : physParam 2 S × ℂ => (A₀ r.1 r.2).H y Φ)
          (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
        (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
          ContinuousOn ((A₀ θ u).H y) (physCarrier S 1 hp)) ∧
        (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
          DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) ∧
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
            physRestrict (sitesOf T') (physIncl 2 S θ') →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab₀.ysite y ⊆ Yhat Set.univ (sitesOf T') →
            (A₀ θ (s : ℂ)).H y = (A₀ θ' (s : ℂ)).H y) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                ((S.blockSplit 1 hp).restr x)) := by
  classical
  obtain ⟨β₂, CE, CF, h3, -, -, H2⟩ := zeroSourceActivity_common_fromTower T hHull hA p
  refine ⟨β₂, h3, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨Jr, val, I, hF, hεU, hval, hεpos, -, -, -, A, hAeq, -, -, hcom⟩ :=
    H2 k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ 1 one_pos le_rfl Dt S hS hp
  obtain ⟨A0, hA0eq, hAhol, hAdiff, hAcont, -, -, -, -, -⟩ :=
    hcom (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)
  subst hA0eq
  have hU2 : Metric.ball (0 : ℂ) corrU ⊆ Metric.ball (0 : ℂ) 2 :=
    Metric.ball_subset_ball (by unfold corrU; norm_num)
  have hεzs : 0 ≤ 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β))) :=
    mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)
  exact ⟨Jr, {Y // Y ∈ I.𝒴}, inferInstance, thickLabels I.𝒴 I.dom, zeroSourceAct A 2 zero_le_two,
    hεpos,
    fun y Φ _ => (hAhol (Sum.inl y) Φ).mono (Set.prod_mono subset_rfl hU2),
    fun y θ hθ u hu => (hAcont (Sum.inl y) θ hθ u (hU2 hu)).continuousOn,
    fun θ hθ y Φ => (hAdiff θ hθ (Sum.inl y) Φ).mono hU2,
    fun T' θ hθ θ' hθ' hres s hs y hsub => by
      subst hAeq
      exact commonAct_zeroSourceAct_hA_rawY S 1 _ hF hN1 hp0 zero_le_two hεU T.κ0_ent
        T.marks_K0_le (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS) (by norm_num)
        hεzs T.κ0_two one_pos T' θ hθ θ' hθ' hres s hs (Sum.inl y) hsub,
    fun D hX => e1_common_activity_freeDatum_of_directTerms T k hk N₁ h3N ν hν0 hν β p₁ hp0 Dt
      S hS hp Jr val hval I hF hεU A hAeq (zeroSourceAct A 2 zero_le_two)
      (zeroSourceAct_total A 2 zero_le_two) D hX⟩

open Classical in
/-- **The tower core of the class chain with given activities.**  As
`e0CoeffFamily_class_fromTower_of_families_gen`, with the numerical condition `hnumH` replaced by
an activity family `AC` of the domains `𝒴C` (amplitude `ε_C`) which agrees with the activities `H`
on `physV` and is analytic, continuous, holomorphic and local there.  Both
`…_of_families_gen` and `…_of_families_red` supply `AC` from their `LabelAct` theorem. -/
theorem e0CoeffFamily_class_fromTower_of_families_core {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (ι : Type) [Fintype ι] {m₀ : ℕ} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (Eτ : ι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ) (Bτ : ι → ℝ)
        (_ : ∀ τ, 0 ≤ Bτ τ) (_ : 0 < S.β)
        (jL : ι → ℕ) (XL : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ, 1 ≤ jL τ) (_ : ∀ τ, jL τ ≤ k)
        (Gk : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (_ : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
          Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
        (X₀ X₁f : ι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (_ : ∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (_ : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (_ : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (_ : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
        (_ : ∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        (_ : ∀ τ, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 m₀ T.m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        (_ : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν (jL τ) bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl)))
        (_ : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν (jL τ) bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
        (F₁L : ι → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
            (rhoSep T.m₁)) 2,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (Dec2.decG (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2
              (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).1
              (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ,
              Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1
                  3 / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (_ : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
          (Gj τ))
        (_ : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (_ : R * δ₁ ≤ deltaStar 3 3 2) (_ : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (_ : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (_ : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        (_ : 3 ^ m₀ ∣ N₁) (_ : 1 ≤ m₀)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (_ : S.p₁ ≤ ρ)
        (_ : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
          Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
        (𝒴C : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
        (H : physParam 2 S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
        (_ : ∃ AC : physParam 2 S → ℂ → LabelAct
            (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj) (S.blockSplit 1 hp).Ωb εC
            (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0),
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u Y, (AC θ u).H Y = H θ Y u) ∧
          (∀ Y Φ, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (AC r.1 r.2).H Y Φ)
            (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
          (∀ Y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
            Continuous ((AC θ u).H Y)) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ Y Φ,
            DifferentiableOn ℂ (fun u => (AC θ u).H Y Φ) (Metric.ball (0 : ℂ) corrU)) ∧
          (∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)), ∀ θ ∈ physV S S.a₁ S.ν T.t,
            ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := 2) Z (physIncl 2 S θ) = physRestrict Z (physIncl 2 S θ') →
            ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C},
              Y.1 ⊆ Yhat Set.univ Z → (AC θ (s : ℂ)).H Y = (AC θ' (s : ℂ)).H Y)),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the numerical condition of the composed activity
      max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) εC ≤
        1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
          Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) →
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
  obtain ⟨β₁, h31, H1⟩ := e0CoeffFamily_class_fromTower_of_labels_gen T hA p
  obtain ⟨β₂, -, H2⟩ := zeroSourceFamily_fields_fromTower T hHull hA p
  refine ⟨max β₁ β₂, h31.trans (le_max_left _ _), ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨F₁, Sol, HC⟩ := H1 k hk N₁ h3N hN₁ ν hν0 hν β ((le_max_left _ _).trans hβ) p₁ hp₁ Dt
    S hS hp
  obtain ⟨Jr, Lb₀, _, Lab₀, A₀, hεpos, h0hol, h0cont, h0diff, h0loc, h0W⟩ :=
    H2 k hk N₁ h3N hN₁ ν hν0 hν β ((le_max_right _ _).trans hβ) p₁ hp0 hp₁ Dt S hS hp
  refine ⟨Jr, ?_⟩
  intro C z ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk
    Gj hlocE X₀ X₁f 𝒦X hB hFl cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀ hκ₀ hκdec
    hκ h1 hlog hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 R hR hsmR hRs
    hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ 𝒴C h𝒴 H hH εC hεC h𝒴dj hAct hE hεnum
  have hκ0' : aEnt 3 3 + 1 ≤ T.κ0 := by linarith [T.κ0_two]
  have ha1 : (1 : ℝ) < corrU := by norm_num [corrU]
  have hε : 0 ≤ max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ
      T.t (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) εC := hεpos.le.trans (le_max_left _ _)
  have hdomC : ∀ τ : ι, ∀ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ),
      IsDj 1 (k + 1) Y :=
    fun τ Y hY => polyDom_isDj_one S.hG' le_rfl hN hm1 (hcov τ) le_rfl (hopt τ) hY
  obtain ⟨AC, hAC, hhol, hcont, hdiff, hloc⟩ := hAct
  have hW := Jr.classActivityFamily_ae_W1_eq_gen C hb₁ hbC
    Eτ Bτ hBτ hβS
    jL XL hj1 hjk Gk Gj
    hlocE
    X₀ X₁f 𝒦X hB hFl hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd
    F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs hsmall hnum hnum' z hρ
    hρc hρpp hp ha1 hbb.le hab 𝒴C h𝒴 H hH hEJ hρp
  have hθ0 : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
        (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈ physV S S.a₁ S.ν T.t := fun D hD =>
    physVqRho_subset S S.a₁ S.ν T.t 1 1 (rawOf_source_mem_physVqRho S 1 T.t D hD 0 (by simp))
  obtain ⟨hM1hol, hM1cont, hM1diff, hM1loc, hM1W⟩ := Jr.classActivityFamily_sum_fields C hp A₀
    (fun θ u => commonAct AC hN1 (by norm_num) (fun _ => Set.univ)
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC hεC T.κ0_two θ u)
    (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS) hN1 (by norm_num) hε T.κ0_two
    h0hol
    (commonAct_holA_analytic AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two fun Y Φ _ => hhol Y Φ)
    h0cont
    (commonAct_contA AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two fun Y θ hθ u hu =>
      (hcont Y θ hθ u hu).continuousOn)
    h0diff
    (fun θ hθ => commonAct_holA_differentiableOn AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two θ
      fun Y Φ => hdiff θ hθ Y Φ)
    h0loc
    (fun T' θ hθ θ' hθ' hres s hs y hsub => by
      cases y with
      | inl Y => exact hloc (sitesOf T') θ hθ θ' hθ' hres s hs Y hsub
      | inr _ => rfl)
    h0W
    (fun D hD s hs => by
      filter_upwards [hW D hD s hs] with x hx
      rw [hx, commonAct_total AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two]
      simp only [hAC _ (hθ0 D hD)])
  -- the labels of the rooted pairs: the bridges among the root-union labels of the class domains
  have hbr : ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z},
      bridge 1 z q.1.2 ∈ bridgeFamily 1 (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z := fun q => by
    have hq : (q.1.1, q.1.2) ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z := q.2
    obtain ⟨h1', h2', h3'⟩ := mem_markedIdx.1 hq
    exact mem_bridgeFamily.2 ⟨q.1.1, q.1.2, h1', h2', h3', rfl⟩
  have hKc : K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) +
      (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) + rootUnionK 3 3 1 T.m₁ T.κ0 := by
    have h0 := K0_pos 3 3 T.κ0
    have h1' := rootUnionK_nonneg (d := 3) (L := 3) (m₁ := T.m₁) 1 T.κ0
    linarith
  obtain ⟨F1, c, e, -, hprop, hvals, hval⟩ := HC Jr C z (Lb₀ ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
      (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))))
    (Lab₀.sum (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj) hN1
      (by norm_num) (fun _ => Set.univ)
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) _
    (2 * T.κdec - 1)
    (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
      rootUnionK 3 3 1 T.m₁ T.κ0) _
    ι hb₁ hbC
    Eτ Bτ hBτ hβS
    jL XL hj1 hjk Gk Gj
    hlocE
    X₀ X₁f 𝒦X hB hFl hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd
    F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs hsmall hnum hnum' hρ hρc
    hρpp hN hm1 hbb hab G₁ hG₁ hρp hEJ
    (fun q => Sum.inl (Sum.inr (Sum.inr ⟨z, ⟨bridge 1 z q.1.2, hbr q⟩⟩))) (fun _ => rfl) hE
    hM1hol hM1cont hM1diff hM1loc hM1W
    (lt_of_lt_of_le hεpos (le_max_left _ _)) hKc le_rfl T.marks_hκ hεnum
  exact ⟨e, _, fun T' => ⟨(hprop T').2.1, (hprop T').2.2.1, (hprop T').2.2.2.1,
    (hprop T').2.2.2.2⟩, fun D hX => ⟨(hvals D hX).2.2.1, (hvals D hX).2.2.2⟩, hval⟩

open Classical in
/-- The generic version of `e0CoeffFamily_class_fromTower_of_families` (any label functionals `Eτ`). -/
theorem e0CoeffFamily_class_fromTower_of_families_gen {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (ι : Type) [Fintype ι] {m₀ : ℕ} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (Eτ : ι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ) (Bτ : ι → ℝ)
        (_ : ∀ τ, 0 ≤ Bτ τ) (_ : 0 < S.β)
        (jL : ι → ℕ) (XL : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ, 1 ≤ jL τ) (_ : ∀ τ, jL τ ≤ k)
        (Gk : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (_ : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
          Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
        (X₀ X₁f : ι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (_ : ∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (_ : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (_ : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (_ : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
        (_ : ∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        (_ : ∀ τ, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 m₀ T.m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        (_ : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν (jL τ) bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl)))
        (_ : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν (jL τ) bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
        (F₁L : ι → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
            (rhoSep T.m₁)) 2,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (Dec2.decG (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2
              (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).1
              (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ,
              Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1
                  3 / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (_ : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
          (Gj τ))
        (_ : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (_ : R * δ₁ ≤ deltaStar 3 3 2) (_ : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (_ : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (_ : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        (_ : 3 ^ m₀ ∣ N₁) (_ : 1 ≤ m₀)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (_ : S.p₁ ≤ ρ)
        (_ : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
          Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
        (𝒴C : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
        (H : physParam 2 S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (_ : ∀ Y ∈ 𝒴C, (∑ τ : ι, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
            2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
              2 * κdec * treeLenCov S.G' m₀ Y)
          else 0) ≤ εC * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y)),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the numerical condition of the composed activity
      max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) εC ≤
        1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
          Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) →
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
  obtain ⟨β₀, hβ₀, HG⟩ := e0CoeffFamily_class_fromTower_of_families_core T hHull hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  obtain ⟨Jr, HG'⟩ := HG k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  refine ⟨Jr, ?_⟩
  intro C z ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk
    Gj hlocE X₀ X₁f 𝒦X hB hFl cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀ hκ₀ hκdec
    hκ h1 hlog hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 R hR hsmR hRs
    hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ 𝒴C h𝒴 H hH εC hεC hnumH hE
    hεnum
  have ha1 : (1 : ℝ) < corrU := by norm_num [corrU]
  have hκ0' : aEnt 3 3 + 1 ≤ T.κ0 := by linarith [T.κ0_two]
  have h𝒴dj := classActivityDomains_isDj_gen S jL XL X₁f 𝒦X hcov hopt hN hm1 le_rfl 𝒴C h𝒴
  obtain ⟨AC, hAC⟩ := classActivityFamily_labelAct_gen S hb₁ hbC Eτ Bτ hBτ hβS jL XL Gk Gj X₀ X₁f
    𝒦X hB hFl S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm hcov hX₁ hconn hrow
    hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hN hm1
    le_rfl (S.blockU z) hρ hρc hp ha1 hbb.le hab 𝒴C h𝒴 h𝒴dj H (fun θ Y u Φ => by rw [hH])
    hκ0' hnumH
  obtain ⟨-, -, -, hhol, hcont, hdiff, hloc⟩ := classActivityFamily_fields_gen S hb₁ hbC Eτ Bτ
    hBτ hβS jL XL Gk Gj X₀ X₁f 𝒦X hB hFl S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm
    hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁L hF₁an hF₁ SolL hSolan
    hSolprop FkL hFkan hFk hN hm1 le_rfl (S.blockU z) hρ hρc hp ha1 hbb.le hab 𝒴C h𝒴 H
    (fun θ Y u Φ => by rw [hH])
  exact HG' C z ι hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hFl hcψ hMX hdm
    hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁L hF₁an hF₁ SolL hSolan
    hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs hsmall hnum hnum' hρ hρc hρpp hN hm1 hbb hab G₁
    hG₁ hρp hEJ 𝒴C h𝒴 H hH hεC h𝒴dj
    ⟨AC, fun θ _ u Y => hAC θ u Y,
      fun Y Φ => by
        rw [show (fun r : physParam 2 S × ℂ => (AC r.1 r.2).H Y Φ) =
          fun r => H r.1 Y r.2 Φ from funext fun r => by rw [hAC]]
        exact hhol Y Φ,
      fun Y θ hθ u hu => by
        rw [show (AC θ u).H Y = fun Φ => H θ Y u Φ from funext fun Φ => by rw [hAC]]
        exact hcont Y θ hθ u hu,
      fun θ hθ Y Φ => by
        rw [show (fun u => (AC θ u).H Y Φ) = fun u => H θ Y u Φ from
          funext fun u => by rw [hAC]]
        exact hdiff θ hθ Y Φ,
      fun Z θ hθ θ' hθ' hres s hs Y hsub => by
        rw [hAC, hAC]
        exact hloc Z θ hθ θ' hθ' hres s hs Y hsub⟩ hE hεnum

open Classical in
/-- **The coefficient family of the new energy density of a class with inherited labels at the
tower, with both families constructed.**  See the module doc-string: under the per-label settings,
maps and numerics of the inherited labels, the formula of the activities, the bound condition
`hnumH`, the analyticity `hE` and the smallness of the composed amplitude, the conclusion of
`e0CoeffFamily_class_fromTower_of_labels` holds for the constructed label system, activity family
and labels of the rooted pairs; stated here: the coefficient family `e` (analytic, local, bounded,
rooted), `E0locJ = ∑ e`, `E0locH = ∑ e` at every chart datum and `hval` on the class domain. -/
theorem e0CoeffFamily_class_fromTower_of_families {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ T.m₁ (k + 1) × Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ T.m₁ (k + 1) 2 (rhoSep T.m₁)} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 < S.β) (_ : 0 ≤ P.E₀)
        (Gk : 𝒯E → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (X₀ X₁f : 𝒯E → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : 𝒯E → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : 𝒯E, BgSetting 2 S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) τ.1.1)
        (_ : ∀ τ : 𝒯E, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (_ : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (_ : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (_ : ∀ τ : 𝒯E, CovSetup S.G' C.m₀ τ.1.1 τ.1.2.2 (𝒦X τ))
        (_ : ∀ τ : 𝒯E, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ))
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        (_ : ∀ τ : 𝒯E, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ τ.1.2.2) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ C.m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        (_ : κdec - 1 ≤ P.κ)
        (_ : ∀ τ : 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1.1 τ.1.2.2) (compWeight 3 S.a₁) S.ν τ.1.1 bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2)
        (F₁L : 𝒯E → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ : 𝒯E, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : 𝒯E → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (_ : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ : 𝒯E, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
            (rhoSep T.m₁)) 2,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (Dec2.decG (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2
              (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).1
              (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ,
              Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1
                  3 / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ : 𝒯E, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (_ : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ : 𝒯E, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (_ : ∀ (τ : 𝒯E) (h : τ.1.1 ≤ k + 1), GsSpecStrong τ.1.1 h τ.1.2.2
          (C.Tm.gs τ.1.1 τ.1.2.2))
        (_ : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (_ : R * δ₁ ≤ deltaStar 3 3 2) (_ : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (_ : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (_ : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 1 ≤ C.m₀)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ q.1.1.1.1 (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (C.Tm.gs q.1.1.1.1 q.1.1.1.2.2) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * C.Tm.E q.1.1.1.1 q.1.1.1.2.1 q.1.1.1.2.2 r.1 r.2))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (_ : S.p₁ ≤ ρ)
        (𝒴C : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
        (H : physParam 2 S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (_ : ∀ Y ∈ 𝒴C, (∑ τ : 𝒯E, if Y ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
            2 * P.E₀ * Real.exp (-κ₀ * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2 -
              2 * κdec * treeLenCov S.G' C.m₀ Y)
          else 0) ≤ εC * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y)),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the numerical condition of the composed activity
      max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) εC ≤
        1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
          Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) →
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
  obtain ⟨β₀, hβ₀, HG⟩ := e0CoeffFamily_class_fromTower_of_families_gen T hHull hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  obtain ⟨Jr, HG'⟩ := HG k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ Gk X₀
    X₁f 𝒦X hB hFl cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀ hκ₀ hκdec hκ h1
    hlog hκP hchart F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 R hR hsmR hRs hsmall
    hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC hnumH hE hεnum
  have hmem : ∀ τ : 𝒯E, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (3 ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
        Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
        (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : 𝒯E, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem τ).1).1
  have hjk : ∀ τ : 𝒯E, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem τ).1).2
  have hXp : ∀ τ : 𝒯E, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem τ).2.2.1
  have hy : ∀ τ : 𝒯E, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem τ).2.2.2
  have hraw := fun τ : 𝒯E => classOldEnergy_chart_radius_raw (N := 2) (b := bL) C hm hcl hκP hE₀
    S.a₁ S.ν δ₃ T.t δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  have hEJ : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ : 𝒯E,
        C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 (Jr.PJ τ.1.1 (rawOf D, w)).1
          (Jr.PJ τ.1.1 (rawOf D, w)).2 := fun D _ w => by
    unfold StepSetting.JointRep.EJ
    rw [Finset.sum_coe_sort 𝒯E (fun τ => C.Tm.E τ.1 τ.2.1 τ.2.2 (Jr.PJ τ.1 (rawOf D, w)).1
      (Jr.PJ τ.1 (rawOf D, w)).2), h𝒯,
      sum_classLabels_E_eq_Edens C.m₀ C.Tm (fun j => (Jr.PJ j (rawOf D, w)).1)
      (fun j => (Jr.PJ j (rawOf D, w)).2)]
  have key := HG' C z 𝒯E hb₁ hbC (fun τ r => C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2)
    (fun _ => P.E₀) (fun _ => hE₀) hβS (fun τ => τ.1.1) (fun τ => τ.1.2.2) hj1 hjk Gk
    (fun τ => C.Tm.gs τ.1.1 τ.1.2.2)
    (fun τ Ψ Ψ' h h' hag => hcl.localE τ.1.1 τ.1.2.1 τ.1.2.2 Ψ Ψ' h h' hag) X₀ X₁f 𝒦X hB hFl hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1)
    (fun τ => (hraw τ).2) F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs
    hsmall hnum hnum' hρ hρc hρpp hN hm1 hbb hab G₁ hG₁ hρp hEJ 𝒴C h𝒴 H hH hεC hnumH hE hεnum
  exact key

end Balaban.Inhabited
