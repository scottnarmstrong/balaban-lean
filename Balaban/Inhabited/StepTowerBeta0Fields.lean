/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActTower
public import Balaban.Inhabited.StepTowerBeta0Zero

/-!
The zero-source family of the class chain at every tower radius

`zeroSourceFamily_fields_fromTower_agree`: the statement of `zeroSourceFamily_fields_fromTower`
for all towers that agree with a reference tower `T₀` on `m₁, BG, BG₂, κ, δ` and every radius
`t ≥ c 3^{-α(k+1)}` (`2 α < 1`), beyond one threshold `β₀`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- The zero-source family of the class chain at every tower radius -/
theorem zeroSourceFamily_fields_fromTower_agree {κmin : ℝ} (T₀ : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
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
  obtain ⟨β₂, h3, H2⟩ := zeroSourceActivity_common_fromTower_agree T₀ hHull hA p hcR hαR
  refine ⟨β₂, h3, fun T hm₁ hBG hBG₂ hκ _ => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨Jr, val, I, hF, hεU, hval, hεpos, -, -, A, hAeq, -, -, hcom⟩ :=
    H2 T hm₁ hBG hBG₂ hκ k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ 1 one_pos le_rfl Dt S hS hp
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

end Balaban.Inhabited
