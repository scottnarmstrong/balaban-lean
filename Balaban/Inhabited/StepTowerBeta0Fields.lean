/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyActTower
public import Balaban.Inhabited.StepTowerBeta0Zero
public import Balaban.Inhabited.StepTowerRotFields

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
  obtain ⟨β₂, h3, H⟩ := zeroSourceFamily_fields_fromTower_agree_rot T₀ hHull hA p hcR hαR
  refine ⟨β₂, h3, fun T hm₁ hBG hBG₂ hκ hδ => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS hp
  exact (H T hm₁ hBG hBG₂ hκ hδ k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS hp).imp
    fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Balaban.Inhabited
