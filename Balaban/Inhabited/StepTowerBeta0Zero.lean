/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Src
public import Balaban.Inhabited.StepTowerRotZero
public import Balaban.Inhabited.ZeroSourceActivityCommon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-source activity family on the common labels, uniformly in the step radius

`zeroSourceActivity_common_fromTower_agree`: the conclusion of
`zeroSourceActivity_common_fromTower` (source radius `ρ = 1`) for all towers that agree with a
reference tower `T₀` on `m₁, BG, BG₂, κ` and all radii `t ≥ c 3^{-α(k+1)}` (`2 α < 1`), beyond one
threshold `β₀`.  The amplitude is `4 ε_U ≤ (M₁/t) (log b)^{3p}/√b + q M₂ (log b)^p/√b`
(`StepTowerG.srcAmp_agree`), and the marks threshold is the `1/t` smallness
`exists_beta0_inv_t_le`; the families are built by the landed witness theorems.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric Balaban.Inhabited.MarkBudgetAudit
open scoped Classical

open Classical in
/-- **The zero-source activity family on the common labels of all roots, uniformly in the step
radius.** -/
theorem zeroSourceActivity_common_fromTower_agree {κmin : ℝ} (T₀ : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c)
    (hα : 2 * α < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S))
          (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t q))
          (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)),
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              (stepOutputPhysical T hHull).theta ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) ≤
              stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 3 3 T.κ0 + 1)),
            A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                  ((S.blockSplit 1 hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj 1 (k + 1) Y),
            ∃ A0 : physParam 2 S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) (S.blockSplit 1 hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)))) (2 * T.κdec - 1) T.κ0 T.marksKc',
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  (show 3 ^ 1 ∣ N₁ by simpa using h3N) (by norm_num) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam 2 S) (u : ℂ) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam 2 S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) (show 3 ^ 1 ∣ N₁ by simpa using h3N)
                  (by norm_num) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physV S S.a₁ S.ν T.t) (ball (0 : ℂ) 2) (physCarrier S 1 hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb 1 reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit 1 hp)
                  (S.WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))) (fun _ _ => (0 : ℂ))))
  := by
  obtain ⟨β₀, h3, H⟩ := zeroSourceActivity_common_fromTower_agree_rot T₀ hHull hA p hc hα
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁ q hq0 hq D S hS
    hp => ?_⟩
  exact (H T hm₁ hBG hBG₂ hκ k hk N₁ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁ q hq0 hq D S hS hp).imp
    fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ => Exists.imp fun _ h => h.2

end Balaban.Inhabited
