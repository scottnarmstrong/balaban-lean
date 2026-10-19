/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Src
public import Balaban.Inhabited.ZeroSourceActivityCommon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-source activity family with the explicit direct terms, uniformly in the step radius

`zeroSourceActivity_common_fromTower_agree_rot`: the statement of
`zeroSourceActivity_common_fromTower_agree` with the explicit form of the direct terms `I` at zero
source (`sourceDirectTerms_scale_fromTower_ray_rho_core`); the landed theorem is its corollary.
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
radius, with the explicit direct terms, general tower.**  For towers `T` that agree with `T₀` on
`m₀, m₁, BG, BG₂, κ, κ₀, κ'` and all radii `t ≥ c L^{-α(k+1)}` (`2 α < d - 2`), beyond one
threshold `β₀`, at source radius `q ≤ 1`: the conclusion of
`zeroSourceActivity_common_fromTowerG_core` with the threshold `stepTheta` of the output constants
in place of the record `C.theta`. -/
theorem StepTowerG.zeroSourceActivity_common_agree_rot {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T₀ : StepTowerG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {c α : ℝ} (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ →
      T.BG = T₀.BG → T.BG₂ = T₀.BG₂ → T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ S : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
            ℂ → (RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
          (I : DirectTerms S T.m₀ hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2 (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
                (physAgΘ S) (AgFDirPair S))
          (hF : DirectTermsFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t q))
          (hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)),
      (I.𝒴 = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
          polyDom S.G' (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
            (LocalCover.fam T.m₀ (LocalCover.blockSite k z))) ∪
        (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
          polyDom S.G' (LocalCover.nbhdF T.m₀ s.1) T.m₀ k (LocalCover.fam T.m₀ s.1)) ∧
      ∃ (F₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N → ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ)),
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₂ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₂ z p).1 = dphi (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (Sol₂ z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2)) ∧
        (∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
          (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
          (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
          I.T Y x w σ (Θ, 0) = -(S.β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                (LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) T.m₀ k
                (LocalCover.fam T.m₀ (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                S.G' T.m₀ (X1 S.G' T.m₀ k (LocalCover.fam T.m₀ (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (compWeight L S.a₁) S.ν k z
                  (F₂ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol₂ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                    flEdat S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) (F₂ z (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                        (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                    (extParams S.G' (↑(LocalCover.nbhdF T.m₀ (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0)) ∧
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
                    (flFieldOne S.G' (stepG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          0 < 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))) ≤
              stepTheta d L (2 * (K0 d L T.κ0 + 1) + max (2 * K0 d L T.κ0)
                (rootUnionK d L T.m₀ T.m₁ T.κ0)) (2 * T.κdec - 1) T.κ0 T.κ' ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))) ≤
              stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
              (2 * T.κdec - 1) T.κ0 T.κ' ∧
          ∃ A : physParam N S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit T.m₀ hp).Ωb
              (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0
              (2 * (K0 d L T.κ0 + 1)),
            A = labelActFamilyOn S T.m₀ (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I hF
                  hLN hp0 (by norm_num) hεU T.κ0_ent
                  T.marks_K0_le ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
              Jr.W1 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))
                  ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (s : ℂ) • S.hatC x) =
                (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam N S) (s : ℂ)).H y
                  ((S.blockSplit T.m₀ hp).restr x)) ∧
            (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
              ∀ t ∈ Icc (0 : ℝ) 1,
              Jr.W2 (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) e.2
                  ((e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), (t : ℂ) • S.hatC x) =
                ∑ y, (A e (t : ℂ)).H y ((S.blockSplit T.m₀ hp).restr x) -
                  ∑ y, (A ((e.1, 0) : physParam N S) (t : ℂ)).H y
                    ((S.blockSplit T.m₀ hp).restr x)) ∧
            ∀ {ι : Type} [Fintype ι] (reads : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
              (dom : ι → Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
              (hdomR : ∀ b, ∀ Y ∈ dom b, IsDj T.m₀ (k + 1) Y),
            ∃ A0 : physParam N S → ℂ → LabelAct
                (commonLabels (thickLabels I.𝒴 I.dom) hLN
                  (by have := T.hL; omega) reads dom hdomR) (S.blockSplit T.m₀ hp).Ωb
                (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)))) (2 * T.κdec - 1) T.κ0
                (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0),
              A0 = commonAct (zeroSourceAct A 2 (by norm_num))
                  hLN (by have := T.hL; omega) reads dom hdomR
                  (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two ∧
              (∀ y (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => (A0 r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ y (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                DifferentiableOn ℂ (fun u => (A0 e u).H y Φ) (ball (0 : ℂ) 2)) ∧
              (∀ y, ∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2,
                Continuous ((A0 e u).H y)) ∧
              (∀ (e : physParam N S) (u : ℂ) (Φ : ∀ b, (S.blockSplit T.m₀ hp).Ωb b),
                ∑ y, (A0 e u).H y Φ =
                  sqFactor 2 u * ∑ y, (A ((e.1, 0) : physParam N S) u).H y Φ) ∧
              (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
                ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) s x =
                    ∑ y, (A0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit T.m₀ hp).restr x)) ∧
              (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)) s x =
                  ∑ y, (A0 ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                    (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit T.m₀ hp).restr x)) ∧
              Nonempty (ParamMarkFamily (S.blockSplit T.m₀ hp).μ
                (commonLabels (thickLabels I.𝒴 I.dom) hLN
                  (by have := T.hL; omega) reads dom hdomR) A0
                (fun i : Empty => i.elim) (fun _ _ _ _ => (0 : ℂ)) 0 (fun i : Empty => i.elim)
                (physV S S.a₁ S.ν T.t) (ball (0 : ℂ) 2) (physCarrier S T.m₀ hp)) ∧
              (∀ _y₀ : {Y // Y ∈ I.𝒴} ⊕ RootUnionLb T.m₀ reads dom,
                Nonempty (InterpMarks S.nuFl (S.blockSplit T.m₀ hp)
                  (S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))) (fun _ _ => (0 : ℂ))))
  := by
  classical
  obtain ⟨C₀, hC₀k0, -, hC₀k', -, hC₀H, -, -, -, -, hC₀Kc, hC₀Kall, hC₀Ktot⟩ :=
    T₀.exists_outputConsts hhull
  obtain ⟨β₁, M₁, M₂, hβ₁, hM₁, hM₂, hamp⟩ := StepTowerG.srcAmp_agree T₀ hA p hc hα
  have hθ0 := C₀.theta_pos
  obtain ⟨β₂, hβ₂, hinv⟩ := exists_beta0_inv_t_le (d := d) (L := L) T₀.hd T₀.hL
    (M₁ := 2 * M₁) (M₂ := 2 * M₂) (η := C₀.theta) (c := c) (α := α) (3 * p) (by positivity)
    (by positivity) hθ0 hc hα
  refine ⟨max β₁ β₂, hβ₁.trans (le_max_left _ _), ?_⟩
  intro T hm₀ hm₁ hBG hBG₂ hκ h0 h' k hk N₁ _ hLN hN ν hνpos hν β hβ hct p₁ hp0 hp₁ q hq0 hq D S hS hp
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : β₂ ≤ β := (le_max_right _ _).trans hβ
  have hβ3 : 3 ≤ β := hβ₁.trans hβ1
  have hdec : T.κdec = T₀.κdec := by rw [T.κdec_eq, T₀.κdec_eq, h0]
  obtain ⟨C, hCk0, -, hCk', -, hCH, -, -, -, -, hCKc, hCKall, hCKtot⟩ :=
    T.exists_outputConsts (by rw [hdec, hκ]; exact hhull)
  have hθeq : C.theta = C₀.theta := by
    unfold StepOutputConsts.theta
    rw [hCKtot, hC₀Ktot, hCKc, hC₀Kc, hCKall, hC₀Kall, hCH, hC₀H, hCk0, hC₀k0, hCk', hC₀k', hdec,
      h0, h', hm₀, hm₁]
  have hCθ : C.theta = stepTheta d L (2 * (K0 d L T.κ0 + 1) + max (2 * K0 d L T.κ0)
      (rootUnionK d L T.m₀ T.m₁ T.κ0)) (2 * T.κdec - 1) T.κ0 T.κ' := by
    unfold StepOutputConsts.theta
    rw [hCKtot, hCKc, hCKall, hCH, hCk0, hCk']
  have hρ : 0 < (1 : ℝ) := one_pos
  have hβρ : max 1 (1 : ℝ) ≤ β := max_le (by linarith) (by linarith)
  have hamp' := hamp T hm₀ hm₁ hBG hBG₂ hκ k hk N₁ ν β hβ1 hct p₁ hp0 hp₁ q hq0 S hS
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hmem0, -, -, h𝒴, F₂, Sol₂, hF₂, hSol₂, hTt, -⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_rho T k hk N₁ hLN hN ν hνpos hν β 1 hρ hβρ p₁ q hq0 hq D S
      hS hp
  obtain ⟨Jr, I, h𝒴I, hTI, hF, hεU, hεpos, H⟩ := activityFamilyAnalytic_of_witnessG_rho T k hk N₁
    hLN ν hνpos hν β 1 hβρ p₁ hp0 q hq0 hq _ rfl D rfl S (heq_of_eq hS) hp val 𝒴 Tt hval hcont hI
    hmem0
  obtain ⟨A, hAeq, han, hcontA, -, -, hW1, hW2, hS1, -, -, -, -, -⟩ := H T.marks_K0_le
  have hε4 : 4 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
            (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β)) ≤
        M₁ / T.t * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * M₂ * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
            Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
    subst hS
    exact hamp'.2
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := T.hL; omega : 1 ≤ L)
  have h3k : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1
  have hb3 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hβ' : ∀ ε : ℝ, ε ≤ 2 * (M₁ / T.t) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
      2 * (1 * M₂) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) →
      ε ≤ C.theta ∧
      ε ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' := by
    intro ε hε
    have hs : 0 < Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := Real.sqrt_pos.2 hb3
    have hℓ : 1 ≤ Real.log (β * (L : ℝ) ^ (k * (d - 2))) := by
      rw [Real.le_log_iff_exp_le hb3]
      have : β ≤ β * (L : ℝ) ^ (k * (d - 2)) := le_mul_of_one_le_right (by linarith) h3k
      exact (Real.exp_one_lt_three.le.trans hβ3).trans this
    have hw : (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p ≤
        (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) := pow_le_pow_right₀ hℓ (by omega)
    have hinv' := hinv k β T.t hβ2 hct
    have h1 : 2 * (1 * M₂) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ≤
        2 * (1 * M₂) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) hs.le
    have e1 : (2 * M₁ / T.t + 2 * M₂) * Real.log (β * (L : ℝ) ^ (k * (d - 2))) ^ (3 * p) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) =
        2 * (M₁ / T.t) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
        2 * (1 * M₂) * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) /
          Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by ring
    have hθ : ε ≤ C.theta := by
      rw [hθeq]
      linarith
    exact ⟨hθ, hθ.trans (T.marks_theta_le_stepTheta T.m₀ C hCKc hCKall hCH hCk0 hCk')⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := StepTowerG.zeroSourceActivity_common_of_witness_rho T C p
    (CE := M₁ / T.t) hM₂ 1 hρ k hk N₁ hLN ν hνpos hν β hβ3 _ rfl hβ' p₁ hp0 q hq0 hq D rfl S
    (heq_of_eq hS) hp val I hF hεU hεpos hε4 Jr ⟨A, hAeq, han, hcontA, hW1, hW2, hS1⟩
  refine ⟨Jr, val, I, hF, hεU, ⟨h𝒴I.trans h𝒴, F₂, Sol₂, hF₂, hSol₂, fun Y x w σ Θ => ?_⟩, hval,
    h1, h3.trans_eq hCθ, h4, h5⟩
  rw [hTI]
  exact hTt Y x w σ Θ

open Classical in
/-- **The zero-source activity family on the common labels of all roots, uniformly in the step
radius, with the explicit direct terms.**  The statement of
`zeroSourceActivity_common_fromTower_agree` with the clause of `zeroSourceActivity_common_fromTowerG_core`
at `d = L = 3`: the domains of `I` are the polymer domains of the local covers and at zero source its
terms are the explicit ray terms of the block expansions of decoupled pairs. -/
theorem zeroSourceActivity_common_fromTower_agree_rot {κmin : ℝ} (T₀ : StepTower κmin)
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
          (I.𝒴 = (Finset.univ.biUnion fun z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) =>
          polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
        (Finset.univ.biUnion fun s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2 =>
          polyDom S.G' (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1)) ∧
      ∃ (F₂ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol₂ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 → ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
        (∀ (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 T.BG T.κ) s D φ α →
            F₂ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 * T.t))) T.t p.2 →
            (Sol₂ z p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (Dec2.decG (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (Sol₂ z p).2 (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (Sol₂ z p).2 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (Sol₂ z p).1 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ, Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2)) ∧
        (∀ (Y : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (x w : (S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) (σ : ℂ)
          (Θ : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2),
          I.T Y x w σ (Θ, 0) = -(S.β : ℂ) *
            ∑ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
                (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) => i.1.1)
                S.G' 1 (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν k z
                  (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) s,
                    flEdat S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                        (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                    (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
            else 0)) ∧
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
  obtain ⟨β₀, h3, H⟩ := StepTowerG.zeroSourceActivity_common_agree_rot T₀.toG
    (T₀.hhull_toG_of_stepHullMin hHull) hA p hc (alpha_three_cast hα)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁ q hq0 hq D S
    hS hp => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  subst hS
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have hp' : 0 < (T.toG.step k hk N₁ ν β p₁).p₁ := hp
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' k hk N₁ (by simpa using h3N) hN ν hν0
    (by simpa using hν) β hβ (by rw [radius_three_cast]; exact hct) p₁ hp0 (by rw [e]; exact hp₁)
    q hq0 hq (StepTower.scaleDataG_of_fixed T D) (T.toG.step k hk N₁ ν β p₁) rfl hp'
  unfold StepTowerG.step at G
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  generalize hϱ : rhoSepG 3 3 T.toG.m₁ = ϱ
  have hϱ' : ϱ = rhoSep T.m₁ := hϱ.symm.trans (rhoSepG_three _)
  have hb' : b = β * 3 ^ k := hb.symm.trans (by rw [e])
  subst hϱ' hb'
  intro G
  exact G

end Balaban.Inhabited
