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
  classical
  obtain ⟨β₁, M₁, M₂, hβ₁, hM₁, hM₂, hamp⟩ :=
    StepTowerG.srcAmp_agree T₀.toG hA p hc (alpha_three_cast hα)
  have hθ0 := (stepOutputPhysical T₀ hHull).theta_pos
  obtain ⟨β₂, hβ₂, hinv⟩ := exists_beta0_inv_t_le (d := 3) (L := 3) (by norm_num) le_rfl
    (M₁ := 2 * M₁) (M₂ := 2 * M₂) (η := (stepOutputPhysical T₀ hHull).theta) (c := c) (α := α)
    (3 * p) (by positivity) (by positivity) hθ0 hc (alpha_three_cast hα)
  refine ⟨max β₁ β₂, hβ₁.trans (le_max_left _ _), ?_⟩
  intro T hm₁ hBG hBG₂ hκ k hk N₁ _ h3N hN ν hνpos hν β hβ hct p₁ hp0 hp₁ q hq0 hq D S hS hp
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : β₂ ≤ β := (le_max_right _ _).trans hβ
  have hβ3 : 3 ≤ β := hβ₁.trans hβ1
  obtain ⟨h0, hdec, h'⟩ := StepTower.agree_rates T₀ T
  have hctG : c * ((3 : ℕ) : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t := by
    rw [radius_three_cast]; exact hct
  have hp₁G : p₁ ≤ pLog A₁ p (β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2))) := by
    rw [scale_three_cast]; exact hp₁
  have hρ : 0 < (1 : ℝ) := one_pos
  have hβρ : max 1 (1 : ℝ) ≤ β := max_le (by linarith) (by linarith)
  -- the amplitude
  have hamp' := hamp T.toG rfl hm₁ hBG hBG₂ hκ k hk N₁ ν β hβ1 hctG p₁ hp0 hp₁G q hq0
    (T.toG.step k hk N₁ ν β p₁) rfl
  rw [scale_three_cast] at hamp'
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hmem0, -, -, h𝒴', F₂, Sol₂, hF₂, hSol₂, hTt⟩ :=
    sourceDirectTerms_scale_fromTower_ray_rho_core T k hk N₁ h3N hN ν hνpos hν β 1 hρ hβρ p₁ q hq0 hq
      D S hS hp
  obtain ⟨Jr, I, h𝒴, hT, hF, hεU, hεpos, H⟩ := activityFamilyAnalytic_of_witness_rho T k hk N₁
    h3N ν hνpos hν β 1 hβρ p₁ hp0 q hq0 hq D S hS hp val 𝒴 Tt hval hcont hI hmem0
  obtain ⟨A, hAeq, han, hcontA, -, -, hW1, hW2, hS1, -, -, -, -, -⟩ := H T.marks_K0_le
  have hε4 : 4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
            (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
        M₁ / T.t * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * M₂ * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) := by
    subst hS
    exact hamp'.2
  have hb3 : 0 < β * 3 ^ k := by positivity
  have hθeq : (stepOutputPhysical T hHull).theta = (stepOutputPhysical T₀ hHull).theta := by
    have e : ∀ U : StepTower κmin, (stepOutputPhysical U hHull).theta =
        stepTheta 3 3 (2 * (K0 3 3 U.κ0 + 1) + max (2 * K0 3 3 U.κ0)
          (rootUnionK 3 3 1 U.m₁ U.κ0)) (2 * U.κdec - 1) U.κ0 U.κ' := fun U => rfl
    rw [e T, e T₀, h0, hdec, h', hm₁]
  have hβ' : ∀ ε : ℝ, ε ≤ 2 * (M₁ / T.t) * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
      2 * (1 * M₂) * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) →
      ε ≤ (stepOutputPhysical T hHull).theta ∧
      ε ≤ stepTheta 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' := by
    intro ε hε
    have hs : 0 < Real.sqrt (β * 3 ^ k) := Real.sqrt_pos.2 hb3
    have hℓ : 1 ≤ Real.log (β * 3 ^ k) := by
      rw [Real.le_log_iff_exp_le hb3]
      have h3k : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
      have : β ≤ β * 3 ^ k := le_mul_of_one_le_right (by linarith) h3k
      exact (Real.exp_one_lt_three.le.trans hβ3).trans this
    have hw : (Real.log (β * 3 ^ k)) ^ p ≤ (Real.log (β * 3 ^ k)) ^ (3 * p) :=
      pow_le_pow_right₀ hℓ (by omega)
    have hw0 : 0 ≤ (Real.log (β * 3 ^ k)) ^ p := by positivity
    have hinv' := hinv k β T.t hβ2 hctG
    rw [scale_three_cast] at hinv'
    have h1 : 2 * (1 * M₂) * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ≤
        2 * (1 * M₂) * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) hs.le
    have e1 : (2 * M₁ / T.t + 2 * M₂) * Real.log (β * 3 ^ k) ^ (3 * p) / Real.sqrt (β * 3 ^ k) =
        2 * (M₁ / T.t) * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        2 * (1 * M₂) * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) := by ring
    have hθ : ε ≤ (stepOutputPhysical T hHull).theta := by
      rw [hθeq]
      linarith
    exact ⟨hθ, hθ.trans (StepTower.marks_theta_le_stepTheta T hHull)⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := T.toG.zeroSourceActivity_common_of_witness_rho
    (stepOutputPhysical T hHull) p (CE := M₁ / T.t) hM₂ 1 hρ k hk N₁ (by simpa using h3N) ν hνpos
    (by simpa using hν) β hβ3 (β * 3 ^ k) (by norm_num) hβ' p₁ hp0 q hq0 hq
    (StepTower.scaleDataG_of_fixed T D) (rhoSepG_three _).symm S
    (by rw [hS]; exact (StepTower.toG_step_heq T k hk N₁ ν β p₁).symm) hp val I hF hεU hεpos hε4
    Jr ⟨A, hAeq, han, hcontA, hW1, hW2, hS1⟩
  exact ⟨Jr, val, I, hF, hεU, ⟨h𝒴.trans h𝒴', F₂, Sol₂, hF₂, hSol₂, fun Y x w σ Θ => by
    rw [hT]; exact hTt Y x w σ Θ⟩, hval, h1, h3, h4, h5⟩

end Balaban.Inhabited
