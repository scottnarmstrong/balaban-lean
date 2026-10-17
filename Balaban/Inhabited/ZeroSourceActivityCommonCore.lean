/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ZeroSourceActivityCommon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-source activity family on the common labels, with the explicit direct terms

`zeroSourceActivity_common_fromTowerG_core` is `zeroSourceActivity_common_fromTowerG` together with
the explicit form of the chosen direct-terms record `I`, which the latter does not state: the
domains `I.𝒴` are the polymer domains of the local covers of the blocks and of the sites, and at
zero source the term of a domain `Y` is the potential part
`-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t) ∂_w³ evTerm_z(Y)(Θ, σ t x₀) dt` of the localized block energy
terms, for a pair `(F₂, Sol₂)` of decoupled background and fluctuation maps per block with their
defining properties.  These are the explicit clauses of `sourceDirectTerms_scale_fromTowerG_ray_rho`
for the witness from which `I` is built (`activityFamilyAnalytic_of_witnessG_rho`), at source
radius `1`.

The proof assembles the same landed theorems as `activityFamilyAnalytic_fromTowerG_rho`,
`zeroSourceActivity_common_fromTowerG_rho` and `zeroSourceActivity_common_fromTowerG` (the source
family bound, the explicit direct terms, the activity family of a witness, the threshold of the
marks and the common family of a witness), keeping the explicit clauses.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric

open Classical in
/-- **The zero-source activity family on the common labels, with the explicit direct terms.**  The
statement of `zeroSourceActivity_common_fromTowerG` with one further clause for the same witnesses:
the domains of the direct-terms record `I` are the polymer domains of the local covers of the
blocks and of the sites, and at zero source its terms are the potential part
`-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evTerm_z(Y)) ω x σ Θ` for decoupled pairs `(F₂ z, Sol₂ z)` per
block with the defining properties of `i4b_analytic` and `Dec2.i4a_analytic`. -/
theorem zeroSourceActivity_common_fromTowerG_core {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) → ∀ q : ℝ, 0 < q → q ≤ 1 →
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
              CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
                CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
          2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k T.m₀ S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (q / S.β))) ≤
              C.theta ∧
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
                  (S.WoneC (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁))) (fun _ _ => (0 : ℂ)))) := by
  classical
  obtain ⟨β₁, CE, CF, -, hCE, hCF, hfam⟩ := sourceFamilyRelative_scale_fromTowerG_rho T hA p
  obtain ⟨β₂, hβ₂3, hβ₂⟩ := T.exists_beta0_marks T.m₀ C hKc hKall hH h0 h' p (CE := 2 * CE)
    (CF := 2 * (1 * CF)) (mul_nonneg zero_le_two hCE.le)
    (mul_nonneg zero_le_two (mul_nonneg zero_le_one hCF.le))
  refine ⟨max (max β₁ β₂) 1, 2 * CE, 2 * CF,
    hβ₂3.trans ((le_max_right _ _).trans (le_max_left _ _)), by linarith, by linarith, ?_⟩
  intro k hk N₁ _ hLN hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ)
  have hβ2 : β₂ ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
  have hβ3 : 3 ≤ β := le_trans hβ₂3 hβ2
  have hβρ : max 1 1 ≤ β := by rw [max_self]; linarith
  obtain ⟨_, _, _, _, _, _, _, _, _, hε4, _⟩ := hfam k hk N₁ hLN hN ν hνpos hν β hβ1 1 hβρ p₁
    hp0 hp₁ q hq0 hq D S hS hp
  obtain ⟨val, 𝒴, Tt, hval, -, hcont, hI, hmem0, -, -, h𝒴, F₂, Sol₂, hF₂, hSol₂, hTt, -⟩ :=
    sourceDirectTerms_scale_fromTowerG_ray_rho T k hk N₁ hLN hN ν hνpos hν β 1 one_pos hβρ p₁ q
      hq0 hq D S hS hp
  obtain ⟨Jr, I, h𝒴I, hTI, hF, hεU, hεpos, H⟩ := activityFamilyAnalytic_of_witnessG_rho T k hk N₁
    hLN ν hνpos hν β 1 hβρ p₁ hp0 q hq0 hq _ rfl D rfl S (heq_of_eq hS) hp val 𝒴 Tt hval hcont hI
    hmem0
  obtain ⟨A, hAeq, han, hcontA, -, -, hW1, hW2, hS1, -, -, -, -, -⟩ := H T.marks_K0_le
  obtain ⟨h1, h2, h3, h4, h5⟩ := StepTowerG.zeroSourceActivity_common_of_witness_rho T C p hCF 1
    one_pos k hk N₁ hLN ν hνpos hν β hβ3 _ rfl (fun ε hε => hβ₂ β k hβ2 ε hε) p₁ hp0 q hq0 hq D rfl
    S (heq_of_eq hS) hp val I hF hεU hεpos hε4 Jr ⟨A, hAeq, han, hcontA, hW1, hW2, hS1⟩
  refine ⟨Jr, val, I, hF, hεU, ⟨h𝒴I.trans h𝒴, F₂, Sol₂, hF₂, hSol₂, fun Y x w σ Θ => ?_⟩, hval,
    h1, h2.trans_eq (by ring), h3, h4, h5⟩
  rw [hTI]
  exact hTt Y x w σ Θ

end Balaban.Inhabited
