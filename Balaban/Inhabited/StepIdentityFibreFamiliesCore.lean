/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepIdentityFibreExplicitCore
public import Balaban.Inhabited.StepIdentityFibre
public import Balaban.Inhabited.StepIdentityFibreObsCore
public import Balaban.Inhabited.E0CoeffFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The uniform step identity of the zero class with the formulas of the coefficient families

`stepIdentity_zeroClass_fibre_fromTowerG_core` is `stepIdentity_zeroClass_fibre_fromTowerG`
together with the formula clauses that the latter does not state:
* for every root `z` of the energy family: the determinant expansion `E` with
  `E.term D′ C = ∑_{y ∈ B(z)} detActivityBg …`, `dz (rawOf D′, g) C = E.term D′ C` on the chart,
  and the direct-terms record `I0` with `Lab₀ ≍ thickLabels I0.𝒴 I0.dom` and
  `A₀ ≍ commonAct (zeroSourceAct (labelActFamilyOn … I0 …))` (`e0CoeffFamily_value_fromTowerG`);
* for the observable family (block scale `1`): the labels correspond to the domains of the local
  covers of the blocks and of the sites, the activity `Ao` has its explicit values at the zero source
  and at a nonzero source, and for every site `(y, i)` the family `Ev` of `mObs y i` is
  `evTerm … (siteFun … y i …)` for a decoupled pair (`obsFamily_pair_fibre_fromTowerG_rho_core`).

It is the projection of `stepIdentity_zeroClass_fibre_fromTowerG_explicitCore`
(`StepIdentityFibreExplicitCore.lean`), which also states the explicit direct terms of the record
`I0`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **The uniform step identity of the zero class on the fibre `h ≡ h₀`, with the formulas of the
coefficient families.**  The statement of `stepIdentity_zeroClass_fibre_fromTowerG` with further
clauses for the same witnesses: for every root `z`, the determinant expansion `E` of the block
`B(z)` (`E.term D′ C = ∑_{y ∈ B(z)} detActivityBg …`, `dz (rawOf D′, g) C = E.term D′ C` at the
data of the chart) and a direct-terms record `I0` with `Lab₀ ≍ thickLabels I0.𝒴 I0.dom` and
`A₀ ≍ commonAct (zeroSourceAct (labelActFamilyOn … I0 …))`; for the observable family, the labels
`Labo` correspond (`ys`) to the domains of the local covers of the blocks and of the sites, `Ao` is
the potential part `-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evTerm_z(Y)) ω ψ̂ σ e.1` at `(e.1, 0)` (decoupled
pairs per block) and the potential part plus the source part
`∑_s [Y ∈ polyDom_s] e.2 s · dirTerm (Ev₃ s Y) …` at `e` (decoupled pairs per site), and for every
site `(y, i)` the family `Ev` of `mObs y i` is `evTerm … (siteFun … y i …)` for a decoupled pair. -/
theorem stepIdentity_zeroClass_fibre_fromTowerG_core {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR)
    (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d
          (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d
            (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat
              (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS))
            (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0))
        (e0 : RootIdx d L N₁ T.m₁ (k + 1) → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ)
        (Lbo : Type) (_ : Fintype Lbo)
        (Labo : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lbo) (εHo : ℝ) (hεHo : 0 < εHo)
        (Ao : physParam N S → ℂ → LabelAct Labo
            (S.blockSplit 1 hp).Ωb εHo (2 * T.κdec - 1) T.κ0
          (K0 d L T.κ0 + 1))
        (mObs : CTorus d L N₁ T.m₁ (k + 1) → Fin N → physParam N S →
          Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
      (∀ (D' : BgData S.G' N)
          (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν
          (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          (S.withDatum D' hDh).WoneC
              (zeroClass d L N₁ T.m₁ k N ϱ) s x =
            ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub N S.G'), g) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁ T.m₁ k ϱ)
          S.hG' (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          S.a₁ S.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          (S.blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
        Nonempty (ParamMarkFamily (S.blockSplit 1 hp).μ
          (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) A₀
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG S) z} =>
            commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
          (fun θ i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0G T k β p₁)
          (physV S S.a₁
            S.ν T.t)
          (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) (physCarrier S 1 hp)) ∧
        ∃ c : physParam N S →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff (S.blockSplit 1 hp).μ
            (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1DomG S) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)
            (fun i u Φ => e1MarkGParamG S (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c θ C)
              (physV S S.a₁
                S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ∀ θ' ∈ physV S S.a₁
                S.ν T.t,
              physRestrict (N := N) (thickSet S.G'
                  (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C)))
                  (physIncl N S θ') → c θ C = c θ' C) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ∀ θ' ∈ physV S S.a₁
                S.ν T.t,
              physRestrict (N := N) (sitesOf C) (physIncl N S θ) =
                physRestrict (sitesOf C) (physIncl N S θ') →
                c θ C = c θ' C) ∧
            (∀ θ ∈ physV S S.a₁
                S.ν T.t,
              ‖c θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          (∀ (D' : BgData S.G' N)
              (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a
              S.ν (k + 1) 1 T.t D' →
            (S.withDatum D' hDh).E1locC
                (zeroClass d L N₁ T.m₁ k N ϱ) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
          ∃ dz : physParam N S → Finset
              (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData S.G' N)
                (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν
                  (k + 1) 1 T.t D' →
              ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
              -(1 / 2 : ℂ) * ∑ y ∈ (S.withDatum D' hDh).blockU z, ∑ i,
                  (S.withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              (S.withDatum D' hDh).E0locC
                  (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  (S.withDatum D' hDh).E1locC
                      (zeroClass d L N₁ T.m₁ k N ϱ) z) ∧
            (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV S
                S.a₁
                S.ν T.t) ∧
            (∀ θ ∈ (physV S S.a₁
                S.ν T.t),
              ∀ θ' ∈ (physV S S.a₁
                S.ν T.t),
              physRestrict (N := N) (thickSet S.G'
                  (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C)))
                  (physIncl N S θ') → dz θ C = dz θ' C) ∧
            (∀ θ ∈ (physV S S.a₁
                S.ν T.t),
              ‖dz θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp
                      (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
              (∀ θ C, e0 z θ C = dz θ C + c θ C) ∧
              (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 z θ C) (physV S
                S.a₁
                S.ν T.t) ∧
            (∀ θ ∈ (physV S S.a₁
                S.ν T.t),
              ∀ θ' ∈ (physV S S.a₁
                S.ν T.t),
              physRestrict (N := N) (thickSet S.G'
                  (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C)))
                  (physIncl N S θ') → e0 z θ C = e0 z θ' C) ∧
            (∀ θ ∈ (physV S S.a₁
                S.ν T.t),
              ‖e0 z θ C‖ ≤ (2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) + 1) * K0 d L T.κ0 *
                      Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 z θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
              (∀ (D' : BgData S.G' N)
                (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a
                S.ν (k + 1) 1 T.t D' →
              (S.withDatum D' hDh).E0locC
                  (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, e0 z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                  (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
            ∃ E : DetExpansionLocC S 1 z T.t
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
              (∀ D' C, E.term D' C = ∑ y ∈ S.blockU z,
                detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D' y C) ∧
              (∀ (D' : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C = E.term D' C) ∧
            ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
                ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
                (RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
                  (CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
              (I0 : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))
                (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (1 / S.β))
                (physXW S (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val
                (physAgΘ S) (AgFDirPair S))
              (hFd : DirectTermsFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I0
                (physVq S S.a₁ S.ν T.t 1))
              (hεU : 0 ≤ S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β)),
              HEq Lab₀ (thickLabels I0.𝒴 I0.dom) ∧
              HEq A₀ (commonAct (zeroSourceAct
                (labelActFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I0 hFd
                  (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by subst hS; exact hp) (by norm_num) hεU
                  T.κ0_ent T.marks_K0_le) 2 (by norm_num))
                (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)
                (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two)) ∧
        2 * εHo ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
        (∃ (𝒴 : Finset (Set (CTorus d L N₁ T.m₁ (k + 1)))) (ys : Lbo ≃ {Y // Y ∈ 𝒴}),
          (∀ l, Labo.ysite l = (ys l).1) ∧
          𝒴 = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
              polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
            (Finset.univ.biUnion fun s : CTorus d L N₁ T.m₁ (k + 1) × Fin N =>
              polyDom S.G' (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1)) ∧
          ∃ (F₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N → (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol₂ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N → ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₂ z (s, rawOf D) = (φ, α)) ∧
        (∀ (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₂ z p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂ z p).2 ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (Sol₂ z p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (Sol₂ z p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (Sol₂ z p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ z p).2)) ∧
        ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lbo)
          (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          (Ao ((e.1, 0) : physParam N S) σ).H l Φ = -(S.β : ℂ) *
            ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Labo.ysite l ∈ polyDom S.G'
                (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
                (LocalCover.fam 1 (LocalCover.blockSite k z)) then
              rayTerm (dl3 (evTerm
                (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1)
                S.G' 1 (X1 S.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z)))
                (fun u s => blockEnergyFun S.G' (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν k z
                  (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                  (Sol₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
                    flEdat S.G' (stepG d L N₁ T.m₁ k ϱ) (F₂ z (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                      u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                        (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
                  (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂ z)
                    (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) (Labo.ysite l))
                (S.hatOf 1 p₁ hp Φ)) taylorWeight (S.hatOf 1 p₁ hp Φ) σ
                (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
            else 0) ∧
      (∃ (F₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N →
            DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
              (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
          (Sol₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N →
            Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
          (Ev₃ : CTorus d L N₁ T.m₁ (k + 1) × Fin N → Set (CTorus d L N₁ T.m₁ (k + 1)) →
            RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ),
        (∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N) (s : DecParams S.G') (D : BgData S.G' N),
          (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            F₃ a (s, rawOf D) = (φ, α)) ∧
        (∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N)
          (p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N),
          (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Sol₃ a p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₃ a p).2 ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (Sol₃ a p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (Sol₃ a p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (Sol₃ a p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₃ a p).2)) ∧
        (∀ a : CTorus d L N₁ T.m₁ (k + 1) × Fin N, Ev₃ a =
          evTerm
                  (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' 1
                  (X1 S.G' 1 k (LocalCover.fam 1 a.1))
                  (fun u t => siteFun S.G' (stepG d L N₁ T.m₁ k ϱ) a.1 a.2
                    (F₃ a (extParams S.G' (↑(LocalCover.nbhdF 1 a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t, u.1))
                    (Sol₃ a (extParams S.G' (↑(LocalCover.nbhdF 1 a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t,
                      flEdat S.G' (stepG d L N₁ T.m₁ k ϱ)
                        (F₃ a (extParams S.G' (↑(LocalCover.nbhdF 1 a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t, u.1))
                        u.1.1 (hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃ a)
                          (extParams S.G' (↑(LocalCover.nbhdF 1 a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t) u.1 u.2))).1
                    (u.1, hatPsiF S.G' S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₃ a)
                      (extParams S.G' (↑(LocalCover.nbhdF 1 a.1) : Set (CTorus d L N₁ T.m₁ (k + 1))) t) u.1 u.2))) ∧
        (∀ (a : CTorus d L N₁ T.m₁ (k + 1) × Fin N) (Y : Set (CTorus d L N₁ T.m₁ (k + 1))),
          AnalyticOnNhd ℂ (Ev₃ a Y) (XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ×ˢ
            {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
        ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ σ : ℂ, ‖σ‖ < 2 → ∀ (l : Lbo) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
          (Ao e σ).H l Φ = (Ao ((e.1, 0) : physParam N S) σ).H l Φ +
            ∑ s : CTorus d L N₁ T.m₁ (k + 1) × Fin N,
              if Labo.ysite l ∈ polyDom S.G' (LocalCover.nbhdF 1 s.1) 1 k
                  (LocalCover.fam 1 s.1) then
                e.2 s.1 s.2 * dirTerm (Ev₃ s (Labo.ysite l)) (fun _ => (1 : ℂ))
                  (S.hatOf 1 p₁ hp Φ) (S.hatOf 1 p₁ hp Φ) σ
                  (e.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
              else 0) ∧
        (∀ (y : CTorus d L N₁ T.m₁ (k + 1)) (i : Fin N)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k
              (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))),
            1 < obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) ∧
            obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))) * max (εHo + εHo) εHo ≤
              stepTheta d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
                RawData d L (N₁ * L ^ T.m₁) (k + 1) N ×
                    (unitPts S.G' × Fin N → ℂ) → ℂ,
      (∃ (Fy : DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Soly : Dec2.DecParams (coverOf S.G') × Edat (lvLowG d L N₁ T.m₁ k ϱ) N → ((lvLowG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((lvLowG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
        (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L 1) ν (rho4 d L N T.BG T.κ) s D φ α →
            Fy (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S.G') × Edat (lvLowG d L N₁ T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (lvLowG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            (Soly p).1 = dphi (lvLowG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) ν p.1) p.2.2.1 p.2.1
              (pertSource (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Soly p).2 ∧
            Dec2.DecFixed (coverOf S.G') (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
              (pertSource (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Soly p).2 ∧
            Small (lvLowG d L N₁ T.m₁ k ϱ) (Soly p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (lvLowG d L N₁ T.m₁ k ϱ) (Soly p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (lvLowG d L N₁ T.m₁ k ϱ) (Soly p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (lvLowG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (lvLowG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) ν p.1 false p.2.2.1 p.2.1
                (pertSource (lvLowG d L N₁ T.m₁ k ϱ) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Soly p).2)) ∧
        Ev = evTerm (fun i : ParIdx S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ T.m₁ (k + 1))) => i.1.1) S.G' 1
          (X1 S.G' 1 k (LocalCover.fam 1 y))
          (fun u s => siteFun S.G' (lvLowG d L N₁ T.m₁ k ϱ) y i
            (Fy (extParams S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
            (Soly (extParams S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s,
              flEdat S.G' (lvLowG d L N₁ T.m₁ k ϱ) (Fy (extParams S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) Fy
                  (extParams S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF S.G' 1 ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) Fy
              (extParams S.G' (↑(LocalCover.nbhdF 1 y) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2))) ∧
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν
                  (k + 1) 1 T.t ×ˢ
                {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t
                    (β * (L : ℝ) ^ (k * (d - 2)))})) ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ
                      T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ
                      T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ
                      T.t (β * (L : ℝ) ^ (k * (d - 2)))},
                ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam (S.blockSplit 1 hp).μ
                (fun θ t σ => tiltActObs Ao (show L ^ 1 ∣ N₁ from (by rwa [hm₀] at h3N)) T.κ0_ent hεHo.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2)))) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 1 S (Lbo ⊕ Lbo)
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                      (LocalCover.fam 1 y)) m)
                (fun m => blockMarkC S 1 hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                      (LocalCover.fam 1 y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (obsUnitVec S m)) 1 T'')
                (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                    (LocalCover.fam 1 y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 1 (Lbo ⊕ Lbo)
                    (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                        (LocalCover.fam 1 y))
                    (rootCube (m₀ := 1) (blockIndex y))))
                (fun θ => obsGrFam S 1 hp Ev
                  (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                      (LocalCover.fam 1 y))
                  (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T')
                    (physVq S S.a₁
                        S.ν T.t q) ∧
                (∀ θ ∈ physVq S S.a₁
                    S.ν T.t q, ‖mObs y i θ T'‖ ≤
                  ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
                      (CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 +
                          K0 d L T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ /
                        (obsRg CR s (p : ℝ) (β * (L : ℝ) ^ (k * (d - 2))))) *
                      (((N * L ^ (d * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) *
                      ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
                    CPE d L ((K0 d L T.κ0 + 1) + (K0 d L T.κ0 + 1) + K0 d L T.κ0 + K0 d L T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
                        (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp
                            (-T.κ0 *
                        (obsLab (Labo.sum Labo) hdj).dl
                          (obsRemLab
                            (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                                (LocalCover.fam 1 y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 1 (Lbo ⊕ Lbo)
                              (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                                  (LocalCover.fam 1 y))
                              (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVq S S.a₁
                    S.ν T.t q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVq S S.a₁
                    S.ν T.t q, ∀ θ' ∈ physVq S
                        S.a₁ S.ν T.t q,
                  agreeOn (thickSet S.G' (sitesOf T'))
                    (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                    (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq S S.a₁
                    S.ν T.t q, ∀ θ' ∈ physVq S
                        S.a₁ S.ν T.t q,
                  physRestrict (N := N) (sitesOf T')
                    (physIncl N S θ) =
                    physRestrict (sitesOf T') (physIncl N S θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
      ∀ (D' : BgData S.G' N)
          (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν
            (k + 1) 1 T.t D' →
        ∀ g : Fld d L N₁ T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
          (S.withDatum D' hDh).TstepC
              (zeroClass d L N₁ T.m₁ k N ϱ) g =
            Complex.exp (-(S.β : ℂ) *
                (S.withDatum D' hDh).AnewC -
              ((S.withDatum D' hDh).Eppp
                  (zeroClass d L N₁ T.m₁ k N ϱ) : ℂ) *
                ((S.withDatum D' hDh).nU : ℂ) +
              FcompAtC (zeroClass d L N₁ T.m₁ k N ϱ).m₀
                (zeroClass d L N₁ T.m₁ k N ϱ).Tm S.a
                    S.ν (Nat.le_succ k)
                (S.withDatum D' hDh).psiKdC g +
              ∑ z : RootIdx d L N₁ T.m₁ (k + 1), ∑ C,
                e0 z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                  (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C +
              ∑ y : CTorus d L N₁ T.m₁ (k + 1), ∑ i : Fin N, g y i *
                ∑ T', mObs y i ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N
                    S.G'), g) T') := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    stepIdentity_zeroClass_fibre_fromTowerG_explicitCore T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp₁ q hq0 hq1 D ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0, Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hα, hroot,
    hrest⟩ := H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp₁ q hq0 hq1 D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0, Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hα,
    fun z => ?_, hrest⟩
  obtain ⟨hP, -, hF, c, hc1, hc2, hcv, dz, hd1, hd2, he0, he2, hev, E, hE1, hE2, val, I0, hFd, hεU, -,
    hL, hA', -⟩ := hroot z
  exact ⟨hP, hF, c, hc1, hc2, hcv, dz, hd1, hd2, he0, he2, hev, E, hE1, hE2, val, I0, hFd, hεU, hL,
    hA'⟩

end Balaban.Inhabited
