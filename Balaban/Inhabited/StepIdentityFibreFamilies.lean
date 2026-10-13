/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepIdentityFibre
public import Balaban.Inhabited.StepIdentityFibreObs
public import Balaban.Inhabited.E0CoeffFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The uniform step identity of the zero class with the coefficient families

At a scale of the shared tower (`d = L = 3`, `N = 2`), write `S[D′]` for the step with the block
datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀`, `C` for the class with
zero old terms and `θ′ = (rawOf D′, g)`.

`stepIdentity_zeroClass_fibre_fromTower` joins three landed statements beyond one threshold:
* the energy coefficient family `e0 z θ U = dz z θ U + c z θ U` of `e0CoeffFamily_value_fromTower`
  (determinant term and mark coefficient), with `ℰ₀(z) = ∑_U e0 z (rawOf D′, 0) U`;
* the observable coefficient family `mObs y i θ V` of `obsFamily_pair_fibre_fromTower`
  (`obsFamily_full_fromTower`), with
  `β_U^{-1/2} ∑_{y,i} g(y,i) ℳ₀(y; g)_i = ∑_{y,i} g(y,i) ∑_V mObs y i θ′ V`;
* the identity `stepIdentity_zeroClass_fibre_local_fromTower` at every datum of the fibre and every
  source of the unit ball (nonvanishing from the fibre activity of
  `stepActivityBoundC_fibre_fromTower`).

The two families (with all clauses of their theorems) are chosen before the datum `D′` and the
source `g`; the conclusion is
`TstepC = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ∑_U e0 z (rawOf D′, 0) U
  + ∑_{y,i} g(y,i) ∑_V mObs y i (rawOf D′, g) V]`.
The energy family, the observable family and the fluctuation activity used for the nonvanishing
have three different label systems; only the threshold is shared.

The statement is first proved for a general tower with block scale `1`
(`stepIdentity_zeroClass_fibre_fromTowerG`, with `T.m₀ = 1` and the hull-rate inequality of
`StepTowerG.exists_outputConsts`); the fixed-tower statement is its corollary.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

open Classical in
/-- **The uniform step identity of the zero class on the fibre `h ≡ h₀`, with the coefficient
families, general tower with block scale `1`.**  The statement of
`stepIdentity_zeroClass_fibre_fromTower` for `T : StepTowerG d L N κmin` with `T.m₀ = 1` and the
hull-rate inequality `hhull` (the hypotheses of `StepTowerG.exists_outputConsts`): the energy
family of `e0CoeffFamily_value_fromTowerG` (block scale `1`), the observable family of
`obsFamily_pair_fibre_fromTowerG` (block scale `T.m₀`) and the identity
`stepIdentity_zeroClass_fibre_local_fromTowerG`; the constants of the bounds are those of these
statements.  The energy family, the observable family and the fluctuation activity have three
different label systems; only the threshold is shared.  The identity is an equality of complex
exponentials, with the normalization term `E''' |T₁|` in the exponent. -/
theorem stepIdentity_zeroClass_fibre_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
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
              ∀ (D' : BgData S.G' N)
                (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a
                S.ν (k + 1) 1 T.t D' →
              (S.withDatum D' hDh).E0locC
                  (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, e0 z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                  (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
        2 * εHo ≤ CE * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ (3 * p) / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) +
          q * CF * (Real.log (β * (L : ℝ) ^ (k * (d - 2)))) ^ p / Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ∧
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
  classical
  obtain ⟨C, hk0, -, hk', -, hkH, -, -, -, -, hKc, hKall, -⟩ := T.exists_outputConsts hhull
  obtain ⟨βe, hβe3, He⟩ := e0CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hkH hk0 hk' hA p
  let T' : StepTowerG d L N κmin :=
    { T with m₀ := 1, m₀_pos := le_rfl, κ_log := by simpa only [hm₀] using T.κ_log }
  obtain ⟨βo, CE, CF, -, hCE, hCF, Ho⟩ := obsFamily_pair_fibre_fromTowerG T' hA p hCR hs0 hs
  obtain ⟨βa, -, Ha⟩ := stepIdentity_zeroClass_fibre_local_fromTowerG T hA p
  refine ⟨max (max βe βo) βa, CE, CF, hβe3.trans ((le_max_left _ _).trans (le_max_left _ _)),
    hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp₁ q hq0 hq1 D ϱ hϱ S hS hp
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  have hβe : βe ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ
  have hβo : βo ≤ β := ((le_max_right _ _).trans (le_max_left _ _)).trans hβ
  have hβa : βa ≤ β := (le_max_right _ _).trans hβ
  have hp0 : 0 < p₁ := hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hroot⟩ :=
    He k hk N₁ h3N hN ν hνpos hν β hβe p₁ hp₁ D (ϱ := rhoSepG d L T.m₁) rfl
      (T.step k hk N₁ ν β p₁) rfl hp
  obtain ⟨Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hamp, hsite, hpair⟩ :=
    Ho k hk N₁ (by rwa [hm₀] at h3N) hN ν hνpos hν β hβo p₁ hp0 hp₁ q hq0 hq1
      { D with covers := by have h := D.covers; rw [hm₀] at h; exact h }
      (T.step k hk N₁ ν β p₁) rfl hp
  have hid := Ha k hk N₁ h3N hN ν hνpos hν β hβa p₁ hp0 hp₁ D (T.step k hk N₁ ν β p₁) rfl
  choose hP hF c hc1 hc2 hcv dz hd1 hd2 e0 he0 he2 hev using hroot
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0, Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hα,
    fun z => ⟨hP z, hF z, c z, hc1 z, hc2 z, hcv z, dz z, hd1 z, hd2 z, he0 z, he2 z, (hev z).1⟩,
    hamp, hsite, ?_⟩
  intro D' hDh hX g hg
  have hg1 : ∑ x, ∑ i, ‖g x i‖ < 1 := lt_of_lt_of_le hg hq1
  rw [hid D' hDh hX g hg1, (hpair D' hDh hX g hg).2,
    Finset.sum_congr rfl fun z _ => (hev z).1 D' hDh hX]

open Classical in
/-- **The uniform step identity of the zero class on the fibre `h ≡ h₀`, with the coefficient
families.**  There are one threshold `β₀ ≥ 3` (the maximum of the thresholds of the energy family,
of the observable family and of the fibre activity) and constants `C_E, C_F`.  At every scale datum
with `β ≥ β₀`, `0 < p₁ ≤ A₁ (log β_k)^p`, and for `0 < q ≤ 1`, there are, chosen before the datum
and the source:
* the energy witnesses of `e0CoeffFamily_value_fromTower`: decoupling pairs `F₁, Sol`, labels
  `Lab₀`, an activity `A₀` (with its identity for `W₁` at every chart datum), and for every root `z`
  the mark coefficient `c`, the determinant term `dz` and `e0 z = dz + c`, each analytic on `physV`,
  local in the parameter on the thickening of `Ŷ(sitesOf U)`, bounded by a constant times
  `e^{-κ' d_Ext(U)}` and supported on rooted polymer sets, with
  `ℰ₀(z) = ∑_U e0 z (rawOf D′, 0) U` at every chart datum `D′` of the fibre;
* the observable witnesses of `obsFamily_full_fromTower`: labels, an activity `Ao`, and for every
  site `(y, i)` an amplitude and a family `Ev`, with the coefficient `mObs y i θ V`
  (`= obsCoeffParam …`), analytic and bounded on `physVq … q`, supported on rooted polymer sets, and
  equal at two parameters of `physVq … q` whose raw data agree on `thickSet (sitesOf V)` and whose
  sources agree on `sitesOf V`; equality of their physical restrictions to `sitesOf V` also gives
  equality of the coefficients;

such that for every datum `D′` of the chart `Ξ^c(𝔹_{k+1}; 1, T.t)` with constant field `h₀` and
every source `g` with `∑ |g| < q`,
`TstepC(g) = exp [-β A^η_{k+1} - E''' |T₁| + ℱ_k(ψ^{(k)}, g) + ∑_z ∑_U e0 z (rawOf D′, 0) U
  + ∑_{y,i} g(y,i) ∑_V mObs y i (rawOf D′, g) V]`
for the step with the datum `D′` and the class with zero old terms.  The energy family is
evaluated at the zero source, the observable family at `(rawOf D′, g)`.

Scope of the statement.
1. It is an equality of complex exponentials.  It does not select an analytic logarithm of
   `TstepC`, and the exponent on the right is determined by it only up to `2πi ℤ`.
2. It holds on the fibre `h ≡ h₀` of the chart of the whole step and for sources of the unit `ℓ¹`
   ball; it is not a statement for an arbitrary datum or generator.
3. `TstepC` is the fluctuation integral after the substitution (2.7): it contains the cutoff, the
   kernel `tKernelC`, the Jacobian `det C^{(k)1/2}` and the normalization of the fluctuation
   measure.  The term `E''' |T₁|` records these conventions and is not zero for the zero class; the
   term `ℱ_k(ψ^{(k)}, g)` is the pairing of the source with the complex small solution.

The marked energy coefficient `c` and observable coefficient `mObs` also have exact locality on
their respective site sets. The determinant coefficient `dz` and combined energy coefficient `e0`
retain the stated thick locality. -/
theorem stepIdentity_zeroClass_fibre_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR)
    (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp : 0 < (T.step k hk N₁ ν β p₁).p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ D : StepScaleData T k hk N₁ ν β p₁,
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3
          (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams (T.step k hk N₁ ν β p₁).G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            ((T.step k hk N₁ ν β p₁).G'.Ω 1 × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) × Torus 3
            (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf (T.step k hk N₁ ν β p₁).G') × Edat
              (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ →
          LabelAct (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D))
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 T.marksKc')
        (e0 : RootIdx 3 3 N₁ T.m₁ (k + 1) → physParam 2 (T.step k hk N₁ ν β p₁) →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ)
        (Lbo : Type) (_ : Fintype Lbo)
        (Labo : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lbo) (εHo : ℝ) (hεHo : 0 < εHo)
        (Ao : physParam 2 (T.step k hk N₁ ν β p₁) → ℂ → LabelAct Labo
            ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).Ωb εHo (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1))
        (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 (T.step k hk N₁ ν β p₁) →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ),
      (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
          (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
        XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
          (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂(T.step k hk N₁ ν β p₁).nuFl,
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).WoneC
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
            ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub 2 (T.step k hk N₁ ν β p₁).G'), g) (s : ℂ)).H y
              (((T.step k hk N₁ ν β p₁).blockSplit 1 hp).restr x)) ∧
      (∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        (∀ b, MarkedBlockExpansionDecPair 2 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
          (T.step k hk N₁ ν β p₁).hG' ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          ((T.step k hk N₁ ν β p₁).blockU z) (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁ (z, b)) (Sol (z, b))) ∧
        Nonempty (ParamMarkFamily ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
          (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) A₀
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
            commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
          (fun θ i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0 T k β p₁)
          (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
            (T.step k hk N₁ ν β p₁).ν T.t)
          (Metric.ball (0 : ℂ) corrU) (physCarrier (T.step k hk N₁ ν β p₁) 1 hp)) ∧
        ∃ c : physParam 2 (T.step k hk N₁ ν β p₁) →
            Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c θ C = gsumCoeff ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
            (commonLabels Lab₀ (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
              (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) (e1Dom_isDj T D)) (A₀ θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1Dom (T.step k hk N₁ ν β p₁)) z} =>
              commonAnchor Lb (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z i)
            (fun i u Φ => e1MarkGParam (T.step k hk N₁ ν β p₁) (fun b => F₁ (z, b))
              (fun b => Sol (z, b)) p₁ hp z T.t θ i u Φ) C) ∧
          (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c θ C)
              (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → c θ C = c θ' C) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ∀ θ' ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              physRestrict (N := 2) (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (sitesOf C) (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
                c θ C = c θ' C) ∧
            (∀ θ ∈ physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t,
              ‖c θ C‖ ≤ K0 3 3 T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
              (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
            XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
              (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
            ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
                (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C) ∧
          ∃ dz : physParam 2 (T.step k hk N₁ ν β p₁) → Finset
              (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
                (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
              XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
                  (k + 1) 1 T.t D' →
              ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
              -(1 / 2 : ℂ) * ∑ y ∈ ((T.step k hk N₁ ν β p₁).withDatum D' hDh).blockU z, ∑ i,
                  ((T.step k hk N₁ ν β p₁).withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
                  (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E1locC
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z) ∧
            (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV (T.step k hk N₁ ν β p₁)
                (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ∀ θ' ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → dz θ C = dz θ' C) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ‖dz θ C‖ ≤ (27 * (covBLogMax 3 3 T.κ /
                  (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp
                      (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
              (∀ θ C, e0 z θ C = dz θ C + c θ C) ∧
              (∀ C : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 z θ C) (physV (T.step k hk N₁ ν β p₁)
                (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ∀ θ' ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              physRestrict (N := 2) (thickSet (T.step k hk N₁ ν β p₁).G'
                  (Yhat Set.univ (sitesOf C))) (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                physRestrict (thickSet (T.step k hk N₁ ν β p₁).G' (Yhat Set.univ (sitesOf C)))
                  (physIncl 2 (T.step k hk N₁ ν β p₁) θ') → e0 z θ C = e0 z θ' C) ∧
            (∀ θ ∈ (physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t),
              ‖e0 z θ C‖ ≤ ((2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 T.κ /
                  (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) + 1) * K0 3 3 T.κ0) *
                      Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 z θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
              ∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
                (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
              XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
                (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
              ((T.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
                  (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) z =
                ∑ C, e0 z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                  (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C) ∧
        2 * εHo ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
        (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
              (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
          ∃ hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k),
            1 < obsRg CR s (p : ℝ) (β * 3 ^ k) ∧
            obsRg CR s (p : ℝ) (β * 3 ^ k) * max (εHo + εHo) εHo ≤
              stepTheta 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                (2 * T.κdec - 1) T.κ0 T.κ' ∧
            ∃ Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
                RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
                    (unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ) → ℂ,
              (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν
                  (k + 1) 1 T.t ×ˢ
                {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t
                    (β * 3 ^ k)})) ∧
              (∀ Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ
                      T.t (β * 3 ^ k)},
                ∀ u' ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ
                      T.t (β * 3 ^ k)},
                AgHatDir (T.step k hk N₁ ν β p₁).hG' Y u u' → Ev Y u = Ev Y u') ∧
              (∀ Y, ∀ u ∈ XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
                  {ψh : unitPts (T.step k hk N₁ ν β p₁).G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ
                      T.t (β * 3 ^ k)},
                ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                  Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y)) ∧
              (∀ θ T', mObs y i θ T' = obsCoeffParam ((T.step k hk N₁ ν β p₁).blockSplit 1 hp).μ
                (fun θ t σ => tiltActObs Ao (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεHo.le
                  hdj (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2))
                  θ t σ)
                (fun m => obsY1 1 (T.step k hk N₁ ν β p₁) (Lbo ⊕ Lbo)
                  (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                      (LocalCover.fam 1 y)) m)
                (fun m => blockMarkC (T.step k hk N₁ ν β p₁) 1 hp m.1 m.2)
                (fun θ m T'' => obsHker
                  (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                      (LocalCover.fam 1 y))
                  (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (obsUnitVec (T.step k hk N₁ ν β p₁) m)) 1 T'')
                (obsRemLab (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                    (LocalCover.fam 1 y))
                  (fun Y => Sum.inl (Sum.inr Y))
                  (obsY0 1 (Lbo ⊕ Lbo)
                    (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                        (LocalCover.fam 1 y))
                    (rootCube (m₀ := 1) (blockIndex y))))
                (fun θ => obsGrFam (T.step k hk N₁ ν β p₁) 1 hp Ev
                  (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                      (LocalCover.fam 1 y))
                  (XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T') ∧
              ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ),
                AnalyticOnNhd ℂ (fun θ => mObs y i θ T')
                    (physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                        (T.step k hk N₁ ν β p₁).ν T.t q) ∧
                (∀ θ ∈ physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                    (T.step k hk N₁ ν β p₁).ν T.t q, ‖mObs y i θ T'‖ ≤
                  ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
                      (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 +
                          K0 3 3 T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' * (T.step k hk N₁ ν β p₁).p₁ /
                        (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
                      (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
                      ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
                      Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
                    CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                        (2 * T.κdec - 1) T.κ0 T.κ' *
                      (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                        ((T.step k hk N₁ ν β p₁).p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp
                            (-T.κ0 *
                        (obsLab (Labo.sum Labo) hdj).dl
                          (obsRemLab
                            (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                                (LocalCover.fam 1 y))
                            (fun Y => Sum.inl (Sum.inr Y))
                            (obsY0 1 (Lbo ⊕ Lbo)
                              (obsDomains (T.step k hk N₁ ν β p₁) (LocalCover.nbhdF 1 y) 1 k
                                  (LocalCover.fam 1 y))
                              (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                  Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
                (∀ θ ∈ physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                    (T.step k hk N₁ ν β p₁).ν T.t q, mObs y i θ T' ≠ 0 →
                  rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
                (∀ θ ∈ physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                    (T.step k hk N₁ ν β p₁).ν T.t q, ∀ θ' ∈ physVq (T.step k hk N₁ ν β p₁)
                        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t q,
                  agreeOn (thickSet (T.step k hk N₁ ν β p₁).G' (sitesOf T'))
                    (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                    (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
                  (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') ∧
                (∀ θ ∈ physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
                    (T.step k hk N₁ ν β p₁).ν T.t q, ∀ θ' ∈ physVq (T.step k hk N₁ ν β p₁)
                        (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t q,
                  physRestrict (N := 2) (sitesOf T')
                    (physIncl 2 (T.step k hk N₁ ν β p₁) θ) =
                    physRestrict (sitesOf T') (physIncl 2 (T.step k hk N₁ ν β p₁) θ') →
                  mObs y i θ T' = mObs y i θ' T')) ∧
      ∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
          (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
        XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a (T.step k hk N₁ ν β p₁).ν
            (k + 1) 1 T.t D' →
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
          ((T.step k hk N₁ ν β p₁).withDatum D' hDh).TstepC
              (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g =
            Complex.exp (-((T.step k hk N₁ ν β p₁).β : ℂ) *
                ((T.step k hk N₁ ν β p₁).withDatum D' hDh).AnewC -
              (((T.step k hk N₁ ν β p₁).withDatum D' hDh).Eppp
                  (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) : ℂ) *
                (((T.step k hk N₁ ν β p₁).withDatum D' hDh).nU : ℂ) +
              FcompAtC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).m₀
                (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)).Tm (T.step k hk N₁ ν β p₁).a
                    (T.step k hk N₁ ν β p₁).ν (Nat.le_succ k)
                ((T.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC g +
              ∑ z : RootIdx 3 3 N₁ T.m₁ (k + 1), ∑ C,
                e0 z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (T.step k hk N₁ ν β p₁).G'),
                  (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) C +
              ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2, g y i *
                ∑ T', mObs y i ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2
                    (T.step k hk N₁ ν β p₁).G'), g) T') := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    stepIdentity_zeroClass_fibre_fromTowerG T.toG rfl (T.hhull_toG_of_stepHullMin hHull) hA p
      hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ q hq0 hq1 D
  have e : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have G := H k hk N₁ (by simpa using h3N) hN ν hνpos (by simpa using hν) β hβ p₁
    (by rw [e]; exact hp₁) q hq0 hq1 (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm (T.step k hk N₁ ν β p₁) rfl hp
  revert G
  generalize hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = b
  have hb' : b = β * 3 ^ k := hb.symm.trans e
  subst hb'
  intro G
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0, Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hα, hroot,
    hamp, hsite, hid⟩ := G
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0, Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hα,
    fun z => ?_, hamp, hsite, hid⟩
  obtain ⟨h1, h2, c, hc, hcl, hcv, dz, hdz, hdzl, he, hel, hev⟩ := hroot z
  have e27 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) =
      27 * (covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) := by
    push_cast; ring
  refine ⟨h1, by simp only [corrF0_toG]; exact h2, c, hc, hcl, hcv, dz, hdz,
    fun C => ?_, he, fun C => ?_, hev⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hdzl C
    refine ⟨a1, a2, fun θ hθ => ?_, a4⟩
    have := a3 θ hθ
    simp only [StepTower.toG_κ, StepTower.toG_κ'] at this
    rw [e27] at this
    convert this using 3
    all_goals rfl
  · obtain ⟨a1, a2, a3, a4⟩ := hel C
    refine ⟨a1, a2, fun θ hθ => ?_, a4⟩
    have := a3 θ hθ
    simp only [StepTower.toG_κ, StepTower.toG_κ'] at this
    rw [e27] at this
    convert this using 3
    all_goals first | rfl | ring

end Balaban.Inhabited
