/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E1MarkParamCommonG
public import Balaban.Inhabited.E1ParamRawLocal
public import Balaban.Fluctuation.GsumActiveParam
public import Balaban.Inhabited.E1ParamFibreValueG
public import Balaban.Inhabited.ZeroSourceActivityCommon
public import Balaban.Inhabited.OffFibreE1ActivityG
public import Balaban.Inhabited.E1CoeffFamilyGCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# One energy coefficient family at the general tower

At a scale of the general tower `T : StepTowerG d L N κmin` with `T.m₀ = 1` (zero class), the
coefficients of the local energy term are assembled as one family
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (G z θ) C` in the datum `θ` of the physical
parameter space, from the landed pieces: the activity `A₀` of
`zeroSourceActivity_common_fromTowerG` (zero-source activity on the common labels, with a records
`C` of the output constants), the marks `e1MarkGParamG` of one family of decoupling pairs chosen
before every parameter, the locality premises of `E1ParamRawLocal.lean`, and
`paramMarked_analytic_local_bound` with the support lemmas of `GsumActiveParam.lean`.

* `e1MarkParam_pairs_fromTowerG`: the field theorem with the defining clauses of the pairs and the
  block dependence for every parameter exposed (in `E1CoeffFamilyGCore.lean`).
* `e1Mark_hG_rawY_fromTowerG`: the sharp locality premise `hG` of
  `paramMarked_analytic_local_bound` (in `E1CoeffFamilyGCore.lean`).
* `e1CoeffFamily_value_fromTowerG`: analyticity, locality, bound and support of the coefficient
  family, with the identity of the coefficient sum at `(rawOf D′, 0)` and the local energy term of
  the step with the datum `D′` of the chart with constant field `h₀`.
  It is the projection of `e1CoeffFamily_value_fromTowerG_core` (`E1CoeffFamilyGCore.lean`), which
  also states the explicit direct terms of the record `I0`.
* `e1CoeffFamily_fromTowerG`: the corollary without the value clause.

The steps are stated over any `ϱ = rhoSepG d L T.m₁` with `S = hatStepKG … ϱ …`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section Main

open Classical in
/-- **One energy coefficient family at the tower, with its value on the fibre `h ≡ h₀`.**  Beyond
a threshold `β₀`, at every scale datum there are one family of decoupling pairs `(F₁, Sol)`, a
label system `Lab₀` and an activity `A₀` on the common labels (with its identity for the
interpolation integral at every chart datum), chosen before every root and before every datum, such
that for every root `z` the pairs have the eight clauses, the activity and the marks carry a
`ParamMarkFamily` over `physV`, `ball 0 (17 / 16 : ℝ)` and `physCarrier`, and the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParamG … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 d L T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`;
and, for every datum `D′` of the chart with constant field `h₀`,
(v) the local energy term of the step with the datum `D′` is
`ℰ₁^{(k+1)}(z) = ∑_C c z (rawOf D′, 0) C`. -/
theorem e1CoeffFamily_value_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS))
            (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)),
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
          ∀ (D' : BgData S.G' N)
              (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' S.a
              S.ν (k + 1) 1 T.t D' →
            (S.withDatum D' hDh).E1locC
                (zeroClass d L N₁ T.m₁ k N ϱ) z =
              ∑ C, c ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
      0 < εH ∧
      εH ≤ stepTheta d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' ∧
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
        DifferentiableOn ℂ (fun u => (A₀ θ u).H y Φ) (Metric.ball (0 : ℂ) 2)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) Φ,
          AnalyticOnNhd ℂ (fun r : physParam N S × ℂ =>
            e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t
              r.1 i r.2 Φ)
            (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16 : ℝ))) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ),
        DepOn (blocksOf 1 (k + 1) Set.univ
          ((commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁)
            (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
            (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).ysite
            (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i)))
          (e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ),
          Measurable (e1MarkGParamG S (fun b => F₁ (z, b))
            (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      (∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        ∀ (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ) Φ,
          ‖e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u Φ‖ ≤
            corrF0G T k β p₁ * Real.exp (-(2 * T.κdec - 1) *
              (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁)
                (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
                (e1DomG_isDj_of_eq T hm₀ D hϱ hS)).dl
                (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z i))) ∧
      ∃ Jr : S.JointRep T.t (2 * p₁),
        (∀ (D' : BgData S.G' N),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass d L N₁ T.m₁ k N ϱ)
              (rawOf D', (s : ℂ) • Balaban.Fluctuation.yhat x) =
              ∑ y, (A₀ ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
                (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
                ((S.blockSplit 1 hp).restr x)) ∧
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
            (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two) := by
  obtain ⟨β₀, h3β, H⟩ := e1CoeffFamily_value_fromTowerG_core T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3β, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, Jr, h10, val, I0, hFd,
    hεU, -, hL, hA', -⟩ := H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  exact ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, h1, fun z => ⟨(h2 z).1, (h2 z).2.2.2⟩, h3, h4, h5, h6, h7,
    h8, h9, Jr, h10, val, I0, hFd, hεU, hL, hA'⟩

open Classical in
/-- **One energy coefficient family at the tower.**  Beyond a threshold `β₀`, at every scale datum
there are one family of decoupling pairs `(F₁, Sol)`, a label system `Lab₀` and an activity `A₀` on
the common labels (the zero-source activity of `zeroSourceActivity_common_fromTower`, with its
identity for the interpolation integral at every chart datum), chosen before every root, such that
for every root `z` the coefficients
`c z θ C = gsumCoeff … (A₀ θ) (commonAnchor …) (e1MarkGParamG … z … θ) C` satisfy, for every finite
set `C` of level-one blocks:
(i) `θ ↦ c z θ C` is analytic on `physV`;
(ii) `c z θ C = c z θ' C` for `θ, θ' ∈ physV` with equal restrictions of `(raw datum, source)` to
the thickening of `Ŷ(sitesOf C)`;
(iii) `‖c z θ C‖ ≤ K₀ e^{-κ' d_Ext(C)}` on `physV`, with `K₀ = K0 d L T.κ0`, `κ' = T.κ'`;
(iv) for every `θ`, if `c z θ C ≠ 0` then `C` contains the root cube, `sitesOf C` is a polymer and
`d_Ext(C) = sizeJ(sitesOf C)`.
The family `A₀`, `c` and the marks carry a `ParamMarkFamily` over `physV`, `ball 0 (17 / 16 : ℝ)` and
`physCarrier`. -/
theorem e1CoeffFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb : Type) (_ : Fintype Lb)
        (Lab₀ : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ)
        (A₀ : physParam N S → ℂ →
          LabelAct (commonLabels Lab₀ (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS))
            (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)),
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
      ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
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
          ∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
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
              ‖c θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C)) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e1CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp₁ D ϱ hϱ S hS hp => ?_⟩
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ := H k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, -⟩ := hz.1 z
  exact ⟨h1, h2, c, hc, fun C =>
    ⟨(hcl C).1, (hcl C).2.1, (hcl C).2.2.2.1, (hcl C).2.2.2.2⟩⟩

end Main

end Balaban.Inhabited
