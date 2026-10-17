/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyGCore
public import Balaban.Inhabited.E1CoeffFamilyG
public import Balaban.Inhabited.DetOutputTermsWitnessG
public import Balaban.Inhabited.DetPackageFromTowerG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The determinant term in parameter form, and the energy coefficient family, general tower

`detParamFamily` (moved from `E0CoeffFamily.lean`, name and statement unchanged, now in
`E0CoeffFamilyGCore.lean`; it is generic in `d`, `L`, `N`): for a record `E : DetExpansionLocC S m₀ z eps κ'' cdet` of the determinant
expansion, the term `E.term D` is a function `dz` of the parameter `θ = (raw datum, source)`,
analytic on `physV`, local in the raw datum on the thickening of `Ŷ(sitesOf T)`, bounded by
`cdet · exp(-κ'' d_Ext T)` on `physV`, and supported on rooted polymer sets.

* `StepTowerG.detConst_le_mul`: the determinant constant of `T` is at most `2 · const · K₀`.
* `e0CoeffFamily_value_fromTowerG`: for the general tower with `T.m₀ = 1`, the mark coefficient
  family of `e1CoeffFamily_value_fromTowerG` together with the determinant function `dz` (with the
  determinant half of the value at every datum of the chart: `-½ ∑_{y ∈ B(z)} tr 𝕃(y,y) = ∑_T dz`
  and `ℰ₀ = ∑_T dz + ℰ₁`) and the sum `e0 = dz + c`, which has the four properties (analyticity,
  locality, the bound `(2 · cdet + 1) K₀ e^{-κ' d_Ext}`, polymer support) and
  `ℰ₀ = ∑_T e0 (rawOf D′, 0) T` at every datum `D′` of the chart with constant field `h₀`.
  It is the projection of `e0CoeffFamily_value_fromTowerG_core` (`E0CoeffFamilyGCore.lean`), which
  also states the explicit direct terms of the record `I0`.
* `e0CoeffFamily_fromTowerG`: the corollary without the value clauses.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section Main

open Classical in
/-- **The energy coefficient family at the general tower with its value on the fibre `h ≡ h₀`.**
See the module doc-string. -/
theorem e0CoeffFamily_value_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
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
          ∃ dz : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
              -(1 / 2 : ℂ) * ∑ y ∈ (S.withDatum D' hDh).blockU z, ∑ i,
                  (S.withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  (S.withDatum D' hDh).E1locC (zeroClass d L N₁ T.m₁ k N ϱ) z) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                dz θ C = dz θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖dz θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
          ∃ e0 : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ θ C, e0 θ C = dz θ C + c θ C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                e0 θ C = e0 θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖e0 θ C‖ ≤ (2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) + 1) * K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
            (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
              (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, e0 ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S.G'),
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
                (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two) := by
  obtain ⟨β₀, h3β, H⟩ := e0CoeffFamily_value_fromTowerG_core T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3β, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ := H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨hP, hfam, c, hc, hC, hcv, dz, hd1, hd2, e0, he0, he1, he2, E, hE1, hE2, val, I0, hFd, hεU, -,
    hL, hA', -⟩ := hz z
  exact ⟨hP, hfam, c, hc, hC, hcv, dz, hd1, hd2, e0, he0, he1, he2, E, hE1, hE2, val, I0, hFd, hεU,
    hL, hA'⟩

open Classical in
/-- **The energy coefficient family at the general tower: determinant, marks and their sum.**
See the module doc-string.  The first part is `e1CoeffFamily_fromTowerG`; then the determinant
function `dz` (with the determinant half of the value at every datum of the chart) and the sum
`e0 = dz + c`. -/
theorem e0CoeffFamily_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
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
              ‖c θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          ∃ dz : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData S.G' N) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
              XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁ T.m₁ (k + 1) N,
              -(1 / 2 : ℂ) * ∑ y ∈ (S.withDatum D' hDh).blockU z, ∑ i,
                  (S.withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              (S.withDatum D' hDh).E0locC (zeroClass d L N₁ T.m₁ k N ϱ) z =
                ∑ C, dz (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  (S.withDatum D' hDh).E1locC (zeroClass d L N₁ T.m₁ k N ϱ) z) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                dz θ C = dz θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖dz θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, dz θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
          ∃ e0 : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ θ C, e0 θ C = dz θ C + c θ C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0 θ C) (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf C))) (physIncl N S θ') →
                e0 θ C = e0 θ' C) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t,
              ‖e0 θ C‖ ≤ (2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) + 1) * K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0 θ C ≠ 0 → rootCube (m₀ := 1) z ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTowerG T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, fun k hk N₁ _ h3N h5 ν hν hνk β hβ p₁ hp₁ D ϱ hϱ S hS hp => ?_⟩
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ :=
    H k hk N₁ h3N h5 ν hν hνk β hβ p₁ hp₁ D hϱ S hS hp
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨h1, h2, c, hc, hcl, -, dz, hdz, hdzl, e0, he, hel, -⟩ := hz z
  exact ⟨h1, h2, c, hc,
    (fun C => ⟨(hcl C).1, (hcl C).2.1, (hcl C).2.2.2.1, (hcl C).2.2.2.2⟩),
    dz, hdz, hdzl, e0, he, hel⟩

end Main

end Balaban.Inhabited
