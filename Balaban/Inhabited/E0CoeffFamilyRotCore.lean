/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyGCore
public import Balaban.Inhabited.E0CoeffFamilyRotAct
public import Balaban.Inhabited.E0CoeffFamilyRotActLab
public import Balaban.Inhabited.E0CoeffFamilyRotCoef
public import Balaban.Inhabited.E0CoeffFamilyRotMarkG
public import Balaban.Fluctuation.DetRotation
public import Balaban.Inhabited.E0CoeffFamilyRotHeq
public import Balaban.Inhabited.E0CoeffFamilyRotTower
public import Balaban.Inhabited.E0CoeffFamilyRotTowerMark
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Per-label spin covariance of the energy coefficient family of the core

`e0CoeffFamily_value_fromTowerG_core_rot` is `e0CoeffFamily_value_fromTowerG_core` with one more
conjunct on the family `e0 = dz + c` it builds: for a real orthogonal `Q` and parameters `θ, θ'` of
`physV` whose raw data differ by the rotation `rotRaw (cmat Q)`, `e0 θ' C = e0 θ C` for every set
`C` of cubes.  The determinant part is covariant by `detActivityBg_rot`; the interpolation part by
the transport `gsumCoeff_rot` along the sitewise rotation of the block variables, with the
activities covariant through the explicit zero-source terms (`rayTermHat_rot`) and the marks
through `e1MarkGParamG_rot`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory

section Main

open Classical in
/-- **The energy coefficient family of the core with its per-label spin covariance.**  The conclusion
is that of `e0CoeffFamily_value_fromTowerG_core` with the last conjunct: for every real orthogonal
`Q` and parameters `θ, θ'` of `physV` whose raw data differ by the rotation `rotRaw (cmat Q)`, the
labels of `e0` agree: `e0 θ' C = e0 θ C`. -/
theorem e0CoeffFamily_value_fromTowerG_core_rot {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
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
        (∀ b, (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D →
          ∀ (φ : S.G'.Ω 1 × Fin N → ℂ) (α : S.G'.Ω 1 → ℂ),
            IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            (F₁ (z, b)) (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            ((Sol (z, b)) p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol (z, b)) p).2 ∧
            Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol (z, b)) p).2))) ∧
        (∀ (θ : physParam N S) (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z})
          (u : ℂ), DepOn (blocksOf 1 (k + 1) Set.univ i.1)
            (e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
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
              Lb = {Y // Y ∈ I0.𝒴} ∧ εH = 2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β))) ∧
              HEq Lab₀ (thickLabels I0.𝒴 I0.dom) ∧
              HEq A₀ (commonAct (zeroSourceAct
                (labelActFamilyOn S 1 (physInclScaled N S (((1 / S.β : ℝ)) : ℂ)) I0 hFd
                  (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by subst hS; exact hp) (by norm_num) hεU
                  T.κ0_ent T.marks_K0_le) 2 (by norm_num))
                (by rwa [hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T hm₀ D hϱ hS)
                (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU)) T.κ0_two) ∧
            (I0.𝒴 = (Finset.univ.biUnion fun z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
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
              (∀ (Y : Set (CTorus d L N₁ T.m₁ (k + 1)))
                (x w : (S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) (σ : ℂ)
                (Θ : RawData d L (N₁ * L ^ T.m₁) (k + 1) N),
                I0.T Y x w σ (Θ, 0) = -(S.β : ℂ) *
                  ∑ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S.G'
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
                          (extParams S.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z)) : Set (CTorus d L N₁ T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0) ∧
              ∀ (Q : Matrix (Fin N) (Fin N) ℝ), Qᵀ * Q = 1 →
                ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
                  (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
                    rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
                  ∀ C, e0 θ' C = e0 θ C) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTowerG_core T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₁ D ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ :=
    H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, fun z => ?_⟩
  obtain ⟨hP, hsp, hdp, hfam, c, hc, hC, hcv, dz, hdz1, hdz2, e0, he0, he0b, he0c, E, hEterm,
    hdzE, val, I0, hFd, hεU, hLbI, hεHI, hLabI, hAI, hdom, F₂, Sol₂, hF₂, hSol₂, hT⟩ := hz z
  refine ⟨hP, hsp, hdp, hfam, c, hc, hC, hcv, dz, hdz1, hdz2, e0, he0, he0b, he0c, E, hEterm,
    hdzE, val, I0, hFd, hεU, hLbI, hεHI, hLabI, hAI, hdom, F₂, Sol₂, hF₂, hSol₂, hT, ?_⟩
  intro Q hQ θ hθ θ' hθ' hrawrot Cs
  have hQ' : (cmat Q)ᵀ * cmat Q = 1 := (isRealOrth_ofReal hQ).1
  obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_orth N hQ
  obtain ⟨D₀, hD₀, hD₀θ''⟩ := hθ.1
  have hD₀θ : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D₀ := hD₀θ''
  have hD' : XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
      (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t (D₀.rot (cmat Q)) := xiCData_rot hQ hD₀
  have hθrot : (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf (D₀.rot (cmat Q)) := by
    rw [hrawrot, hD₀θ]; rfl
  have hδc : 0 ≤ T.δc := delta_nonneg_of_margin D.core T.dom_margin
  -- the determinant part
  have hdzrot : dz θ' Cs = dz θ Cs := by
    have e1 : θ = (⟨rawOf D₀, rawOf_mem_rawSub D₀⟩, θ.2) := Prod.ext (Subtype.ext hD₀θ) rfl
    have e2 : θ' = (⟨rawOf (D₀.rot (cmat Q)), rawOf_mem_rawSub _⟩, θ'.2) :=
      Prod.ext (Subtype.ext hθrot) rfl
    have h1 : dz θ' Cs = E.term (D₀.rot (cmat Q)) Cs := by
      rw [e2]; exact hdzE _ hD' _ Cs
    have h2 : dz θ Cs = E.term D₀ Cs := by
      rw [e1]; exact hdzE _ hD₀ _ Cs
    rw [h1, h2, hEterm, hEterm]
    exact Finset.sum_congr rfl fun y _ =>
      detActivityBg_rot D.core hk hδc T.large_block T.δc_small T.dom_margin T.coer_margin hQ' hD₀
        y Cs
  have hcrot : c θ' Cs = c θ Cs := by
    rw [hc θ' Cs, hc θ Cs]
    subst hLbI
    subst hεHI
    have hLab := eq_of_heq hLabI
    subst hLab
    have hAH := labelAct_H_of_heq (f := A₀) (hε := by rfl) (hκ := by rfl) (hκ0 := by rfl) (hKc := by rfl) (h := hAI)
    obtain ⟨E', hE', hEeq⟩ := exists_blockSplit_equiv (T.step k hk N₁ ν β p₁) 1 hp e
    have hp0 : 0 < p₁ := hp
    refine Balaban.Polymer.TwoTorusStep.gsumCoeff_rot _ _ _ _ _ _ _ (fun i u => hdp θ i u) Cs E'
      hE' (ae_mem_physCarrier _ 1 hp) ?_ ?_
    · intro s hs y Φ hΦ
      rw [hEeq Φ]
      refine (hAH θ' (s : ℂ) y (fun b u => e (Φ b u))).trans (Eq.trans ?_ (hAH θ (s : ℂ) y Φ).symm)
      refine commonAct_zeroSourceAct_H_rot (T.step k hk N₁ ν β p₁) 1 _ hFd _ _ _ _ _ _ _ _ _ _ _ _
        one_pos le_rfl hθ hθ' (s : ℂ) y Φ _ ?_
      intro z' hy hu
      have hψ : ∀ q, ‖((T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) q‖ ≤ p₁ :=
        (T.step k hk N₁ ν β p₁).hatOf_mem 1 hp hp Φ
      have hh : (T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp (fun b u => e (Φ b u)) =
          rotFld (cmat Q) ((T.step k hk N₁ ν β p₁).hatOf 1 p₁ hp Φ) :=
        hatOf_rot (T.step k hk N₁ ν β p₁) 1 hp e he le_rfl hΦ
      have hkey := directTerm_rot_tower T hk D hp _ rfl F₂ Sol₂ hF₂ hSol₂ I0.T hT hQ z'.1 hD₀ hψ hu
      refine Eq.trans (congrArg (fun x => I0.T z'.1 (x, x) (x, x) (s : ℂ)
        ((θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), 0)) hh) ?_
      rw [hrawrot, hD₀θ]
      exact hkey
    · intro s hs i Φ hΦ
      rw [hEeq Φ]
      exact e1MarkGParamG_rot_tower T hk D _ rfl hp (fun b => F₁ (z, b)) (fun b => (hsp b).1)
        (fun b => Sol (z, b)) (fun b => (hsp b).2) hQ e he z θ θ' hθ.1 hrawrot i s hΦ
  rw [he0 θ' Cs, he0 θ Cs, hdzrot, hcrot]

end Main

end Balaban.Inhabited
