/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyTorusE0
public import Balaban.Inhabited.E0CoeffFamilyTorusIT
import Mathlib.Tactic.Linarith

/-!
# The energy coefficient family of the core agrees on two tori

`e0CoeffFamily_value_fromTowerG_core_twoTorus` applies `e0CoeffFamily_value_fromTowerG_core` on two
tori `N₁`, `N₁'` (one `β₀` for both) and returns, with all the properties that the core exports on
each torus, the exact agreement of the two families `e0`, `e0'` at the common box: for the root `z`
of the first torus and the root `bc z` of the second, a set `Tb` of cubes of a box
that embeds in both tori (the margins `hn`, `hn'`) and parameters `θ`, `θ'` of `physV` whose raw
data agree on the box of radius `R + 3 L^(k+1)` (`RawBoxAgree`), `e0' θ' (cubeMap '' Tb) = e0 θ Tb`.
The proof is `coreE0_twoTorus` applied to the objects of the two cores.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory
  Balaban.Polymer.TwoTorusStep

section Main

/-- **The energy coefficient family of the core on two tori.**  See the module doc-string. -/
theorem e0CoeffFamily_value_fromTowerG_core_twoTorus {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) (C : StepOutputConsts d L)
    (hKc : C.Kc = 2 * (K0 d L T.κ0 + 1))
    (hKall : C.Kall = max (2 * K0 d L T.κ0) (rootUnionK d L T.m₀ T.m₁ T.κ0))
    (hH : C.kH = 2 * T.κdec - 1) (h0 : C.k0 = T.κ0) (h' : C.k' = T.κ') {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ N₁' : ℕ) [NeZero N₁] [NeZero N₁'] (h3N : L ^ T.m₀ ∣ N₁)
        (h3N' : L ^ T.m₀ ∣ N₁'), 5 < N₁ → 5 < N₁' →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ D : StepScaleDataG T k hk N₁ ν β p₁, ∀ Dn : StepScaleDataG T k hk N₁' ν β p₁,
      ∀ {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁)
        (S' : StepSetting d L N₁' T.m₁ k N ϱ)
        (hS' : S' = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp' : 0 < S'.p₁),
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
      ∃ (F₁' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S'.G' × RawData d L (N₁' * L ^ T.m₁) (k + 1) N →
            (S'.G'.Ω 1 × Fin N → ℂ) × (S'.G'.Ω 1 → ℂ))
        (Sol' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) × Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S'.G') × Edat (stepG d L N₁' T.m₁ k ϱ) N →
            ((stepG d L N₁' T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁' T.m₁ k ϱ).Ω 1 → ℂ))
        (Lb' : Type) (_ : Fintype Lb')
        (Lab₀' : CubeLabels (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb') (εH' : ℝ)
        (A₀' : physParam N S' → ℂ →
          LabelAct (commonLabels Lab₀' (by rwa [hm₀] at h3N' : L ^ 1 ∣ N₁') (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S') (e1DomG_isDj_of_eq T hm₀ Dn hϱ hS'))
            (S'.blockSplit 1 hp').Ωb εH' (2 * T.κdec - 1) T.κ0 (2 * (K0 d L T.κ0 + 1) + rootUnionK d L 1 T.m₁ T.κ0)),
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
      (∀ (D' : BgData S'.G' N)
          (hDh : ∀ y i, D'.h y i = (S'.h₀ i : ℂ)),
        XiCData S'.G' S'.a S'.ν
          (k + 1) 1 T.t D' → ∀ g : Fld d L N₁' T.m₁ (k + 1) N,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S'.nuFl,
          (S'.withDatum D' hDh).WoneC
              (zeroClass d L N₁' T.m₁ k N ϱ) s x =
            ∑ y, (A₀' ((⟨rawOf D', rawOf_mem_rawSub _⟩ :
                rawSub N S'.G'), g) (s : ℂ)).H y
              ((S'.blockSplit 1 hp').restr x)) ∧
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
(∀ z' : RootIdx d L N₁' T.m₁ (k + 1), z' = boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z → (
        (∀ b, MarkedBlockExpansionDecPair N (stepG d L N₁' T.m₁ k ϱ)
          S'.hG' (((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
          S'.a₁ S'.ν T.BG T.BG₂ T.κ T.t T.t T.κdec p₁
          (S'.blockU z') (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k b)) b (F₁' (z', b)) (Sol' (z', b))) ∧
        (∀ b, (∀ (s : DecParams S'.G') (Dn : BgData S'.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S'.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S'.ν Dn →
          ∀ (φ : S'.G'.Ω 1 × Fin N → ℂ) (α : S'.G'.Ω 1 → ℂ),
            IsDecBg S'.G' (compWeight L S'.a₁) S'.ν (rho4 d L N T.BG T.κ) s Dn φ α →
            (F₁' (z', b)) (s, rawOf Dn) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S'.G') × Edat (stepG d L N₁' T.m₁ k ϱ) N, (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁' T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
            ((Sol' (z', b)) p).1 = dphi (stepG d L N₁' T.m₁ k ϱ) (Dec2.decG (coverOf S'.G') (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol' (z', b)) p).2 ∧
            Dec2.DecFixed (coverOf S'.G') (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν p.1 false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) p.2.2.2.1 p.2.2.2.2) ((Sol' (z', b)) p).2 ∧
            Small (stepG d L N₁' T.m₁ k ϱ) ((Sol' (z', b)) p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁' T.m₁ k ϱ) ((Sol' (z', b)) p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁' T.m₁ k ϱ) ((Sol' (z', b)) p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁' T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁' T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S'.G') (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν p.1 false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = ((Sol' (z', b)) p).2))) ∧
        (∀ (θ : physParam N S') (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S') z'})
          (u : ℂ), DepOn (blocksOf 1 (k + 1) Set.univ i.1)
            (e1MarkGParamG S' (fun b => F₁' (z', b)) (fun b => Sol' (z', b)) p₁ hp' z' T.t θ i u)) ∧
        Nonempty (ParamMarkFamily (S'.blockSplit 1 hp').μ
          (commonLabels Lab₀' (by rwa [hm₀] at h3N' : L ^ 1 ∣ N₁') (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S') (e1DomG_isDj_of_eq T hm₀ Dn hϱ hS')) A₀'
          (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG S') z'} =>
            commonAnchor Lb' (fun _ => Set.univ) (e1DomG S') z' i)
          (fun θ i u Φ => e1MarkGParamG S' (fun b => F₁' (z', b))
            (fun b => Sol' (z', b)) p₁ hp' z' T.t θ i u Φ)
          (2 * T.κdec - 1) (fun _ => corrF0G T k β p₁)
          (physV S' S'.a₁
            S'.ν T.t)
          (Metric.ball (0 : ℂ) (17 / 16 : ℝ)) (physCarrier S' 1 hp')) ∧
        ∃ c' : physParam N S' →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
          (∀ θ C, c' θ C = gsumCoeff (S'.blockSplit 1 hp').μ
            (commonLabels Lab₀' (by rwa [hm₀] at h3N' : L ^ 1 ∣ N₁') (by have := T.hL; omega)
              (fun _ => Set.univ) (e1DomG S') (e1DomG_isDj_of_eq T hm₀ Dn hϱ hS')) (A₀' θ)
            (fun i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1DomG S') z'} =>
              commonAnchor Lb' (fun _ => Set.univ) (e1DomG S') z' i)
            (fun i u Φ => e1MarkGParamG S' (fun b => F₁' (z', b))
              (fun b => Sol' (z', b)) p₁ hp' z' T.t θ i u Φ) C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => c' θ C)
              (physV S' S'.a₁
                S'.ν T.t) ∧
            (∀ θ ∈ physV S' S'.a₁
                S'.ν T.t,
              ∀ θ' ∈ physV S' S'.a₁
                S'.ν T.t,
              physRestrict (N := N) (thickSet S'.G'
                  (Yhat Set.univ (sitesOf C))) (physIncl N S' θ) =
                physRestrict (thickSet S'.G' (Yhat Set.univ (sitesOf C)))
                  (physIncl N S' θ') → c' θ C = c' θ' C) ∧
            (∀ θ ∈ physV S' S'.a₁
                S'.ν T.t,
              ∀ θ' ∈ physV S' S'.a₁
                S'.ν T.t,
              physRestrict (N := N) (sitesOf C) (physIncl N S' θ) =
                physRestrict (sitesOf C) (physIncl N S' θ') →
                c' θ C = c' θ' C) ∧
            (∀ θ ∈ physV S' S'.a₁
                S'.ν T.t,
              ‖c' θ C‖ ≤ K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, c' θ C ≠ 0 → rootCube (m₀ := 1) z' ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C) ∧
              dExt C = sizeJ 1 (k + 1) (sitesOf C))) ∧
          (∀ (D' : BgData S'.G' N)
              (hDh : ∀ y i, D'.h y i = (S'.h₀ i : ℂ)),
            XiCData S'.G' S'.a
              S'.ν (k + 1) 1 T.t D' →
            (S'.withDatum D' hDh).E1locC
                (zeroClass d L N₁' T.m₁ k N ϱ) z' =
              ∑ C, c' ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S'.G'),
                (0 : CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
          ∃ dz' : physParam N S' → Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ (D' : BgData S'.G' N) (hDh : ∀ y i, D'.h y i = (S'.h₀ i : ℂ)),
              XiCData S'.G' S'.a S'.ν (k + 1) 1 T.t D' → ∀ g : Fld d L N₁' T.m₁ (k + 1) N,
              -(1 / 2 : ℂ) * ∑ y ∈ (S'.withDatum D' hDh).blockU z', ∑ i,
                  (S'.withDatum D' hDh).logAC (y, i) (y, i) =
                ∑ C, dz' (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C ∧
              (S'.withDatum D' hDh).E0locC (zeroClass d L N₁' T.m₁ k N ϱ) z' =
                ∑ C, dz' (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C +
                  (S'.withDatum D' hDh).E1locC (zeroClass d L N₁' T.m₁ k N ϱ) z') ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => dz' θ C) (physV S' S'.a₁ S'.ν T.t) ∧
            (∀ θ ∈ physV S' S'.a₁ S'.ν T.t, ∀ θ' ∈ physV S' S'.a₁ S'.ν T.t,
              physRestrict (N := N) (thickSet S'.G' (Yhat Set.univ (sitesOf C))) (physIncl N S' θ) =
                physRestrict (thickSet S'.G' (Yhat Set.univ (sitesOf C))) (physIncl N S' θ') →
                dz' θ C = dz' θ' C) ∧
            (∀ θ ∈ physV S' S'.a₁ S'.ν T.t,
              ‖dz' θ C‖ ≤ ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, dz' θ C ≠ 0 → rootCube (m₀ := 1) z' ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
          ∃ e0' : physParam N S' → Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ,
            (∀ θ C, e0' θ C = dz' θ C + c' θ C) ∧
          (∀ C : Finset (CubeB (d := d) (L := L) (N₁ := N₁') (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e0' θ C) (physV S' S'.a₁ S'.ν T.t) ∧
            (∀ θ ∈ physV S' S'.a₁ S'.ν T.t, ∀ θ' ∈ physV S' S'.a₁ S'.ν T.t,
              physRestrict (N := N) (thickSet S'.G' (Yhat Set.univ (sitesOf C))) (physIncl N S' θ) =
                physRestrict (thickSet S'.G' (Yhat Set.univ (sitesOf C))) (physIncl N S' θ') →
                e0' θ C = e0' θ' C) ∧
            (∀ θ ∈ physV S' S'.a₁ S'.ν T.t,
              ‖e0' θ C‖ ≤ (2 * ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) + 1) * K0 d L T.κ0 * Real.exp (-T.κ' * dExt C)) ∧
            (∀ θ, e0' θ C ≠ 0 → rootCube (m₀ := 1) z' ∈ C ∧ IsPolyDom 1 (k + 1) (sitesOf C))) ∧
            (∀ (D' : BgData S'.G' N) (hDh : ∀ y i, D'.h y i = (S'.h₀ i : ℂ)),
              XiCData S'.G' S'.a S'.ν (k + 1) 1 T.t D' →
              (S'.withDatum D' hDh).E0locC (zeroClass d L N₁' T.m₁ k N ϱ) z' =
                ∑ C, e0' ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N S'.G'),
                  (0 : CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ)) C) ∧
            ∃ E' : DetExpansionLocC S' 1 z' T.t
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
              (∀ D' C, E'.term D' C = ∑ y ∈ S'.blockU z',
                detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D' y C) ∧
              (∀ (D' : BgData S'.G' N), XiCData S'.G' S'.a S'.ν (k + 1) 1 T.t D' →
                ∀ g C, dz' (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C = E'.term D' C) ∧
            ∃ (val' : ((S'.U × Fin N → ℂ) × (S'.U × Fin N → ℂ)) →
                ((S'.U × Fin N → ℂ) × (S'.U × Fin N → ℂ)) → ℂ →
                (RawData d L (N₁' * L ^ T.m₁) (k + 1) N ×
                  (CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ)) → ℂ)
              (I0' : DirectTerms S' 1 hp' (fun ψ => (ψ, ψ)) p₁ 2
                (S'.β * prop33EpsEtaScaled d L N T.m₁ k 1 S'.a₁ T.BG T.BG₂ T.κ T.t
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S'.β))
                (2 * T.κdec - 1)
                (rawOf S'.D', (0 : CTorus d L N₁' T.m₁ (k + 1) → Fin N → ℂ))
                (physSΛEta S' S'.a₁ S'.ν T.t (1 / S'.β))
                (physXW S' (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) 2 2
                  (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁)) val'
                (physAgΘ S') (AgFDirPair S'))
              (hFd' : DirectTermsFamilyOn S' 1 (physInclScaled N S' (((1 / S'.β : ℝ)) : ℂ)) I0'
                (physVq S' S'.a₁ S'.ν T.t 1))
              (hεU' : 0 ≤ S'.β * prop33EpsEtaScaled d L N T.m₁ k 1 S'.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S'.β)),
              Lb' = {Y // Y ∈ I0'.𝒴} ∧ εH' = 2 ^ 2 * (2 * (S'.β * prop33EpsEtaScaled d L N T.m₁ k 1 S'.a₁ T.BG T.BG₂ T.κ T.t
                (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S'.β))) ∧
              HEq Lab₀' (thickLabels I0'.𝒴 I0'.dom) ∧
              HEq A₀' (commonAct (zeroSourceAct
                (labelActFamilyOn S' 1 (physInclScaled N S' (((1 / S'.β : ℝ)) : ℂ)) I0' hFd'
                  (by rwa [hm₀] at h3N' : L ^ 1 ∣ N₁') (by subst hS'; exact hp') (by norm_num) hεU'
                  T.κ0_ent T.marks_K0_le) 2 (by norm_num))
                (by rwa [hm₀] at h3N' : L ^ 1 ∣ N₁') (by have := T.hL; omega)
                (fun _ => Set.univ) (e1DomG S') (e1DomG_isDj_of_eq T hm₀ Dn hϱ hS')
                (mul_nonneg (sq_nonneg 2) (mul_nonneg zero_le_two hεU')) T.κ0_two) ∧
            (I0'.𝒴 = (Finset.univ.biUnion fun z' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) =>
                polyDom S'.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k z')) 1 k
                  (LocalCover.fam 1 (LocalCover.blockSite k z'))) ∪
              (Finset.univ.biUnion fun s : CTorus d L N₁' T.m₁ (k + 1) × Fin N =>
                polyDom S'.G' (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1)) ∧
            ∃ (F₂' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
                  DecParams S'.G' × RawData d L (N₁' * L ^ T.m₁) (k + 1) N → (S'.G'.Ω 1 × Fin N → ℂ) × (S'.G'.Ω 1 → ℂ))
                (Sol₂' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
                  Dec2.DecParams (coverOf S'.G') × Edat (stepG d L N₁' T.m₁ k ϱ) N → ((stepG d L N₁' T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁' T.m₁ k ϱ).Ω 1 → ℂ)),
              (∀ (z' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (s : DecParams S'.G') (Dn : BgData S'.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
                InUnionDomainC S'.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S'.ν Dn → ∀ (φ : S'.G'.Ω 1 × Fin N → ℂ)
                  (α : S'.G'.Ω 1 → ℂ), IsDecBg S'.G' (compWeight L S'.a₁) S'.ν (rho4 d L N T.BG T.κ) s Dn φ α →
                  F₂' z' (s, rawOf Dn) = (φ, α)) ∧
              (∀ (z' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) (p : Dec2.DecParams (coverOf S'.G') × Edat (stepG d L N₁' T.m₁ k ϱ) N), (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
                StrictDataM (stepG d L N₁' T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t))) T.t p.2 →
                  (Sol₂' z' p).1 = dphi (stepG d L N₁' T.m₁ k ϱ) (Dec2.decG (coverOf S'.G') (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν p.1) p.2.2.1 p.2.1
                    (pertSource (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z' p).2 ∧
                  Dec2.DecFixed (coverOf S'.G') (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν p.1 false p.2.2.1 p.2.1
                    (pertSource (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) p.2.2.2.1 p.2.2.2.2) (Sol₂' z' p).2 ∧
                  Small (stepG d L N₁' T.m₁ k ϱ) (Sol₂' z' p).2 (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
                  Small (stepG d L N₁' T.m₁ k ϱ) (Sol₂' z' p).2 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
                  SupBounds (stepG d L N₁' T.m₁ k ϱ) (Sol₂' z' p).1 (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
                  (∀ δα' : (stepG d L N₁' T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁' T.m₁ k ϱ) δα' (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
                    Dec2.DecFixed (coverOf S'.G') (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν p.1 false p.2.2.1 p.2.1
                      (pertSource (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' z' p).2)) ∧
              (∀ (Y : Set (CTorus d L N₁' T.m₁ (k + 1)))
                (x w : (S'.U × Fin N → ℂ) × (S'.U × Fin N → ℂ)) (σ : ℂ)
                (Θ : RawData d L (N₁' * L ^ T.m₁) (k + 1) N),
                I0'.T Y x w σ (Θ, 0) = -(S'.β : ℂ) *
                  ∑ z' : Torus d (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))), if Y ∈ polyDom S'.G'
                      (LocalCover.nbhdF 1 (LocalCover.blockSite k z')) 1 k
                      (LocalCover.fam 1 (LocalCover.blockSite k z')) then
                    rayTerm (dl3 (evTerm
                      (fun i : ParIdx S'.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z')) : Set (CTorus d L N₁' T.m₁ (k + 1))) => i.1.1)
                      S'.G' 1 (X1 S'.G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z')))
                      (fun u s => blockEnergyFun S'.G' (stepG d L N₁' T.m₁ k ϱ) (compWeight L S'.a₁) S'.ν k z'
                        (F₂' z' (extParams S'.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z')) : Set (CTorus d L N₁' T.m₁ (k + 1))) s, u.1))
                        (Sol₂' z' (extParams S'.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z')) : Set (CTorus d L N₁' T.m₁ (k + 1))) s,
                          flEdat S'.G' (stepG d L N₁' T.m₁ k ϱ) (F₂' z' (extParams S'.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z')) : Set (CTorus d L N₁' T.m₁ (k + 1))) s, u.1))
                            u.1.1 (hatPsiF S'.G' S'.a₁ S'.ν S'.hG' ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z')
                              (extParams S'.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z')) : Set (CTorus d L N₁' T.m₁ (k + 1))) s) u.1 u.2))).1
                        (u.1, hatPsiF S'.G' S'.a₁ S'.ν S'.hG' ((S'.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₂' z')
                          (extParams S'.G' (↑(LocalCover.nbhdF 1 (LocalCover.blockSite k z')) : Set (CTorus d L N₁' T.m₁ (k + 1))) s) u.1 u.2)) Y) w.1) taylorWeight x.1 σ Θ
                  else 0) ∧ (∀ {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
                (hrc : L ^ (k + 1) * rc + L ^ (k + 1) ≤ R)
                (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x)
                (hn : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁ * L ^ T.m₁) * L ^ (k + 1))
                (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + T.m₁) + 5 < (N₁' * L ^ T.m₁) * L ^ (k + 1))
                (θ : physParam N S) (θ' : physParam N S')
                (hθ : θ ∈ physV S S.a₁ S.ν T.t) (hθ' : θ' ∈ physV S' S'.a₁ S'.ν T.t)
                (hraw : RawBoxAgree
                  {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ T.m₁) * L ^ (k + 1)) z}
                  (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
                  (θ'.1 : RawData d L (N₁' * L ^ T.m₁) (k + 1) N))
                (Tb : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1
                  (k + 1) Set.univ))
                (hTb : ∀ b ∈ Tb, ∀ x ∈ box b.1 (cellSide L 1 T.m₁ (k + 1)),
                  InBox d R ((N₁ * L ^ T.m₁) * L ^ (k + 1)) x),
                e0' θ' (Tb.image (cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁')
                  (m₁ := T.m₁) (K := k + 1) (m₀ := 1) (by rwa [hm₀] at h3N)
                  (by rwa [hm₀] at h3N') (le_refl (k + 1)))) = e0 θ Tb))))) := by
  classical
  obtain ⟨β₀, h3, H⟩ := e0CoeffFamily_value_fromTowerG_core T hm₀ C hKc hKall hH h0 h' hA p
  refine ⟨β₀, h3, ?_⟩
  intro k hk N₁ N₁' _ _ h3N h3N' hN hN' ν hν0 hν β hβ p₁ hp₁ D Dn ϱ hϱ S hS hp S' hS' hp'
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hz⟩ :=
    H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₁ D hϱ S hS hp
  obtain ⟨F₁', Sol', Lb', hLb', Lab₀', εH', A₀', hα', hzB⟩ :=
    H k hk N₁' h3N' hN' ν hν0 hν β hβ p₁ hp₁ Dn hϱ S' hS' hp'
  subst hϱ
  obtain rfl : S = T.step k hk N₁ ν β p₁ := hS
  obtain rfl : S' = T.step k hk N₁' ν β p₁ := hS'
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, F₁', Sol', Lb', hLb', Lab₀', εH', A₀', hα, hα',
    fun z => ?_⟩
  obtain ⟨hP, hsp, hdp, hfam, c, hc, hC, hcv, dz, hdz1, hdz2, e0, he0, he0b, he0c, E, hEterm,
    hdzE, val, I0, hFd, hεU, hLbI, hεHI, hLabI, hAI, hdom, F₂, Sol₂, hF₂, hSol₂, hT⟩ := hz z
  refine ⟨hP, hsp, hdp, hfam, c, hc, hC, hcv, dz, hdz1, hdz2, e0, he0, he0b, he0c, E, hEterm,
    hdzE, val, I0, hFd, hεU, hLbI, hεHI, hLabI, hAI, hdom, F₂, Sol₂, hF₂, hSol₂, hT, ?_⟩
  intro z' hz'
  subst hz'
  obtain ⟨hP', hsp', hdp', hfam', c', hc', hC', hcv', dz', hdz1', hdz2', e0', he0', he0b', he0c',
    E', hEterm', hdzE', val', I0', hFd', hεU', hLbI', hεHI', hLabI', hAI', hdom', F₂', Sol₂',
    hF₂', hSol₂', hT'⟩ := hzB (boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
      (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z)
  refine ⟨hP', hsp', hdp', hfam', c', hc', hC', hcv', dz', hdz1', hdz2', e0', he0', he0b', he0c',
    E', hEterm', hdzE', val', I0', hFd', hεU', hLbI', hεHI', hLabI', hAI', hdom', F₂', Sol₂',
    hF₂', hSol₂', hT', ?_⟩
  intro rc R hz hrc hroot hn hn' θ θ' hθ hθ' hraw Tb hTb
  have hN1 : L ^ 1 ∣ N₁ := by simpa only [hm₀] using h3N
  have hN1' : L ^ 1 ∣ N₁' := by simpa only [hm₀] using h3N'
  exact coreE0_twoTorus T hm₀ hk hN1 hN1' hN hN' ν hν0.le hν β p₁ D Dn hp hp'
    (F₁ := fun b => F₁ (z, b)) (F₁' := fun b => F₁' (boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
      (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z, b))
    (fun b => (hsp b).1) (fun b => (hsp' b).1)
    (Sol := fun b => Sol (z, b)) (Sol' := fun b => Sol' (boxMap (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))
      (N₁' * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) z, b))
    (fun b => (hsp b).2) (fun b => (hsp' b).2) z hz hrc hroot hn hn' θ θ' hθ hθ' hraw
    (fun i u => hdp θ i u) (fun i u => hdp' θ' i u) Tb hTb hc hc' E E' hEterm hEterm' hdzE hdzE' he0 he0'
    I0 I0' hFd hFd' hεU hεU' hLbI hLbI' hεHI hεHI' hLabI hLabI' hAI hAI' hdom hdom' hF₂ hF₂'
    hSol₂ hSol₂'
    (explicit_evDec_of_core T hk ν β p₁ _ rfl hT) (explicit_evDec_of_core T hk ν β p₁ _ rfl hT')

end Main

end Balaban.Inhabited
