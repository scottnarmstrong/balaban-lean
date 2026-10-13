/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepIdentityFibreFamilies
public import Balaban.Inhabited.RenormPhysicalRecord
public import Balaban.Inhabited.StepIdentityFibreObs
import Balaban.Inhabited.Thm31SiteDomains
import Mathlib.Tactic.Linarith

/-!
# The physical zero-class step, with common coefficient witnesses

The marked energy coefficient and the observable coefficient have exact locality on their
`sitesOf` supports. The determinant coefficient retains collar locality. The identity is an
identity of exponentials on the constant-field fibre.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit Matrix Metric Set MeasureTheory LocalCover

open Classical in
/-- The zero-class family and exponential step identity with one energy family and one
observable family, chosen before the datum and source. The scope is `d=L=3`, `N=2`, the
zero class and the fibre `h=h₀`. The coefficients are indexed by cube sets and regrouped
through `sitesOf`; sources lie in the unit `ℓ¹` ball and the observable rate is
`(3/2)κdec`. This does not assert a local chart, the paper's rotation radius or rates,
reality, symmetry, or nonzero old and boundary channels. -/
theorem zeroClassStep_families_fromTower {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ} (hCR : 0 < CR)
    (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
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
      (∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2) T',
        ∀ θ ∈ physVq (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν T.t q,
          ‖mObs y i θ T'‖ ≤ C * obsPrefactor p s (β * 3 ^ k) *
            Real.exp (-(3 / 2 * T.κdec) * dExt T')) ∧
      (∀ (D' : BgData (T.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
        XiCData (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a
          (T.step k hk N₁ ν β p₁).ν (k + 1) 1 T.t D' →
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, (∑ x, ∑ j, ‖g x j‖) < q →
        ∀ y i, ((T.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i =
          (((T.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            ∑ C₀, mObs y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C₀) ∧
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
  classical
  obtain ⟨βe, hβe3, He⟩ := e0CoeffFamily_value_fromTower T hHull hA p
  obtain ⟨βo, CE, CF, C, hβo3, hCE, hCF, hC0, Ho⟩ :=
    obsFamily_pair_fibre_prefactor_fromTower T hA p hCR hs0 hs
  obtain ⟨βa, hβa3, Ha⟩ := stepIdentity_zeroClass_fibre_local_fromTower T hA p
  refine ⟨max (max βe βo) βa, CE, CF, C,
    hβe3.trans ((le_max_left _ _).trans (le_max_left _ _)), hCE, hCF, hC0, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ q hq0 hq1 D
  have hβe : βe ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ
  have hβo : βo ≤ β := ((le_max_right _ _).trans (le_max_left _ _)).trans hβ
  have hβa : βa ≤ β := (le_max_right _ _).trans hβ
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, hα, hroot⟩ :=
    He k hk N₁ h3N hN ν hνpos hν β hβe p₁ hp hp₁ D
  obtain ⟨Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs, hamp, hsite, hpair⟩ :=
    Ho k hk N₁ h3N hN ν hνpos hν β hβo p₁ hp hp₁ q hq0 hq1 D
      (T.step k hk N₁ ν β p₁) rfl hp
  have hid := Ha k hk N₁ h3N hN ν hνpos hν β hβa p₁ hp hp₁ D
    (T.step k hk N₁ ν β p₁) rfl
  choose hP hF c hc1 hc2 hcv dz hd1 hd2 e0 he0 he2 hev using hroot
  refine ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0, Lbo, hLbo, Labo,
    εHo, hεHo, Ao, mObs, hα,
    (fun z => ⟨hP z, hF z, c z, hc1 z, hc2 z, hcv z, dz z, hd1 z,
      hd2 z, he0 z, he2 z, hev z⟩), hamp, ?_, ?_, ?_, ?_⟩
  · intro y i hdj
    obtain ⟨hR, h1, hθ, Ev, ha, hd, hb, hmk, hcl⟩ := hsite y i hdj
    refine ⟨hR, h1, hθ, Ev, ha, hd, hb, hmk, fun T' => ?_⟩
    exact ⟨(hcl T').1, (hcl T').2.1, (hcl T').2.2.1,
      (hcl T').2.2.2.1, (hcl T').2.2.2.2.1⟩
  · intro y i T' θ hθ
    have hdj : ∀ Y ∈ obsDomains (T.step k hk N₁ ν β p₁)
        (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y :=
      obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ le_rfl
        (D.covers.2 (y, i)).1 (D.covers.2 (y, i)).2.2.1
    obtain ⟨_, _, _, _, _, _, _, _, hcl⟩ := hsite y i hdj
    exact (hcl T').2.2.2.2.2 θ hθ
  · intro D' hDh hX g hg y i
    exact (hpair D' hDh hX g hg).1 y i
  · intro D' hDh hX g hg
    have hg1 : ∑ x, ∑ i, ‖g x i‖ < 1 := lt_of_lt_of_le hg hq1
    rw [hid D' hDh hX g hg1, (hpair D' hDh hX g hg).2,
      Finset.sum_congr rfl fun z _ => hev z D' hDh hX]

open Classical in
/-- The physical zero-class step on site domains. The family witnesses and renormalization
solution are chosen before every constant-field chart datum and source in the unit ball.
The record has the site cover `renYs ∪ sitesOf` and `renDY` distance; its four local
expansion consequences follow with the budgets of `renormPhysicalZero_onFibre_half_consequences_uniform`.
The statement concerns `d=L=3`, `N=2`, the zero class and `h=h₀`; it does not include the
paper's local chart, rotation radius, rates, reality, symmetries, or old and boundary terms. -/
theorem zeroClassStep_sites_fromTower {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF C : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 ≤ C ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
    ∀ p₁ : ℝ, ∀ _hp : 0 < (R.toStepTower.step k hk N₁ ν β p₁).p₁,
      p₁ ≤ pLog A₁ p (β * 3 ^ k) →
    ∀ _Dsc : StepScaleData R.toStepTower k hk N₁ ν β p₁,
    ∀ _Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1)),
    ∃ (cE e0 : RootIdx 3 3 N₁ R.m₁ (k + 1) →
        physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
        Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
      (cM : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 →
        physParam 2 (R.toStepTower.step k hk N₁ ν β p₁) →
        Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
      (F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2 → ℂ) ×
          (((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 → ℂ)),
    (∀ z C₀, AnalyticOnNhd ℂ (fun θ => cE z θ C₀)
      (physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t) ∧
      (∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        ∀ θ' ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
          (R.toStepTower.step k hk N₁ ν β p₁).a₁
          (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        physRestrict (sitesOf C₀) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
          physRestrict (sitesOf C₀) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cE z θ C₀ = cE z θ' C₀) ∧
      (∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        ‖cE z θ C₀‖ ≤ K0 3 3 R.κ0 * Real.exp (-R.toStepTower.κ' * dExt C₀)) ∧
      (∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        cE z θ C₀ ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf C₀))) ∧
    (∀ y i C₀, AnalyticOnNhd ℂ (fun θ => cM y i θ C₀)
      (physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t) ∧
      (∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        ∀ θ' ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
          (R.toStepTower.step k hk N₁ ν β p₁).a₁
          (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        physRestrict (sitesOf C₀) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ) =
          physRestrict (sitesOf C₀) (physIncl 2 (R.toStepTower.step k hk N₁ ν β p₁) θ') →
        cM y i θ C₀ = cM y i θ' C₀) ∧
      (∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        ‖cM y i θ C₀‖ ≤ C * obsPrefactor p s (β * 3 ^ k) *
          Real.exp (-(3 / 2 * R.κdec) * dExt C₀)) ∧
      (∀ θ ∈ physV (R.toStepTower.step k hk N₁ ν β p₁)
        (R.toStepTower.step k hk N₁ ν β p₁).a₁
        (R.toStepTower.step k hk N₁ ν β p₁).ν R.t,
        cM y i θ C₀ ≠ 0 → IsPolyDom 1 (k + 1) (sitesOf C₀))) ∧
    IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν
      (R.t / 2) (R.t / 2) R.r₀ (8 * (R.t / 2)) F ∧
    (∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < 1 →
      RenormExpInputOn (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
        R.r₀ (renCK 3 3 2 R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) =>
          blockSites 3 3 N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min R.toStepTower.κ' (3 / 2 * R.κdec))) (min (3 / 2 * R.κdec) (min R.toStepTower.κ' (3 / 2 * R.κdec))) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + K0 3 3 R.κ0)
        0 (C * obsPrefactor p s (β * 3 ^ k)) 0 (fun (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) (fun _ _ _ => 0) (fun (p : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2) (ξ : Fin 3 → ℂ) =>
          if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) p.2
          else 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ))
    ) ∧
    (∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < 1 →
      (∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min R.toStepTower.κ' (3 / 2 * R.κdec)))
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min R.toStepTower.κ' (3 / 2 * R.κdec)))
          (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * (R.t / 2)) +
            renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z)))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min R.toStepTower.κ' (3 / 2 * R.κdec)))
          ((hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)) + K0 3 3 R.κ0))
          (fun D ξ => if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
            (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).E0locC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z else 0) term)) ∧
      ∀ (pt : ((lvTop N₁ R.m₁ k (rhoSep R.m₁))).Ω 1 × Fin 2) (εR : ℝ), εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (pt.1 : CTorus 3 3 N₁ R.m₁ (k + 1))))) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (pt.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))) ∪ (Finset.univ.image fun T : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus 3 3 N₁ R.m₁ (k + 1) => x ∈ sitesOf T)))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (min (3 / 2 * R.κdec) (min R.toStepTower.κ' (3 / 2 * R.κdec)))
          ((C * obsPrefactor p s (β * 3 ^ k)) + 1 * (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) * εR ^ 1)
          (fun D ξ => (if hD : ∀ x i, D.h x i = ((((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ)) : ℂ)
          then (((((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ)))⁻¹ *
            ((R.toStepTower.step k hk N₁ ν β p₁).withDatum
              (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ) hD).M0C
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g (pt.1 : CTorus 3 3 N₁ R.m₁ (k + 1)) pt.2
          else 0) + (F ((D.Ψ, D.h), ξ)).1 pt) term)
    ) ∧

    (∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G'
        (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      (∀ z, ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
        (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
        ∑ C₀, e0 z (⟨rawOf D', rawOf_mem_rawSub _⟩,
          (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C₀) ∧
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ i, ‖g x i‖) < 1 →
        ∀ y i, ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
          (((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            ∑ C₀, cM y i (⟨rawOf D', rawOf_mem_rawSub _⟩, g) C₀) ∧
    (∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
        (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
      XiCData (R.toStepTower.step k hk N₁ ν β p₁).G'
        (R.toStepTower.step k hk N₁ ν β p₁).a
        (R.toStepTower.step k hk N₁ ν β p₁).ν (k + 1) 1 R.t D' →
      (∀ z, ∃ eY : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) → ℂ,
        ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).E0locC
          (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) z =
          ∑ Y ∈ Finset.univ.image (fun C₀ : Finset (CubeB (d := 3) (L := 3)
            (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) => sitesOf C₀), eY Y ∧
        (∀ Y, eY Y ≠ 0 → IsDj 1 (k + 1) Y ∧
          box (rootCube (m₀ := 1) (K := k + 1) z).1
            (cellSide 3 1 R.m₁ (k + 1)) ⊆ Y) ∧
        ∀ Y, ‖eY Y‖ ≤
          ((2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 R.κ /
            (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) + 1) *
            K0 3 3 R.κ0) * Real.exp (-R.toStepTower.κ' * sizeJ 1 (k + 1) Y)) ∧
      ∀ (g : Fld 3 3 N₁ R.m₁ (k + 1) 2), (∑ x, ∑ j, ‖g x j‖) < 1 →
        ∀ y i, ∃ mY : Set (CTorus 3 3 N₁ R.m₁ (k + 1)) → ℂ,
          ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).M0C
            (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g y i =
            (((R.toStepTower.step k hk N₁ ν β p₁).betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
              ∑ Y ∈ Finset.univ.image (fun C₀ : Finset (CubeB (d := 3) (L := 3)
                (N₁ := N₁) (m₁ := R.m₁) (K := k + 1) 1 (k + 1) Set.univ) => sitesOf C₀), mY Y ∧
          (∀ Y, mY Y ≠ 0 → IsDj 1 (k + 1) Y ∧
            box (rootCube (m₀ := 1) (K := k + 1) (blockIndex y)).1
              (cellSide 3 1 R.m₁ (k + 1)) ⊆ Y) ∧
          ∀ Y, ‖mY Y‖ ≤ C * obsPrefactor p s (β * 3 ^ k) *
            Real.exp (-(3 / 2 * R.κdec) * sizeJ 1 (k + 1) Y)) ∧
      ∀ (D' : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2)
          (hDh : ∀ y i, D'.h y i = ((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℂ)),
        XiCData (R.toStepTower.step k hk N₁ ν β p₁).G' (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (k + 1) 1 R.t D' →
        ∀ g : Fld 3 3 N₁ R.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).TstepC
              (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) g =
            Complex.exp (-((R.toStepTower.step k hk N₁ ν β p₁).β : ℂ) *
                ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).AnewC -
              (((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).Eppp
                  (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)) : ℂ) *
                (((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).nU : ℂ) +
              FcompAtC (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)).m₀
                (zeroClass 3 3 N₁ R.m₁ k 2 (rhoSep R.m₁)).Tm (R.toStepTower.step k hk N₁ ν β p₁).a
                    (R.toStepTower.step k hk N₁ ν β p₁).ν (Nat.le_succ k)
                ((R.toStepTower.step k hk N₁ ν β p₁).withDatum D' hDh).psiKdC g +
              ∑ z : RootIdx 3 3 N₁ R.m₁ (k + 1), ∑ C,
                e0 z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 (R.toStepTower.step k hk N₁ ν β p₁).G'),
                  (0 : CTorus 3 3 N₁ R.m₁ (k + 1) → Fin 2 → ℂ)) C +
              ∑ y : CTorus 3 3 N₁ R.m₁ (k + 1), ∑ i : Fin 2, g y i *
                ∑ C', cM y i ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2
                    (R.toStepTower.step k hk N₁ ν β p₁).G'), g) C') := by
  let T := R.toStepTower
  have hHull : stepHullMin ≤ κmin := stepHullMin_le_renDetFibreMin.trans hR
  obtain ⟨β₀, CE, CF, C, h3, hCE, hCF, hC, H⟩ :=
    zeroClassStep_families_fromTower T hHull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, C, h3, hCE, hCF, hC, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp hp₁ Dsc Xcut
  obtain ⟨F₁, Sol, Lb, hLb, Lab₀, εH, A₀, e0,
    Lbo, hLbo, Labo, εHo, hεHo, Ao, mObs,
    hα, hroot, hamp, hsite, hpref, hvalM, hid⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp hp₁ 1 one_pos le_rfl Dsc
  choose hP hF c hc1 hc2 hcv dz hd1 hd2 he0 he2 hev using hroot
  have hdj : ∀ (y : CTorus 3 3 N₁ R.m₁ (k + 1)) (i : Fin 2),
      ∀ Y ∈ obsDomains (T.step k hk N₁ ν β p₁)
        (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y := by
    intro y i
    exact obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ le_rfl
      (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1
  choose hRg hRg1 hRgθ Ev hEvA hEvL hEvB hmk hcl using fun y i => hsite y i (hdj y i)
  have hB : 0 ≤ K0 3 3 R.κ0 := (T.marks_K0_pos).le
  have hβpos : 0 < β := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3) (h3.trans hβ)
  have hβ1 : 1 ≤ β * 3 ^ k := by
    have hpow : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hBM : 0 ≤ C * obsPrefactor p s (β * 3 ^ k) :=
    mul_nonneg hC (obsPrefactor_nonneg p s hβ1)
  obtain ⟨F, Fcut, hFsol, hFcutAn, hFcutEq, hRecord⟩ :=
    renormPhysicalZero_onFibre_half_uniform R hR k hk N₁ h3N hN hνpos.le hν β p₁
      hβpos Xcut 1 le_rfl hB hBM c mObs
      (fun z C₀ => (hc2 z C₀).1)
      (fun z C₀ θ hθ θ' hθ' hrestr =>
        (hc2 z C₀).2.2.1 θ hθ θ' hθ' hrestr)
      (fun z θ hθ C₀ _ => (hc2 z C₀).2.2.2.1 θ hθ)
      (fun z θ _ C₀ hne => ((hc2 z C₀).2.2.2.2 θ hne).2.1)
      (fun z D' hDh hX => hcv z D' hDh hX)
      (fun y i C₀ => by simpa only [physVq_one] using (hcl y i C₀).1)
      (fun y i C₀ θ hθ θ' hθ' hrestr => by
        exact (hcl y i C₀).2.2.2.2 θ
          (by simpa only [physVq_one] using hθ) θ'
          (by simpa only [physVq_one] using hθ') hrestr)
      (fun y i θ hθ C₀ _ => hpref y i C₀ θ
        (by simpa only [physVq_one] using hθ))
      (fun y i θ hθ C₀ hne => ((hcl y i C₀).2.2.1 θ
        (by simpa only [physVq_one] using hθ) hne).2)
      (fun g hg y i D' hDh hX => hvalM D' hDh hX g hg y i)
  have he : 0 < R.t / 2 := by
    have ht := R.t_pos
    positivity
  have het : R.t / 2 ≤ R.t := by linarith [R.t_pos]
  have hCore := R.flCore_scale_mono k hk N₁ hN hνpos.le hν he het he het
  have hHB := bgHyp_lv (k := k) R.m₁ hνpos.le hν
  have hcK := R.toStepTowerRen.renCK_facts.1
  have hr := R.r₀_pos
  refine ⟨c, e0, mObs, F, ?_, ?_, hFsol, hRecord, ?_, ?_, ?_, hid⟩
  · intro z C₀
    exact ⟨(hc2 z C₀).1, (hc2 z C₀).2.2.1,
      (hc2 z C₀).2.2.2.1,
      fun θ _ hne => ((hc2 z C₀).2.2.2.2 θ hne).2.1⟩
  · intro y i C₀
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [physVq_one] using (hcl y i C₀).1
    · intro θ hθ θ' hθ' hrestr
      exact (hcl y i C₀).2.2.2.2 θ
        (by simpa only [physVq_one] using hθ) θ'
        (by simpa only [physVq_one] using hθ') hrestr
    · intro θ hθ
      exact hpref y i C₀ θ (by simpa only [physVq_one] using hθ)
    · intro θ hθ hne
      exact ((hcl y i C₀).2.2.1 θ
        (by simpa only [physVq_one] using hθ) hne).2
  · intro g hg
    have I := hRecord g hg
    refine ⟨fun z εR hεR0 hεR => ⟨?_, ?_, ?_⟩, fun p εR hεR => ?_⟩
    · exact thm31g_C1_on hHB he hCore.small1
        (hCore.c7le.trans (c7_le_bgC1 3 3 2 R.BG R.κ)) R.r₀_le I
        zero_le_one hcK hεR z
    · exact thm31g_C2_on hHB he R.r₀_le I zero_le_one
        (by positivity) hcK hεR0 hεR z
    · exact thm31g_Eu_zero_of_fields_on I hr hεR z
    · exact thm31h_zero_of_fields_on I zero_le_one (by positivity) hcK hr hεR p
  · intro D' hDh hX
    exact ⟨fun z => hev z D' hDh hX,
      fun g hg y i => hvalM D' hDh hX g hg y i⟩
  · intro D' hDh hX
    have hg0 : (∑ x, ∑ j, ‖(0 : Fld 3 3 N₁ R.m₁ (k + 1) 2) x j‖) < 1 := by simp
    have hθ0 : ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2
        (T.step k hk N₁ ν β p₁).G'), (0 : Fld 3 3 N₁ R.m₁ (k + 1) 2)) ∈
        physV (T.step k hk N₁ ν β p₁) (T.step k hk N₁ ν β p₁).a₁
          (T.step k hk N₁ ν β p₁).ν R.t :=
      ⟨⟨D', hX, rfl⟩, hg0⟩
    refine ⟨fun z => ?_, fun g hg y i => ?_⟩
    · let θ : physParam 2 (T.step k hk N₁ ν β p₁) :=
        (⟨rawOf D', rawOf_mem_rawSub _⟩, (0 : Fld 3 3 N₁ R.m₁ (k + 1) 2))
      have hθ : θ ∈ physV (T.step k hk N₁ ν β p₁)
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν R.t := hθ0
      let BE : ℝ := ((2 * (3 : ℝ) ^ 3 * (covBLogMax 3 3 R.κ /
          (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) + 1) *
            K0 3 3 R.κ0)
      have hBE : 0 ≤ BE := by
        have h0 := (norm_nonneg (e0 z θ ∅)).trans ((he2 z ∅).2.2.1 θ hθ)
        exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).1 h0
      obtain ⟨eY, _, _, hsum, hsupp, hbound⟩ :=
        sitesOf_regroup (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1)
          (m₀ := 1) (by simpa using h3N) (fun C₀ => e0 z θ C₀)
          BE T.κ' hBE (rootCube z)
          (fun C₀ _ => (he2 z C₀).2.2.1 θ hθ)
          (fun C₀ hne =>
            ⟨((he2 z C₀).2.2.2 θ hne).2, ((he2 z C₀).2.2.2 θ hne).1⟩)
      exact ⟨eY, (hev z D' hDh hX).trans hsum, hsupp, hbound⟩
    · let θ : physParam 2 (T.step k hk N₁ ν β p₁) :=
        (⟨rawOf D', rawOf_mem_rawSub _⟩, g)
      have hθ : θ ∈ physV (T.step k hk N₁ ν β p₁)
          (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν R.t :=
        ⟨⟨D', hX, rfl⟩, hg⟩
      obtain ⟨mY, _, _, hsum, hsupp, hbound⟩ :=
        sitesOf_regroup (L := 3) (N₁ := N₁) (m₁ := R.m₁) (K := k + 1)
          (m₀ := 1) (by simpa using h3N) (fun C₀ => mObs y i θ C₀)
          (C * obsPrefactor p s (β * 3 ^ k)) (3 / 2 * T.κdec) hBM
          (rootCube (blockIndex y))
          (fun C₀ _ => hpref y i C₀ θ
            (by simpa only [physVq_one] using hθ))
          (fun C₀ hne =>
            have h := (hcl y i C₀).2.2.1 θ
              (by simpa only [physVq_one] using hθ) hne
            ⟨h.2, h.1⟩)
      refine ⟨mY, ?_, hsupp, hbound⟩
      rw [hvalM D' hDh hX g hg y i, hsum]

end Balaban.Inhabited
