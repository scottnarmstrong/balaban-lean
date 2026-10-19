/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyTower
public import Balaban.Inhabited.StepTowerBeta0Class

/-!
The class chain with the label families general at every tower radius, with the spin covariance of its family

`e0CoeffFamily_class_fromTower_of_labels_gen_onSet_agree_pad_rot`: the statement of
`e0CoeffFamily_class_fromTower_of_labels_gen_onSet_agree_pad` with the covariance conjunct of
`e0CoeffFamily_class_fromTower_agree_rot`; the landed theorem is its corollary.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The class chain with the labels' marks, with the formula of its family.**  The statement of
`StepTowerG.e0CoeffFamily_class_of_labels_gen_onSet_agree_pad_rot` with the two conjuncts of
`StepTowerG.e0CoeffFamily_class_agree_rot_formula`: the defining properties of the decoupling pairs
`F₁ (z, b)`, `Sol (z, b)` of the bridge marks, and `e = newLevelDetBg S.G' … (S.blockU z) + c` on the
step chart, `c` the interpolation coefficient of the first conjunct. -/
theorem StepTowerG.e0CoeffFamily_class_of_labels_gen_onSet_agree_pad_rot_formula {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin)
    (hm₀ : T₀.m₀ = 1) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, ∀ hm₀T : T.m₀ = T₀.m₀, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (Dt : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
        (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
      -- the defining properties of the decoupling pairs of the marks
      (∀ (z : RootIdx d L N₁ T.m₁ (k + 1)) b,
        (∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N T.BG T.κ) S.ν D →
          ∀ (φ : S.G'.Ω 1 × Fin N → ℂ) (α : S.G'.Ω 1 → ℂ),
            IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N T.BG T.κ) s D φ α →
            (F₁ (z, b)) (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N,
          (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N T.BG T.κ * (xiC1 d * T.t)))
            T.t p.2 →
          ((Sol (z, b)) p).1 = dphi (stepG d L N₁ T.m₁ k ϱ) (Dec2.decG (coverOf S.G')
              (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1) p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2)
              ((Sol (z, b)) p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2)
              ((Sol (z, b)) p).2 ∧
            Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2
              (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).2
              (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) ((Sol (z, b)) p).1
              (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ T.m₁ k ϱ) δα'
                (c6' d L N (famConst d L T.BG₂ T.κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' →
              δα' = ((Sol (z, b)) p).2))) ∧
      -- the locality of the bridge marks: the mark of the bridge `i` depends only on its blocks
      (∀ (z : RootIdx d L N₁ T.m₁ (k + 1)) (θ : physParam N S)
          (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z}) (u : ℂ),
        DepOn (blocksOf 1 (k + 1) Set.univ i.1)
          (e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b)) p₁ hp z T.t θ i u)) ∧
      ∀ (Jr : S.JointRep T.t (2 * p₁)) (C : StepClass d L N₁ T.m₁ k N ϱ)
        (z : RootIdx d L N₁ T.m₁ (k + 1)) (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb)
        (εH κH Kc : ℝ)
        (A : physParam N S → ℂ →
          LabelAct (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS))
            (S.blockSplit 1 hp).Ωb εH κH T.κ0 Kc)
        (ι : Type) [Fintype ι] {m₀ : ℕ} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (hb₁ : 1 ≤ bL) (hbC : bL ≤ scaledC0 d)
        (Eτ : ι → RawData d L (N₁ * L ^ T.m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
        (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
        (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
        (Gk : ι → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) (ϱ))
        (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
          Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
        (X₀ X₁f : ι → Finset (CTorus d L N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (hcψ : 0 ≤ cψ)
        (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ T.m₁) {δc : ℝ}
        (hdm : decDomMargin d L N BG κ (xiC1 d * T.t) < δc)
        (hα : K4 d L N BG κ * (xiC1 d * T.t) < coerciveConst d / 2)
        (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
        (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
        (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
        (hconn : HatConn S.G')
        (hrow : RowInHat (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν)
        (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
            bondCost (scaleW L m₀ T.m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
        {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
        (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
        (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        {𝒮 : ι → Set (RawData d L (N₁ * L ^ T.m₁) (k + 1) N)}
        (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
        (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
          ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
        (F₁L : ι → DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (hSolan : ∀ τ, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2})
        (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k
            (ϱ)) N,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG d L N₁ T.m₁ k ϱ)
                (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2
              (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2 (cK2' d L N (famConst d L BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).1
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ,
              Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (hFkan : ∀ τ, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) N,
          InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
        (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
            bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
        (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        (hSg : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
          (Gj τ))
        (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
        (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * T.t))) + 5 * (R * δ₁) ≤ bgC1 d L N)
        (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
        (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
          c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < 2 * p₁)
        (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀)
        {bb : ℝ} (hbb : 0 < bb)
        (hab : (corrU + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam N S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ T.m₁ k
                  (ϱ))
                (compWeight L S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (hρp : S.p₁ ≤ ρ)
        (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
          Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
        (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 (fun _ =>
              Set.univ) (e1DomG S))
        (hy1 : ∀ q, (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).ysite (y1 q) = bridge 1 z
                q.1.2)
        (pad : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ) (hpad : ∀ q, 0 < pad q),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- (M1) the activity family of the class
      (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
        (fun r : physParam N S × ℂ => (A r.1 r.2).H y Φ)
        (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) →
      (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
        ContinuousOn ((A θ u).H y) (physCarrier S 1 hp)) →
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
        DifferentiableOn ℂ (fun u => (A θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) →
      (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
          physRestrict (sitesOf T') (physIncl N S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
          (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).ysite y ⊆
            Yhat Set.univ (sitesOf T') →
          (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y) →
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          Jr.W1 C (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
            ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
              (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) →
      -- the constants of the class activity and of the inherited marks
      0 < εH → K0 d L T.κ0 + 1 ≤ Kc → κH ≤ 2 * T.κdec - 1 →
      T.κ' + 3 * T.κ0 + c1 d L + 3 / 2 ≤ κH →
      εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
        Real.exp ((κH - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) →
      ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ,
        (∀ q, F1 q = (‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) * Real.exp (-κ₀ *
          treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) - 2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb) +
          pad q) * Real.exp ((2 * T.κdec - 1) * (commonLabels Lab
          (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
          (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).dl (y1 q))) ∧
        -- the locality of the marks: the mark of `q` depends only on the blocks of its bridge
        (∀ θ q u, DepOn (blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) (G₁ θ q u)) ∧
        ∃ c e : physParam N S → Finset
              (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
        (∀ θ T', c θ T' = gsumCoeff (S.blockSplit 1 hp).μ
          (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)) (A θ)
          (Sum.elim (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z) y1)
          (Sum.elim (fun i u Φ => e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u Φ) (G₁ θ)) T') ∧
        -- the family is the determinant part plus `c` on the step chart
        (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ T',
          e θ T' = newLevelDetBg S.G' (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) (S.blockU z) θ T' +
            c θ T') ∧
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          (AnalyticOnNhd ℂ (fun θ => c θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                physRestrict (sitesOf T') (physIncl N S θ') → c θ T' = c θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖c θ T'‖ ≤
              CPE d L Kc κH T.κ0 T.κ' *
                ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
                    corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                  ∑ j, F1 j * Real.exp (-T.κ0 *
                    (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                      (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).dl (y1 j))) *
                Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, c θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T') ∧
              dExt T' = sizeJ 1 (k + 1) (sitesOf T'))) ∧
          (AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                  (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
              e θ T' = e θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
              (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) *
                  Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                    dExt T') +
                CPE d L Kc κH T.κ0 T.κ' *
                  ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
                      corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                    ∑ j, F1 j * Real.exp (-T.κ0 *
                      (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                        (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).dl (y1 j))) *
                  Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E1locJ C z (rawOf D) = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E1locH C z = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        (∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)) ∧
        -- the spin covariance of `e` from that of the activity `A` and the marks `G₁`
        ((∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ∀ Φ ∈ physCarrier S 1 hp,
            (A θ' (s : ℂ)).H y (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) =
              (A θ (s : ℂ)).H y Φ) →
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j, ∀ Φ ∈ physCarrier S 1 hp,
            G₁ θ' j (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G₁ θ j (s : ℂ) Φ) →
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') := by
  obtain ⟨β₀, hβ₀, H⟩ := StepTowerG.e0CoeffFamily_class_agree_rot_formula T₀ hm₀ hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ => ?_⟩
  have hmT : T.m₀ = 1 := hm₀T.trans hm₀
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp₁ Dt ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, hpin, hbrdep, H'⟩ := H T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁ hp₁ Dt hϱ S hS hp
  refine ⟨F₁, Sol, hpin, hbrdep, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ
    hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow
    hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk
    h𝒮 hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1 pad hpad
    hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε
  obtain ⟨F1, hF1eq, hF1, hmeas, hdep, hbd, hhol, hcont, hdiff, hloc, hroot, hid⟩ :=
    Jr.classMarks_M2_of_family_gen_onSet_pad (h𝒮 := h𝒮)
        C hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB
      hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁L hF₁an hF₁
      SolL hSolan hSolprop FkL hFkan hFk (fun τ => hSg τ ((hjk τ).trans (Nat.le_succ k))) hc7 hR
      hsmR hRs hsmall hnum hnum' hN hm1 T.hd
      (by have := T.hL; omega) z hρ hρc hρpp hp (by norm_num [corrU]) hbb hab G₁ hG₁ hEJ hρp hE Lab
      (fun _ => Set.univ) (e1DomG S)
      (by rwa [hmT] at h3N) (e1DomG_isDj_of_eq T hmT Dt hϱ hS) y1 hy1 (2 * T.κdec - 1) pad hpad
  exact ⟨F1, hF1eq, fun θ q u => hy1 q ▸ hdep θ q u, H' Jr C z Lb Lab εH κH Kc A _ y1 G₁ F1 hE
    hAhol hAcont hAdiff hAloc hW hmeas hdep hbd
    hhol hcont hdiff (fun T' θ hθ θ' hθ' hres s hs j hsub => hloc _ θ hθ θ' hθ' hres s hs j hsub)
    hroot hid hF1 hεpos hKc hκG hκH hε⟩


open Classical in
/-- **The agree version of the class chain with the labels' marks, with the spin covariance of the family.**  The statement of `e0CoeffFamily_class_fromTower_of_labels_gen_onSet_agree_pad` with the covariance conjunct of `e0CoeffFamily_class_fromTower_agree_rot`. -/
theorem StepTowerG.e0CoeffFamily_class_of_labels_gen_onSet_agree_pad_rot {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin)
    (hm₀ : T₀.m₀ = 1) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, ∀ hm₀T : T.m₀ = T₀.m₀, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (Dt : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
        (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
            (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) ×
          Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
              ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ)),
      ∀ (Jr : S.JointRep T.t (2 * p₁)) (C : StepClass d L N₁ T.m₁ k N ϱ)
        (z : RootIdx d L N₁ T.m₁ (k + 1)) (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb)
        (εH κH Kc : ℝ)
        (A : physParam N S → ℂ →
          LabelAct (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS))
            (S.blockSplit 1 hp).Ωb εH κH T.κ0 Kc)
        (ι : Type) [Fintype ι] {m₀ : ℕ} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (hb₁ : 1 ≤ bL) (hbC : bL ≤ scaledC0 d)
        (Eτ : ι → RawData d L (N₁ * L ^ T.m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
        (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
        (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
        (Gk : ι → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) (ϱ))
        (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
          Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
        (X₀ X₁f : ι → Finset (CTorus d L N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (hcψ : 0 ≤ cψ)
        (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ T.m₁) {δc : ℝ}
        (hdm : decDomMargin d L N BG κ (xiC1 d * T.t) < δc)
        (hα : K4 d L N BG κ * (xiC1 d * T.t) < coerciveConst d / 2)
        (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
        (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
        (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
        (hconn : HatConn S.G')
        (hrow : RowInHat (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν)
        (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
            bondCost (scaleW L m₀ T.m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
        {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
        (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
        (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        {𝒮 : ι → Set (RawData d L (N₁ * L ^ T.m₁) (k + 1) N)}
        (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
        (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
          ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
        (F₁L : ι → DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (hSolan : ∀ τ, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2})
        (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ T.m₁ k
            (ϱ)) N,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG d L N₁ T.m₁ k ϱ)
                (Dec2.decG (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2
              (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2 (cK2' d L N (famConst d L BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).1
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ,
              Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (hFkan : ∀ τ, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) N,
          InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
        (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
            bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
        (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        (hSg : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
          (Gj τ))
        (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
        (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * T.t))) + 5 * (R * δ₁) ≤ bgC1 d L N)
        (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
        (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
          c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < 2 * p₁)
        (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀)
        {bb : ℝ} (hbb : 0 < bb)
        (hab : (corrU + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam N S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ T.m₁ k
                  (ϱ))
                (compWeight L S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (hρp : S.p₁ ≤ ρ)
        (hEJ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
          Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
        (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 (fun _ =>
              Set.univ) (e1DomG S))
        (hy1 : ∀ q, (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).ysite (y1 q) = bridge 1 z
                q.1.2)
        (pad : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ) (hpad : ∀ q, 0 < pad q),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- (M1) the activity family of the class
      (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
        (fun r : physParam N S × ℂ => (A r.1 r.2).H y Φ)
        (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) →
      (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
        ContinuousOn ((A θ u).H y) (physCarrier S 1 hp)) →
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
        DifferentiableOn ℂ (fun u => (A θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) →
      (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
          physRestrict (sitesOf T') (physIncl N S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
          (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).ysite y ⊆
            Yhat Set.univ (sitesOf T') →
          (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y) →
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          Jr.W1 C (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
            ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
              (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) →
      -- the constants of the class activity and of the inherited marks
      0 < εH → K0 d L T.κ0 + 1 ≤ Kc → κH ≤ 2 * T.κdec - 1 →
      T.κ' + 3 * T.κ0 + c1 d L + 3 / 2 ≤ κH →
      εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
        Real.exp ((κH - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) →
      ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ,
        (∀ q, F1 q = (‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) * Real.exp (-κ₀ *
          treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) - 2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb) +
          pad q) * Real.exp ((2 * T.κdec - 1) * (commonLabels Lab
          (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega) (fun _ => Set.univ) (e1DomG S)
          (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).dl (y1 q))) ∧ ∃ c e : physParam N S → Finset
              (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
        (∀ θ T', c θ T' = gsumCoeff (S.blockSplit 1 hp).μ
          (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
            (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)) (A θ)
          (Sum.elim (commonAnchor Lb (fun _ => Set.univ) (e1DomG S) z) y1)
          (Sum.elim (fun i u Φ => e1MarkGParamG S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u Φ) (G₁ θ)) T') ∧
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          (AnalyticOnNhd ℂ (fun θ => c θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (sitesOf T') (physIncl N S θ) =
                physRestrict (sitesOf T') (physIncl N S θ') → c θ T' = c θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖c θ T'‖ ≤
              CPE d L Kc κH T.κ0 T.κ' *
                ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
                    corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                  ∑ j, F1 j * Real.exp (-T.κ0 *
                    (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                      (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).dl (y1 j))) *
                Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, c θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T') ∧
              dExt T' = sizeJ 1 (k + 1) (sitesOf T'))) ∧
          (AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := N) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                  (physIncl N S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl N S θ') →
              e θ T' = e θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
              (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) *
                  Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                    dExt T') +
                CPE d L Kc κH T.κ0 T.κ' *
                  ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG S) z},
                      corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                    ∑ j, F1 j * Real.exp (-T.κ0 *
                      (commonLabels Lab (by rwa [hm₀T.trans hm₀] at h3N : L ^ 1 ∣ N₁) (by have := T.hL; omega)
                        (fun _ => Set.univ) (e1DomG S) (e1DomG_isDj_of_eq T (hm₀T.trans hm₀) Dt hϱ hS)).dl (y1 j))) *
                  Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E1locJ C z (rawOf D) = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E1locH C z = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        (∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)) ∧
        -- the spin covariance of `e` from that of the activity `A` and the marks `G₁`
        ((∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ∀ Φ ∈ physCarrier S 1 hp,
            (A θ' (s : ℂ)).H y (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) =
              (A θ (s : ℂ)).H y Φ) →
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j, ∀ Φ ∈ physCarrier S 1 hp,
            G₁ θ' j (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G₁ θ j (s : ℂ) Φ) →
        ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') := by
  obtain ⟨β₀, hβ₀, H⟩ :=
    StepTowerG.e0CoeffFamily_class_of_labels_gen_onSet_agree_pad_rot_formula T₀ hm₀ hA p hcR hαR
  refine ⟨β₀, hβ₀, ?_⟩
  intro T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp₁ Dt ϱ hϱ S hS hp
  obtain ⟨F₁, Sol, -, -, H'⟩ := H T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁
    hp₁ Dt hϱ S hS hp
  refine ⟨F₁, Sol, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ
    hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow
    hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk
    h𝒮 hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1
    pad hpad hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε
  obtain ⟨F1, hF1eq, -, c, e, hc, -, he⟩ := @H' Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ
    hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow
    hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk
    h𝒮 hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1
    pad hpad hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε
  exact ⟨F1, hF1eq, c, e, hc, he⟩

open Classical in
/-- **The agree version of the class chain with the labels' marks, with the spin covariance of the family.**  The statement of `e0CoeffFamily_class_fromTower_of_labels_gen_onSet_agree_pad` with the covariance conjunct of `e0CoeffFamily_class_fromTower_agree_rot`. -/
theorem e0CoeffFamily_class_fromTower_of_labels_gen_onSet_agree_pad_rot {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (Dt : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (hS : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ (F₁ : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
          Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
            (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (Sol : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) ×
          Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))) →
          Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
              ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ)),
      ∀ (Jr : S.JointRep T.t (2 * p₁)) (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (z : RootIdx 3 3 N₁ T.m₁ (k + 1)) (Lb : Type) [Fintype Lb]
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb)
        (εH κH Kc : ℝ)
        (A : physParam 2 S → ℂ →
          LabelAct (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS))
            (S.blockSplit 1 hp).Ωb εH κH T.κ0 Kc)
        (ι : Type) [Fintype ι] {m₀ : ℕ} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (hb₁ : 1 ≤ bL) (hbC : bL ≤ scaledC0 3)
        (Eτ : ι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ) (Bτ : ι → ℝ)
        (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
        (jL : ι → ℕ) (XL : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
        (Gk : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
          Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
        (X₀ X₁f : ι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (hB : ∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (hF : ∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (hcψ : 0 ≤ cψ)
        (hMX : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (hα : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
        (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
        (hconn : HatConn S.G')
        (hrow : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 m₀ T.m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
        {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
        (hκ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
        (hlog : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        {𝒮 : ι → Set (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)}
        (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
        (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
          ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
        (F₁L : ι → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (hSolan : ∀ τ, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
            (rhoSep T.m₁)) 2,
          (∀ P, ‖p.1 P‖ < Real.exp κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2 →
            (SolL τ p).1 = dphi (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                (Dec2.decG (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                    S.ν p.1)
                p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2)
                (SolL τ p).2 ∧
            Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                S.ν p.1
              false p.2.2.1 p.2.1
              (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                  p.2.2.2.2)
              (SolL τ p).2 ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2
              (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2 (cK2' 3 3 2 (famConst 3 3 BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).1
              (cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ,
              Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1
                  3 / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (hFkan : ∀ τ, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (hFk : ∀ τ, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        (hSg : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
          (Gj τ))
        (hc7 : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (hR : 2 ≤ R)
        (hsmR : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (hRs : R * δ₁ ≤ deltaStar 3 3 2) (hsmall : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (hnum : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (hnum' : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < 2 * p₁)
        (hN : 3 ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀)
        {bb : ℝ} (hbb : 0 < bb)
        (hab : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (hρp : S.p₁ ≤ ρ)
        (hEJ : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
          Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
        (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 (fun _ =>
              Set.univ) (e1Dom S))
        (hy1 : ∀ q, (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite (y1 q) = bridge 1 z
                q.1.2)
        (pad : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ) (hpad : ∀ q, 0 < pad q),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- (M1) the activity family of the class
      (∀ y, ∀ Φ ∈ physCarrier S 1 hp, AnalyticOnNhd ℂ
        (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
        (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) →
      (∀ y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
        ContinuousOn ((A θ u).H y) (physCarrier S 1 hp)) →
      (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ y Φ,
        DifferentiableOn ℂ (fun u => (A θ u).H y Φ) (Metric.ball (0 : ℂ) corrU)) →
      (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ), ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
        physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
          physRestrict (sitesOf T') (physIncl 2 S θ') →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y,
          (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite y ⊆
            Yhat Set.univ (sitesOf T') →
          (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y) →
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
          Jr.W1 C (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x) =
            ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
              (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
              ((S.blockSplit 1 hp).restr x)) →
      -- the constants of the class activity and of the inherited marks
      0 < εH → K0 3 3 T.κ0 + 1 ≤ Kc → κH ≤ 2 * T.κdec - 1 →
      T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ κH →
      εH ≤ 1 / (8 * Kc ^ 3 * c1 3 3 *
        Real.exp ((κH - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) →
      ∃ F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ,
        (∀ q, F1 q = (‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) * Real.exp (-κ₀ *
          treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) - 2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb) +
          pad q) * Real.exp ((2 * T.κdec - 1) * (commonLabels Lab
          (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num) (fun _ => Set.univ) (e1Dom S)
          (e1Dom_isDj_of_eq T Dt hS)).dl (y1 q))) ∧ ∃ c e : physParam 2 S → Finset
              (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ,
        (∀ θ T', c θ T' = gsumCoeff (S.blockSplit 1 hp).μ
          (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)) (A θ)
          (Sum.elim (commonAnchor Lb (fun _ => Set.univ) (e1Dom S) z) y1)
          (Sum.elim (fun i u Φ => e1MarkGParam S (fun b => F₁ (z, b)) (fun b => Sol (z, b))
            p₁ hp z T.t θ i u Φ) (G₁ θ)) T') ∧
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          (AnalyticOnNhd ℂ (fun θ => c θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                physRestrict (sitesOf T') (physIncl 2 S θ') → c θ T' = c θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖c θ T'‖ ≤
              CPE 3 3 Kc κH T.κ0 T.κ' *
                ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
                    corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                  ∑ j, F1 j * Real.exp (-T.κ0 *
                    (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                      (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).dl (y1 j))) *
                Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, c θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T') ∧
              dExt T' = sizeJ 1 (k + 1) (sitesOf T'))) ∧
          (AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
              physRestrict (N := 2) (thickSet S.G' (Yhat Set.univ (sitesOf T')))
                  (physIncl 2 S θ) =
                physRestrict (thickSet S.G' (Yhat Set.univ (sitesOf T'))) (physIncl 2 S θ') →
              e θ T' = e θ' T') ∧
            (∀ θ ∈ physV S S.a₁ S.ν T.t, ‖e θ T'‖ ≤
              27 * covBLogMax 3 3 T.κ /
                  (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)) *
                  Real.exp (-((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) / 18) *
                    dExt T') +
                CPE 3 3 Kc κH T.κ0 T.κ' *
                  ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1Dom S) z},
                      corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
                    ∑ j, F1 j * Real.exp (-T.κ0 *
                      (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
                        (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).dl (y1 j))) *
                  Real.exp (-T.κ' * dExt T')) ∧
            (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E1locJ C z (rawOf D) = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E1locH C z = ∑ T', c ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        (∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0)) ∧
        -- the spin covariance of `e` from that of the activity `A` and the marks `G₁`
        ((∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, ∀ Φ ∈ physCarrier S 1 hp,
            (A θ' (s : ℂ)).H y (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) =
              (A θ (s : ℂ)).H y Φ) →
        (∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j, ∀ Φ ∈ physCarrier S 1 hp,
            G₁ θ' j (s : ℂ) (fun b u => WithLp.toLp 2 (Q *ᵥ (Φ b u).ofLp)) = G₁ θ j (s : ℂ) Φ) →
        ∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
          ∀ T', e θ' T' = e θ T') := by
  obtain ⟨β₀, h3, H⟩ := StepTowerG.e0CoeffFamily_class_of_labels_gen_onSet_agree_pad_rot T₀.toG rfl hA p hcR
    (alpha_three_cast hαR)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ hδ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp₁ Dt S hS hp
    => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ (by simpa using h3N) hN ν hν0
    (by simpa using hν) β hβ (by rw [radius_three_cast]; exact hct) p₁ (by rw [e]; exact hp₁)
    (StepTower.scaleDataG_of_fixed T Dt) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm S hS hp
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [h27, h18] at G
  obtain ⟨F₁, Sol, G'⟩ := G
  refine ⟨F₁, Sol, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1 pad hpad hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε
  simp only [corrF0_toG]
  exact @G' Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1 pad hpad hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε


end Balaban.Inhabited
