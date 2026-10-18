/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyM2
public import Balaban.Fluctuation.LocalClassDensityValTower

/-!
# A general class at the tower with the inherited marks (`LocalClassDensityFamilyTower`)

`e0CoeffFamily_class_fromTower_of_labels`: `e0CoeffFamily_class_fromTower` with the input (M2)
discharged.  The marks family of the inherited energy is the family `G₁` of
`LocalClassDensityFamilyMarks` (formula `hG₁`, the rooted pairs of `markedIdx` of the class domains
as index set, labels `y1` of the rooted pairs whose sites are the bridges `bridge 1 z Y`, `hy1`),
and every hypothesis (M2) follows from `classMarks_M2_of_family`; `F1` is produced.  The per-label
settings of the inherited labels at the step (`hB`, `hF`, `hcov`, `hX₁`, `hopt`, `hSg`, `hchart`),
their maps with the defining properties, and the numerical conditions
(`(corrU + b) · markedRad < δ₁`, `p₁ ≤ ρ < 2 p₁`, `ρ ≤ c_ψ`) are named hypotheses.  The input (M1)
(the activity family of the class) remains a hypothesis: it is not constructed.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- The generic version of `e0CoeffFamily_class_fromTower_of_labels`, with the label charts of
`hEan`, `hEbd` replaced by any sets `𝒮 τ` containing the composed step data of the labels
(`h𝒮`); `e0CoeffFamily_class_fromTower_of_labels_gen` is the case of the label charts. -/
theorem e0CoeffFamily_class_fromTower_of_labels_gen_onSet {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
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
                q.1.2),
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
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ, ∃ c e : physParam 2 S → Finset
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
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, H⟩ := e0CoeffFamily_class_fromTower T hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  obtain ⟨F₁, Sol, H'⟩ := H k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  refine ⟨F₁, Sol, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ
    hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow
    hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk
    h𝒮 hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1
    hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε
  obtain ⟨F1, hF1, hmeas, hdep, hbd, hhol, hcont, hdiff, hloc, hroot, hid⟩ :=
    Jr.classMarks_M2_of_family_gen_onSet (h𝒮 := h𝒮)
        C hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB
      hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁L hF₁an hF₁
      SolL hSolan hSolprop FkL hFkan hFk (fun τ => hSg τ ((hjk τ).trans (Nat.le_succ k))) hc7 hR
      hsmR hRs hsmall hnum hnum' hN hm1 le_rfl
      (by norm_num) z hρ hρc hρpp hp (by norm_num [corrU]) hbb hab G₁ hG₁ hEJ hρp hE Lab
      (fun _ => Set.univ) (e1Dom S)
      (by simpa using h3N) (e1Dom_isDj_of_eq T Dt hS) y1 hy1 (2 * T.κdec - 1)
  exact ⟨F1, H' Jr C z Lb Lab εH κH Kc A _ y1 G₁ F1 hE hAhol hAcont hAdiff hAloc hW hmeas hdep hbd
    hhol hcont hdiff (fun T' θ hθ θ' hθ' hres s hs j hsub => hloc _ θ hθ θ' hθ' hres s hs j hsub)
    hroot hid hF1 hεpos hKc hκG hκH hε⟩

open Classical in
/-- The generic version of `e0CoeffFamily_class_fromTower_of_labels` (any label functionals `Eτ`). -/
theorem e0CoeffFamily_class_fromTower_of_labels_gen {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
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
        (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν (jL τ) bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl)))
        (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight 3 S.a₁) S.ν (jL τ) bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
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
                q.1.2),
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
          (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ, ∃ c e : physParam 2 S → Finset
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
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, H⟩ := e0CoeffFamily_class_fromTower_of_labels_gen_onSet T hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  obtain ⟨F₁, Sol, H'⟩ := H k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  refine ⟨F₁, Sol, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ
    hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow
    hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk
    hSg hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1
    hE hAhol hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε
  exact @H' Jr C z Lb _ Lab εH κH Kc A ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ
    Bτ hBτ hβS jL XL hj1 hjk Gk Gj hlocE X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn
    hrow hopt κdec κ₀ hκ₀ hκdec hκ h1 hlog _ hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL
    hFkan hFk (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht) hSg hc7 R
    hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ y1 hy1 hE hAhol
    hAcont hAdiff hAloc hW hεpos hKc hκG hκH hε


open Classical in
/-- **The coefficient family of the new energy density of a general class at the tower, with the
marks of the inherited energy constructed.**  The conclusion of `e0CoeffFamily_class_fromTower`,
whose hypotheses (M2) are replaced by the per-label settings and maps of the inherited labels
(`𝒯E`), the formula `hG₁` of the marks and the labels `y1` of the rooted pairs (`hy1`); `F1` is
produced.  The input (M1) and the analyticity `hE` are hypotheses as in
`e0CoeffFamily_class_fromTower`. -/
theorem e0CoeffFamily_class_fromTower_of_labels {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
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
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ T.m₁ (k + 1) × Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ T.m₁ (k + 1) 2 (rhoSep T.m₁)} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (hb₁ : 1 ≤ bL) (hbC : bL ≤ scaledC0 3)
        (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
        (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
        (Gk : 𝒯E → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (X₀ X₁f : 𝒯E → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : 𝒯E → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (hB : ∀ τ : 𝒯E, BgSetting 2 S.G' (Gk τ) (C.Tm.gs τ.1.1 τ.1.2.2) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) τ.1.1)
        (hF : ∀ τ : 𝒯E, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (hcψ : 0 ≤ cψ)
        (hMX : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (hα : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (hsm : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (hcov : ∀ τ : 𝒯E, CovSetup S.G' C.m₀ τ.1.1 τ.1.2.2 (𝒦X τ))
        (hX₁ : ∀ τ : 𝒯E, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ))
        (hconn : HatConn S.G')
        (hrow : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        (hopt : ∀ τ : 𝒯E, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ τ.1.2.2) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 τ.1.2.2)
        {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
        (hκ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
        (hlog : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ C.m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        (hκP : κdec - 1 ≤ P.κ)
        (hchart : ∀ τ : 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1.1 τ.1.2.2) (compWeight 3 S.a₁) S.ν τ.1.1 bL
          (bL ^ 2 * T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl),
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2)
        (F₁L : 𝒯E → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (hF₁an : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (hF₁ : ∀ τ : 𝒯E, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : 𝒯E → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (hSolan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (hSolprop : ∀ τ : 𝒯E, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
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
        (FkL : ∀ τ : 𝒯E, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (hFkan : ∀ τ : 𝒯E, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (hFk : ∀ τ : 𝒯E, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (hSg : ∀ (τ : 𝒯E) (h : τ.1.1 ≤ k + 1), GsSpecStrong τ.1.1 h τ.1.2.2
          (C.Tm.gs τ.1.1 τ.1.2.2))
        (hc7 : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (hR : 2 ≤ R)
        (hsmR : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (hRs : R * δ₁ ≤ deltaStar 3 3 2) (hsmall : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (hnum : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (hnum' : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < 2 * p₁)
        (hN : 3 ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀)
        {bb : ℝ} (hbb : 0 < bb)
        (hab : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ q.1.1.1.1 (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (C.Tm.gs q.1.1.1.1 q.1.1.1.2.2) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * C.Tm.E q.1.1.1.1 q.1.1.1.2.1 q.1.1.1.2.2 r.1 r.2))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (hρp : S.p₁ ≤ ρ)
        (y1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} → Lb ⊕ RootUnionLb 1 (fun _ =>
              Set.univ) (e1Dom S))
        (hy1 : ∀ q, (commonLabels Lab (by simpa using h3N : 3 ^ 1 ∣ N₁) (by norm_num)
            (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS)).ysite (y1 q) = bridge 1 z
                q.1.2),
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
          (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} → ℝ, ∃ c e : physParam 2 S → Finset
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
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  obtain ⟨β₀, hβ₀, H⟩ := e0CoeffFamily_class_fromTower_of_labels_gen T hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  obtain ⟨F₁, Sol, H'⟩ := H k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp₁ Dt S hS hp
  refine ⟨F₁, Sol, ?_⟩
  intro Jr C z Lb _ Lab εH κH Kc A 𝒯E h𝒯 P Dom ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC
    hm hcl hβS hE₀ Gk X₀ X₁f 𝒦X hB hF cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀
    hκ₀ hκdec hκ h1 hlog hκP hchart F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 R hR
    hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp y1 hy1 hE hAhol hAcont
    hAdiff hAloc hW hεpos hKc hκG hκH hε
  have hmem : ∀ τ : 𝒯E, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (3 ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
        Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
        (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : 𝒯E, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem τ).1).1
  have hjk : ∀ τ : 𝒯E, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem τ).1).2
  have hXp : ∀ τ : 𝒯E, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem τ).2.2.1
  have hy : ∀ τ : 𝒯E, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem τ).2.2.2
  have hraw := fun τ : 𝒯E => classOldEnergy_chart_radius_raw (N := 2) (b := bL) C hm hcl hκP hE₀
    S.a₁ S.ν δ₃ T.t δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  have hEJ : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
      Jr.EJ C (rawOf D, w) = ∑ τ : 𝒯E,
        C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 (Jr.PJ τ.1.1 (rawOf D, w)).1
          (Jr.PJ τ.1.1 (rawOf D, w)).2 := fun D _ w => by
    unfold StepSetting.JointRep.EJ
    rw [Finset.sum_coe_sort 𝒯E (fun τ => C.Tm.E τ.1 τ.2.1 τ.2.2 (Jr.PJ τ.1 (rawOf D, w)).1
      (Jr.PJ τ.1 (rawOf D, w)).2), h𝒯,
      sum_classLabels_E_eq_Edens C.m₀ C.Tm (fun j => (Jr.PJ j (rawOf D, w)).1)
      (fun j => (Jr.PJ j (rawOf D, w)).2)]
  have key := H' Jr C z Lb Lab εH κH Kc A 𝒯E hb₁ hbC
    (fun τ r => C.Tm.E τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβS
    (fun τ => τ.1.1) (fun τ => τ.1.2.2) hj1 hjk Gk (fun τ => C.Tm.gs τ.1.1 τ.1.2.2)
    (fun τ Ψ Ψ' h h' hag => hcl.localE τ.1.1 τ.1.2.1 τ.1.2.2 Ψ Ψ' h h' hag) X₀ X₁f 𝒦X hB hF hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1)
    (fun τ => (hraw τ).2) F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs
    hsmall hnum hnum' hρ hρc hρpp hN hm1 hbb hab G₁ hG₁ hρp hEJ y1 hy1 hE hAhol hAcont hAdiff
    hAloc hW hεpos hKc hκG hκH hε
  exact key

end Balaban.Inhabited
