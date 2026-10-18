/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerBeta0Families
public import Balaban.Inhabited.StepTowerNewLevelE0LabelsAgree
public import Balaban.Inhabited.StepTowerNewLevelE0Bound
public import Balaban.Inhabited.StepTowerNewLevelE0Sum

/-!
# The class chain with the activity and mark families at every tower radius, the constant `B` explicit (`StepTowerNewLevelE0FamiliesAgree`)

`e0CoeffFamily_class_fromTower_of_families_core_onSet_agree_phi`: `e0CoeffFamily_class_fromTower_of_families_core_onSet_agree` with the hypotheses `0 < markedRad`, `hnumR` and the constant `B` bounded as in
`e0CoeffFamily_class_fromTower_of_families_core_onSet_phi`.
-/

@[expose] public section


namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- The sum of the label constants and the bridge constants, bounded by the explicit constant
of `e0CoeffFamily_class_fromTower_of_families_core_onSet_explicitB`. -/
theorem explicitB_tail {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ : ℕ} [NeZero N₁]
    (h3N : 3 ^ 1 ∣ N₁) {ν β p₁ : ℝ} (hβ : 0 < β) (hp₁ : 0 < p₁)
    (Dt : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
    (hS : S = T.step k hk N₁ ν β p₁) (z : RootIdx 3 3 N₁ T.m₁ (k + 1)) {ι : Type} [Fintype ι]
    (dom : ι → Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (hdom : ∀ τ, ∀ Y ∈ dom τ, IsDj 1 (k + 1) Y) (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (h𝒴 : ∀ τ, ∀ Y ∈ dom τ, Y ∈ 𝒴) {εC aR bb sβ : ℝ} (hεC : 0 ≤ εC) (haR : 0 < aR)
    (hbb : 0 < bb) (hsβ : 0 < sβ) (Bτ : ι → ℝ) (hBτ : ∀ τ, 0 ≤ Bτ τ)
    (E : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ℝ)
    (hnum : ∀ Y ∈ 𝒴, corrU / aR * (∑ τ, if Y ∈ dom τ then 2 * Bτ τ * Real.exp (E τ Y) else 0) ≤
        εC * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y))
    (dlf : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))) dom z} → ℝ)
    (hdl : ∀ q, dlf q = treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2))
    (F1 : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1)))) dom z} → ℝ)
    (hF1 : ∀ q, F1 q = (‖(sβ : ℂ)‖ * ((sβ⁻¹ * Bτ q.1.1) * Real.exp (E q.1.1 q.1.2) / bb) +
      ((1 : ℝ) / 2) ^ ((Fintype.equivFin ι q.1.1 : ℕ) + 1) *
        Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) q.1.2) *
        Real.exp (-((2 * T.κdec - 1) - T.κ0) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2))) *
      Real.exp ((2 * T.κdec - 1) * dlf q)) :
    CPE 3 3 (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
        ((∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁
            (k + 1)))) (e1Dom S) z}, corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1)) +
          ∑ q, F1 q * Real.exp (-T.κ0 * dlf q)) ≤
      CPE 3 3 (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          (corrF0 T k β p₁ * K0 3 3 T.κ0 +
            εC * aR / (2 * bb * corrU) *
              (((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)) * K0 3 3 T.κ0 +
            ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T.κ0 * cBr 3 3) * K0 3 3 T.κ0) := by
  have hβ3 := hβ
  have hS0 : ∑ i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁
      (k + 1)))) (e1Dom S) z}, corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) i.1) ≤
      corrF0 T k β p₁ * K0 3 3 T.κ0 :=
    bridgeFamily_entropy h3N (by norm_num) (e1Dom_isDj_of_eq T Dt hS) z T.κ0_ent
      (corrF0_pos T hk hβ hp₁).le
  have hκGκ0 : T.κ0 ≤ 2 * T.κdec - 1 := by
    have := T.marks_hκ
    have := T.marks_hκ'
    have := T.κ0_nonneg
    have := one_le_c1 3 3
    linarith
  have hS1 := marksConst_sum_le_of_hnumR (m₀ := 1) h3N (by norm_num) dom hdom z T.κ0_ent hκGκ0
    hεC haR corrU_pos hbb hsβ Bτ hBτ E
    (fun Y hY => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hY
      exact hnum _ (h𝒴 q.1 q.2 (mem_markedIdx.1 hq).1))
    (fun τ => ((1 : ℝ) / 2) ^ ((Fintype.equivFin ι τ : ℕ) + 1)) (fun τ => by positivity)
    (sum_half_pow_le_one ι) dlf hdl F1 hF1
  refine mul_le_mul_of_nonneg_left ?_ (by unfold CPE; have := one_le_c1 3 3; positivity)
  refine (add_le_add hS0 hS1).trans (le_of_eq ?_)
  ring

open Classical in
/-- The agree version of the class chain with the activity and mark families, with `B` bounded by an explicit constant. -/
theorem e0CoeffFamily_class_fromTower_of_families_core_onSet_agree_phi {κmin : ℝ} (T₀ : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < 1) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (3 : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (ι : Type) [Fintype ι] {m₀ : ℕ} {ϱ₁ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (Eτ : ι → RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 → ℂ) (Bτ : ι → ℝ)
        (_ : ∀ τ, 0 ≤ Bτ τ) (_ : 0 < S.β)
        (jL : ι → ℕ) (XL : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ, 1 ≤ jL τ) (_ : ∀ τ, jL τ ≤ k)
        (Gk : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (Gj : ι → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (_ : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
          Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
        (X₀ X₁f : ι → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (𝒦X : ι → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃
          (X₀ τ)          (X₁f τ) (jL τ))
        (_ : ∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG
            T.t δ₃ KcL Cx c₂ BG₂
          δ₁ δfl (X₁f τ))
        {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (_ : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (_ : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (_ : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
        (_ : ∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        (_ : ∀ τ, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ (XL τ)) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 m₀ T.m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        {𝒮 : ι → Set (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)}
        (_ : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
        (_ : ∀ τ, ∀ r ∈ 𝒮 τ,
          ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
        (F₁L : ι → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' 2), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) × ((stepG 3 3 N₁ T.m₁ k (rhoSep
              T.m₁)).Ω 1 → ℂ))
        (_ : ∀ τ, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG 3 3 N₁ T.m₁ k
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
        (_ : ∀ τ, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ, ∀ D : BgData (Gk τ) 2, InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν
            D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        (_ : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        (_ : ∀ (τ : ι) (h : (jL τ) ≤ k + 1), GsSpecStrong (jL τ) h (XL τ)
          (Gj τ))
        (_ : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (_ : R * δ₁ ≤ deltaStar 3 3 2) (_ : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (_ : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (_ : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        (_ : 3 ^ m₀ ∣ N₁) (_ : 1 ≤ m₀)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
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
        (_ : S.p₁ ≤ ρ)
        (_ : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D → ∀ w : S.EC,
          Jr.EJ C (rawOf D, w) = ∑ τ, Eτ τ (Jr.PJ (jL τ) (rawOf D, w)))
        (𝒴C : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))
        (H : physParam 2 S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) m₀ (jL τ) (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * Eτ τ r)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (h𝒴dj : ∀ Y ∈ 𝒴C, IsDj 1 (k + 1) Y)
        (_ : ∃ AC : physParam 2 S → ℂ → LabelAct
            (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj) (S.blockSplit 1 hp).Ωb εC
            (2 * T.κdec - 1) T.κ0 (K0 3 3 T.κ0),
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u Y, (AC θ u).H Y = H θ Y u) ∧
          (∀ Y Φ, AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (AC r.1 r.2).H Y Φ)
            (physV S S.a₁ S.ν T.t ×ˢ Metric.ball (0 : ℂ) corrU)) ∧
          (∀ Y, ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ Metric.ball (0 : ℂ) corrU,
            Continuous ((AC θ u).H Y)) ∧
          (∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ Y Φ,
            DifferentiableOn ℂ (fun u => (AC θ u).H Y Φ) (Metric.ball (0 : ℂ) corrU)) ∧
          (∀ Z : Set (CTorus 3 3 N₁ T.m₁ (k + 1)), ∀ θ ∈ physV S S.a₁ S.ν T.t,
            ∀ θ' ∈ physV S S.a₁ S.ν T.t,
            physRestrict (N := 2) Z (physIncl 2 S θ) = physRestrict Z (physIncl 2 S θ') →
            ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ Y : {Y // Y ∈ 𝒴C},
              Y.1 ⊆ Yhat Set.univ Z → (AC θ (s : ℂ)).H Y = (AC θ' (s : ℂ)).H Y)),
      (0 < markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) →
      (∀ Y ∈ 𝒴C, corrU / (δ₁ / (2 * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (∑ τ : ι, if Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ) then
            2 * Bτ τ * Real.exp (-κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) -
              2 * κdec * treeLenCov S.G' m₀ Y)
          else 0) ≤ εC * Real.exp (-(2 * T.κdec - 1) * treeLenCovOne 1 (k + 1) Y)) →
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2 =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the numerical condition of the composed activity
      max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) εC ≤
        1 / (8 * (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) ^ 3 * c1 3 3 *
          Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG 3 3 + c1 3 3 + T.κ' * cG 3 3)) →
      (Φ : (physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ), B ≤ CPE 3 3 (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
          rootUnionK 3 3 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          (corrF0 T k β p₁ * K0 3 3 T.κ0 +
            εC * (δ₁ / (2 * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) / (2 * bb * corrU) *
              (((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr 3 3)) * K0 3 3 T.κ0 +
            ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T.κ0 * cBr 3 3) * K0 3 3 T.κ0) → Φ e B) →
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
        (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
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
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
            (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub 2 S.G'), (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub 2 S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub 2 S.G'), 0) T' else 0) := by
  classical
  obtain ⟨β₁, h31, H1⟩ := e0CoeffFamily_class_fromTower_of_labels_gen_onSet_agree_pad T₀ hA p hcR hαR
  obtain ⟨β₂, -, H2⟩ := zeroSourceFamily_fields_fromTower_agree T₀ hHull hA p hcR hαR
  refine ⟨max β₁ β₂, h31.trans (le_max_left _ _), fun T hm₁ hBG hBG₂ hκ hδ => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS hp
  have hN1 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨F₁, Sol, HC⟩ := H1 T hm₁ hBG hBG₂ hκ hδ k hk N₁ h3N hN₁ ν hν0 hν β ((le_max_left _ _).trans hβ) hct p₁ hp₁ Dt
    S hS hp
  obtain ⟨Jr, Lb₀, _, Lab₀, A₀, hεpos, h0hol, h0cont, h0diff, h0loc, h0W⟩ :=
    H2 T hm₁ hBG hBG₂ hκ hδ k hk N₁ h3N hN₁ ν hν0 hν β ((le_max_right _ _).trans hβ) hct p₁ hp0 hp₁ Dt S hS hp
  refine ⟨Jr, ?_⟩
  intro C z ι _ m₀ ϱ₁ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC Eτ Bτ hBτ hβS jL XL hj1 hjk Gk
    Gj hlocE X₀ X₁f 𝒦X hB hFl cψ hcψ hMX δc hdm hα hsm hcov hX₁ hconn hrow hopt κdec κ₀ hκ₀ hκdec
    hκ h1 hlog 𝒮 hEan hEbd F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hSg hc7 R hR hsmR hRs
    hsmall hnum hnum' ρ hρ hρc hρpp hN hm1 bb hbb hab G₁ hG₁ hρp hEJ 𝒴C h𝒴 H hH εC hεC h𝒴dj hAct hmr hnumR hE hεnum Φ hΦ
  have hκ0' : aEnt 3 3 + 1 ≤ T.κ0 := by linarith [T.κ0_two]
  have ha1 : (1 : ℝ) < corrU := by norm_num [corrU]
  have hε : 0 ≤ max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ
      T.t (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (1 / S.β)))) εC := hεpos.le.trans (le_max_left _ _)
  have hdomC : ∀ τ : ι, ∀ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ),
      IsDj 1 (k + 1) Y :=
    fun τ Y hY => polyDom_isDj_one S.hG' le_rfl hN hm1 (hcov τ) le_rfl (hopt τ) hY
  obtain ⟨AC, hAC, hhol, hcont, hdiff, hloc⟩ := hAct
  have hW := Jr.classActivityFamily_ae_W1_eq_gen_onSet (h𝒮 := h𝒮) C hb₁ hbC
    Eτ Bτ hBτ hβS
    jL XL hj1 hjk Gk Gj
    hlocE
    X₀ X₁f 𝒦X hB hFl hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd
    F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs hsmall hnum hnum' z hρ
    hρc hρpp hp ha1 hbb.le hab 𝒴C h𝒴 H hH hEJ hρp
  have hθ0 : ∀ D : BgData S.G' 2, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
      ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
        (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈ physV S S.a₁ S.ν T.t := fun D hD =>
    physVqRho_subset S S.a₁ S.ν T.t 1 1 (rawOf_source_mem_physVqRho S 1 T.t D hD 0 (by simp))
  obtain ⟨hM1hol, hM1cont, hM1diff, hM1loc, hM1W⟩ := Jr.classActivityFamily_sum_fields C hp A₀
    (fun θ u => commonAct AC hN1 (by norm_num) (fun _ => Set.univ)
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC hεC T.κ0_two θ u)
    (fun _ => Set.univ) (e1Dom S) (e1Dom_isDj_of_eq T Dt hS) hN1 (by norm_num) hε T.κ0_two
    h0hol
    (commonAct_holA_analytic AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two fun Y Φ _ => hhol Y Φ)
    h0cont
    (commonAct_contA AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two fun Y θ hθ u hu =>
      (hcont Y θ hθ u hu).continuousOn)
    h0diff
    (fun θ hθ => commonAct_holA_differentiableOn AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two θ
      fun Y Φ => hdiff θ hθ Y Φ)
    h0loc
    (fun T' θ hθ θ' hθ' hres s hs y hsub => by
      cases y with
      | inl Y => exact hloc (sitesOf T') θ hθ θ' hθ' hres s hs Y hsub
      | inr _ => rfl)
    h0W
    (fun D hD s hs => by
      filter_upwards [hW D hD s hs] with x hx
      rw [hx, commonAct_total AC hN1 (by norm_num) _ _ hdomC hεC T.κ0_two]
      simp only [hAC _ (hθ0 D hD)])
  -- the labels of the rooted pairs: the bridges among the root-union labels of the class domains
  have hbr : ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z},
      bridge 1 z q.1.2 ∈ bridgeFamily 1 (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z :=
    fun q => bridge_mem_bridgeFamily_of_mem q.2
  have hKc : K0 3 3 T.κ0 + 1 ≤ 2 * (K0 3 3 T.κ0 + 1) +
      (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) + rootUnionK 3 3 1 T.m₁ T.κ0 := by
    have h0 := K0_pos 3 3 T.κ0
    have h1' := rootUnionK_nonneg (d := 3) (L := 3) (m₁ := T.m₁) 1 T.κ0
    linarith
  obtain ⟨padF, hpadFdef⟩ : ∃ f : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁
      T.m₁ (k + 1)))) (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} → ℝ,
      ∀ q, f q = ((1 : ℝ) / 2) ^ ((Fintype.equivFin ι q.1.1 : ℕ) + 1) *
        Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) q.1.2) *
        Real.exp (-((2 * T.κdec - 1) - T.κ0) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)) :=
    ⟨fun q => ((1 : ℝ) / 2) ^ ((Fintype.equivFin ι q.1.1 : ℕ) + 1) *
        Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) q.1.2) *
        Real.exp (-((2 * T.κdec - 1) - T.κ0) * treeLenCovOne 1 (k + 1) (bridge 1 z q.1.2)),
      fun q => rfl⟩
  have hpadF : ∀ q, 0 < padF q := fun q => by rw [hpadFdef q]; positivity
  obtain ⟨F1, hF1eq, c, e, -, hprop, hvals, hval⟩ := HC (h𝒮 := h𝒮) Jr C z (Lb₀ ⊕ ({Y // Y ∈ 𝒴C} ⊕ RootUnionLb 1
      (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ))))
    (Lab₀.sum (commonLabels (thickLabels (m₀ := 1) (j := k + 1) 𝒴C h𝒴dj) hN1
      (by norm_num) (fun _ => Set.univ)
      (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC)) _
    (2 * T.κdec - 1)
    (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
      rootUnionK 3 3 1 T.m₁ T.κ0) _
    ι hb₁ hbC
    Eτ Bτ hBτ hβS
    jL XL hj1 hjk Gk Gj
    hlocE
    X₀ X₁f 𝒦X hB hFl hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd
    F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk hSg hc7 hR hsmR hRs hsmall hnum hnum' hρ hρc
    hρpp hN hm1 hbb hab G₁ hG₁ hρp hEJ
    (fun q => Sum.inl (Sum.inr (Sum.inr ⟨z, ⟨bridge 1 z q.1.2, hbr q⟩⟩))) (fun _ => rfl) padF hpadF hE
    hM1hol hM1cont hM1diff hM1loc hM1W
    (lt_of_lt_of_le hεpos (le_max_left _ _)) hKc le_rfl T.marks_hκ hεnum
  refine ⟨e, _, hΦ _ _ ?_, fun T' => ⟨(hprop T').2.1, (hprop T').2.2.1, (hprop T').2.2.2.1,
    (hprop T').2.2.2.2⟩, fun D hX => ⟨(hvals D hX).2.2.1, (hvals D hX).2.2.2⟩, hval⟩
  refine explicitB_tail T hk (by simpa using h3N)
    (lt_of_lt_of_le (by norm_num) ((h31.trans (le_max_left _ _)).trans hβ)) hp0 Dt S hS z
    (fun τ : ι => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) hdomC 𝒴C
    (fun τ Y hY => by rw [h𝒴]; exact Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hY⟩) hεC
    (div_pos (lt_trans (mul_pos (add_pos corrU_pos hbb) hmr) hab) (mul_pos two_pos hmr))
    hbb hβS Bτ hBτ
    (fun τ Y => -κ₀ * treeLenCovOne m₀ (jL τ) (XL τ) - 2 * κdec * treeLenCov S.G' m₀ Y)
    hnumR _ ?_ F1 ?_
  · intro q
    rfl
  · intro q
    rw [hF1eq q, hpadFdef q]

end Balaban.Inhabited
