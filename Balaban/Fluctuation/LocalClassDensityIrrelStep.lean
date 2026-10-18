/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelChainX

/-!
# The class chain with the per-label premises at the composed step data
(`LocalClassDensityIrrelStep`)

`e0CoeffFamily_class_fromTower_of_irrelBounds_step`: the theorem
`e0CoeffFamily_class_fromTower_of_irrelBounds_X` with its two per-label premises, the chart
condition `hchart` and the bound `hEbd` of the irrelevant parts (P1 (3.128)), stated only at the
composed step data of the labels, as in the source: for every realizable triple `t ∈ FlRealLC`
of the step (decoupled background `φ_{k+1}(s)` of the step datum `Θ ∈ Ξ^c_{k+1}(1, t)`, complex
decoupling parameters, fluctuation field `δφ(s)`, layer-constant fluctuation `ψ'` in the ball),
at the datum `r = D2raw (Gk τ) (Gj τ) a (FkL τ) (d1Triple S.G' (Gk τ) stepG a t)` of
`𝔹_j(X^⋆)`, the composition (6.2) into the level-`j` generating set of the label of the background
of the composed datum of `𝔹_k(X^⋆)` (P1 Lemma 2.1: `ψ^{(j)}_k`).  P1 (3.128) is the bound "at
`ψ = ψ^{(j)}_k`"; on the whole label chart `Ξ^c_j(Gj τ; bL, …)` of the landed theorem the
irrelevant parts have no factor `L^{-(d+α₃)(k-j)}` (WIDEGEN, W1040).

The chain reads the label functionals only at these data (`classOldMarkedLocal_joint_gen_onSet`,
through `eTermFun`), so the theorem is the instance of
`e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet` at the sets of composed step data.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

open Classical in
/-- **The coefficient family of the new energy density of a class with inherited labels, with the
per-label premises at the composed step data.**  As
`e0CoeffFamily_class_fromTower_of_irrelBounds_X`, with the chart condition (the composed datum in
the term domain, `Ψ(y)·Ψ(y)` in the slit plane) and the per-label bound of the irrelevant parts
`‖ℰ^{(j)}_irrel(y, X; r)‖ ≤ B_τ e^{-(κ_dec - 1) d^cov_{C.m₀}(X)}` required only at the composed
step data `r = D2raw (Gk τ) (Gj τ) a (FkL τ) (d1Triple S.G' (Gk τ) stepG a t)`,
`t ∈ FlRealLC`. -/
theorem e0CoeffFamily_class_fromTower_of_irrelBounds_step {κmin : ℝ} (T : StepTower κmin)
    (hHull : stepHullMin ≤ κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁) (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        (_ : S = T.step k hk N₁ ν β p₁) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (z : RootIdx 3 3 N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus 3 3 N₁ T.m₁ (k + 1) × Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) ×
            Set (CTorus 3 3 N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (3 ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom 3 3 N₁ T.m₁ (k + 1) 2 (rhoSep T.m₁)} {ϱ₁ ϱ₀ ϱ₃ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 < S.β) (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1)
            (rhoSep T.m₁), (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld 3 3 N₁ T.m₁ (k + 1) 2, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock 3 3 (N₁ * 3 ^ T.m₁) (k + 1) j x = jBlock 3 3 (N₁ * 3 ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus 3 3 N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide 3 C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => 3 / 2 * cellSide 3 C.m₀ T.m₁ τ.1.1) (3 * cellSide 3 C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus 3 3 N₁ T.m₁ (k + 1) × CTorus 3 3 N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW 3 C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : r₀ ≤ 324)
        (_ : bgR0 3 3 + 1 + 6 * Real.log 3 / (agmonRate 3 / 16) ≤ 855 * (3 : ℝ) ^ T.m₁)
        (_ : bgR0 3 3 ≤ ϱ₁) (_ : ϱ₁ ≤ Balaban.LargeField.minSep 3 (3 ^ (T.m₁ + 4)))
        (Gk0 : GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₀)
        (Gj0 : GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₃)
        {X₀' X₁f' X₁f'' : Finset (CTorus 3 3 N₁ T.m₁ (k + 1))} {j₁ : ℕ}
        (_ : BgSetting 2 S.G' Gk0 Gj0 S.a₁ S.ν cB BG κ r₀ T.t δ₃ X₀' X₁f' j₁)
        (_ : FlSetting 2 S.G' Gk0 (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG T.t δ₃ KcL Cx
          c₂ BG₂ δ₁ δfl X₁f''),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) ϱ₁)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν κ BG T.t δ₃
          KcL Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀ {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ (3 : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin 3 3 2 BG κ (xiC1 3 * T.t) < δc)
        (_ : K4 3 3 2 BG κ * (xiC1 3 * T.t) < coerciveConst 3 / 2)
        (_ : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * (((3 ^ C.m₀) ^ 3 : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        -- the constants of the per-label bounds of the irrelevant parts (P1 (3.128))
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((3 : ℕ) : ℝ)⁻¹ ^ (k - τ.1.1)) ^ (((3 : ℕ) : ℝ) + α₃)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀)
        (_ : aEnt 3 3 + 1 ≤ κ₀) (_ : 0 ≤ 2 * T.κdec - 1)
        (_ : (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (C.m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
          ((3 : ℕ) : ℝ) ^ C.m₀ * ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec)
        (F₁L : {τ // τ ∈ 𝒯E} → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (s : DecParams S.G') (D : BgData S.G' 2),
          (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : {τ // τ ∈ 𝒯E} → Dec2.DecParams (coverOf S.G') ×
          Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 BG κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ p : Dec2.DecParams (coverOf S.G') ×
            Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2,
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
        (FkL : ∀ τ : {τ // τ ∈ 𝒯E}, RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((Gk τ).Ω 1 × Fin 2 → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ D : BgData (Gk τ) 2,
          InUnionDomainC (Gk τ) (bgC0 3 3 2) (bgC1 3 3 2) S.ν D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D,
            bgMultC (Gk τ) (compWeight 3 S.a₁) S.ν (bgC0 3 3 2) D))
        -- the composed step data of the labels lie in the term domain, `Ψ(y)·Ψ(y)` in the slit plane
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ
            T.t (X₁f τ) BG₂ δ₁, ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` at the composed step data
        -- (P1 (3.128), open)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ
            T.t (X₁f τ) BG₂ δ₁, ∀ r, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) →
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        (_ : c7 3 3 2 BG κ ≤ thm73C3 3 3 2) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (R * δ₁) ≤ bgC1 3 3 2)
        (_ : R * δ₁ ≤ deltaStar 3 3 2) (_ : cK2 3 3 2 * (R * δ₁) < bgC0 3 3 2 / 2)
        (_ : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        (_ : cK2' 3 3 2 (famConst 3 3 BG₂ κ) * δ₁ ≤
          c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3 / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam 2 S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ q.1.1.1.1 (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG 3 3 N₁ T.m₁ k
                  (rhoSep T.m₁))
                (compWeight 3 S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ q.1.1.1.1 q.1.1.1.2.1
                  q.1.1.1.2.2 r.1 r.2))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (_ : S.p₁ ≤ ρ)
        (𝒴C : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
        (H : physParam 2 S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw S.G' (compWeight 3 S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2
                    r.1 r.2)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (compWeight 3 S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2
                    r.1 r.2)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (_ : 0 < markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (_ : 2 * corrU * markedRad 3 3 2 k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (_ : corrU / (δ₁ / (2 * markedRad 3 3 2 k S.a₁ κ cψ
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 κ₀ * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG 3 3)) * ((((3 : ℕ) : ℝ) ^ (n₁ - 1)) ^ 3)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ) ^ C.m₀ *
            ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3)))) ≤ εC),
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
      ∃ e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
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
  obtain ⟨β₀, hβ₀, HC⟩ := e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet T hHull hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  obtain ⟨Jr, HC'⟩ := HC k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀
    i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hr₀ hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, HX⟩ := @HC' C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL
    Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hr₀ hrho hϱ₁
    hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog Bτ hBτ
    CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL
    hFkan hFk hchart hEbd hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp
    𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum
  exact @HX cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog
    (fun τ => {r | ∃ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ T.t (X₁f τ)
      BG₂ δ₁, r = D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
        (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1 t.2.1
          t.2.2)})
    (fun τ r hr => by
      obtain ⟨t, ht, rfl⟩ := hr
      exact hchart τ t ht _ rfl) Bτ hBτ
    (fun τ r hr => by
      obtain ⟨t, ht, rfl⟩ := hr
      exact hEbd τ t ht _ rfl) CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL
    hSolan hSolprop FkL hFkan hFk (fun τ t ht => ⟨t, ht, rfl⟩) hc7 R hR hsmR hRs hsmall hnum hnum'
    ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum

end Balaban.Inhabited
