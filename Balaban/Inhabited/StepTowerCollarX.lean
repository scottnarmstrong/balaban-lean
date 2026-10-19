/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelChainX
public import Balaban.Inhabited.StepTowerCollarCore
public import Balaban.Inhabited.StepTowerCollarGNum

/-!
# The class chain with the per-label bound in `d(X)` at a general collar (`StepTowerCollarX`)

* `index_condition_shift_collar`: the block-index condition `(5 L + 13) c₁ + r₀ L ≤ (L - 2) L^{m₀+1}`
  of `bgFlSetting_castLocalB` at `L = d = 3`, `c₁ = 81`, `m₀ ≥ 7` for every collar `r₀ ≤ 1431`
  (`2268 + 3 · 1431 = 3^8`); the form of `index_condition_shift_three` (`r₀ ≤ 324`) for the larger
  collars of the source (`r₀ = 4 d L³ + L = 327`).
* `e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet_agree_collar`: the statement of
  `e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet_agree` with the premise `r₀ ≤ 324` replaced
  by `r₀ ≤ 1431`.  The proof is the former proof of
  `e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet_agree`, which is now its instance, with the
  index condition `index_condition_shift_collar` and the chain core
  `e0CoeffFamily_class_fromTower_of_irrelBounds_core_onSet_agree_collar`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

/-- **The block-index condition at `L = d = 3` for the collars `r₀ ≤ 1431`.**  With `c₁ = 3^4 = 81`
(`m₁' = m₁ + 4`) the condition `(5 L + 13) c₁ + r₀ L ≤ (L - 2) L^{m₀+1}` of
`bgFlSetting_castLocalB` holds for `m₀ ≥ 7`. -/
theorem index_condition_shift_collar {m₀ : ℕ} (hm : 7 ≤ m₀) {r₀ : ℝ} (hr : r₀ ≤ 1431) :
    (((5 * 3 + 13) * 81 : ℕ) : ℝ) + r₀ * ((3 : ℕ) : ℝ) ≤
      (((3 - 2 : ℕ)) : ℝ) * ((3 : ℕ) : ℝ) ^ (m₀ + 1) := by
  have h : ((3 : ℕ) : ℝ) ^ 8 ≤ ((3 : ℕ) : ℝ) ^ (m₀ + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have := index_condition_collar_of_le (L := 3) (m₀ := m₀) hr
    (R := 1431) (by norm_num at h ⊢; linarith)
  norm_num at this ⊢
  linarith

open Classical in
/-- The class chain (XCollar), with `B` bounded by an explicit constant. -/
theorem StepTowerG.e0CoeffFamily_class_of_irrelBounds_X_onSet_agree_collar_phi {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin)
    (hm₀ : T₀.m₀ = 1) (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (_ : ϱ = rhoSepG d L T.m₁)
        (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (_ : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass d L N₁ T.m₁ k N ϱ) (z : RootIdx d L N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus d L N₁ T.m₁ (k + 1) × Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ T.m₁ (k + 1) ×
            Set (CTorus d L N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom d L N₁ T.m₁ (k + 1) N ϱ} {ϱ₁ ϱ₀ ϱ₃ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 d)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 < S.β) (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ T.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => L / 2 * cellSide L C.m₀ T.m₁ τ.1.1) (L * cellSide L C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW L C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : L ^ C.m₀ ∣ N₁) (_ : 1 ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
        (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + r₀ * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
        (_ : rhoSepG d L T.m₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s)))
        (_ : bgR0 d L ≤ ϱ₁) (_ : ϱ₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s)))
        (Gk0 : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₀)
        (Gj0 : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₃)
        {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ T.m₁ (k + 1))} {j₁ : ℕ}
        (_ : BgSetting N S.G' Gk0 Gj0 S.a₁ S.ν cB BG κ r₀ T.t δ₃ X₀' X₁f' j₁)
        (_ : FlSetting N S.G' Gk0 (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG T.t δ₃ KcL Cx
          c₂ BG₂ δ₁ δfl X₁f''),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₁)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG T.t δ₃
          KcL Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀ {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin d L N BG κ (xiC1 d * T.t) < δc)
        (_ : K4 d L N BG κ * (xiC1 d * T.t) < coerciveConst d / 2)
        (_ : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν)
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        -- the sets `𝒮 τ` (containing the composed step data) lie in the term domain, `Ψ(y)·Ψ(y)` in
        -- the slit plane
        {𝒮 : {τ // τ ∈ 𝒯E} → Set (RawData d L (N₁ * L ^ T.m₁) (k + 1) N)}
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃))))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀)
        (_ : aEnt d L + 1 ≤ κ₀) (_ : 0 ≤ 2 * T.κdec - 1)
        (_ : (2 * T.κdec - 1) * ((L : ℝ) ^ (C.m₀ - 1) + 2 * (d : ℝ) *
          (L : ℝ) ^ C.m₀ * ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
        (F₁L : {τ // τ ∈ 𝒯E} → DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (s : DecParams S.G') (D : BgData S.G' N),
          (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : {τ // τ ∈ 𝒯E} → Dec2.DecParams (coverOf S.G') ×
          Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ p : Dec2.DecParams (coverOf S.G') ×
            Edat (stepG d L N₁ T.m₁ k ϱ) N,
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
            Background.Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2
              (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Background.Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2 (cK2' d L N (famConst d L BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).1
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ,
              Background.Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ : {τ // τ ∈ 𝒯E}, RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) N,
          InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ D : BgData (Gk τ) N,
          InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
            bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
        (_ : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        (_ : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * T.t))) + 5 * (R * δ₁) ≤ bgC1 d L N)
        (_ : R * δ₁ ≤ deltaStar d L N) (_ : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
        (_ : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        (_ : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
          c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam N S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ q.1.1.1.1 (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ T.m₁ k
                  ϱ)
                (compWeight L S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ q.1.1.1.1 q.1.1.1.2.1
                  q.1.1.1.2.2 r.1 r.2))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (_ : S.p₁ ≤ ρ)
        (𝒴C : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
        (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k ϱ)
                  (compWeight L S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2
                    r.1 r.2)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k ϱ)
                  (compWeight L S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2
                    r.1 r.2)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (_ : 0 < markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (_ : 2 * corrU * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (_ : corrU / (δ₁ / (2 * markedRad d L N k S.a₁ κ cψ
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L κ₀ * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * (((L : ℝ) ^ (n₁ - 1)) ^ d)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤ εC),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the numerical condition of the composed activity
      max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β)))) εC ≤
        1 / (8 * (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
          rootUnionK d L 1 T.m₁ T.κ0) ^ 3 * c1 d L *
          Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) →
      (Φ : (physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) =
            rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) →
          ∀ T', e θ' T' = e θ T') →
        B ≤ CPE d L (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
          rootUnionK d L 1 T.m₁ T.κ0) (2 * T.κdec - 1) T.κ0 T.κ' *
          (corrF0G T k β p₁ * K0 d L T.κ0 +
            εC * (δ₁ / (2 * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) / (2 * bb * corrU) *
              (((nFibre d L : ℕ) : ℝ) * Real.exp ((2 * T.κdec - 1) * cBr d L)) * K0 d L T.κ0 +
            ((nFibre d L : ℕ) : ℝ) * Real.exp (T.κ0 * cBr d L) * K0 d L T.κ0) → Φ e B) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        Φ e B ∧
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
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
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)
  := by
  classical
  obtain ⟨β₀, hβ₀, HC⟩ := StepTowerG.e0CoeffFamily_class_of_irrelBounds_core_onSet_agree_collar_phi T₀
    hm₀ hhull hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt ϱ hϱ S hS hp
  obtain ⟨Jr, HC'⟩ := HC T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁
    hp0 hp₁ Dt hϱ S hS hp
  subst hϱ
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀
    i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm0 s hm7 hr₀ hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f'
    X₁f'' j₁ hB0 hF0
  have hmem : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 ∈ Finset.Icc 1 k ∧ Aligned (L ^ τ.1.1) τ.1.2.1 ∧
      IsPolyDom C.m₀ τ.1.1 τ.1.2.2 ∧ τ.1.2.1 ∈ τ.1.2.2 := by
    intro τ
    have h : τ.1 ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ T.m₁ (k + 1) ×
        Set (CTorus d L N₁ T.m₁ (k + 1))))).filter
        (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) := by
      rw [← h𝒯]; exact τ.2
    rw [Finset.mem_filter, Finset.mem_product] at h
    exact ⟨h.1.1, h.2⟩
  have hj1 : ∀ τ : {τ // τ ∈ 𝒯E}, 1 ≤ τ.1.1 := fun τ => (Finset.mem_Icc.1 (hmem τ).1).1
  have hjk : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 ≤ k := fun τ => (Finset.mem_Icc.1 (hmem τ).1).2
  have hXp : ∀ τ : {τ // τ ∈ 𝒯E}, IsPolyDom C.m₀ τ.1.1 τ.1.2.2 := fun τ => (hmem τ).2.2.1
  have hy : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.2.1 ∈ τ.1.2.2 := fun τ => (hmem τ).2.2.2
  have hcov : ∀ τ : {τ // τ ∈ 𝒯E}, CovSetup S.G' C.m₀ τ.1.1 (XL τ) (𝒦X τ) := fun τ =>
    covSetup_of_chosen S.hG' hN (Nat.succ_le_succ (hjk τ)) (by have := T.hL; omega) (h𝒦 τ)
  have hXLpoly : ∀ τ : {τ // τ ∈ 𝒯E}, IsPolyDom C.m₀ τ.1.1 (XL τ) := fun τ => by
    rw [hXL τ]
    exact isPolyDom_union (hXp τ) (isPolyDom_cubeAt hN ((hjk τ).trans (Nat.le_succ k)) τ.1.2.1)
      (hy τ) (mem_cubeAt τ.1.2.1)
  -- the per-label settings
  have h81 : L ^ s ∣ N₁ := (pow_dvd_pow L hm7).trans hN
  obtain ⟨N₁', hN1', hc⟩ := exists_finer_torusG T.m₁ s h81
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, hSg⟩ := settings_family_castLocalB_spec (N₁' := N₁')
    (m₁' := T.m₁ + s) hc S.hG' hB0 hF0 S.hG (by have := T.hL; omega) (m₀ := C.m₀) hN (by omega)
    (fun τ : {τ // τ ∈ 𝒯E} => τ.1.1) XL 𝒦X hj1 hjk hXLpoly hcov hϱ₁ (bgR0_le_rhoSepG T.m₁ T.hd T.hL) hs₁
    hrho (c₁ := L ^ s) (le_of_eq (pow_add L T.m₁ s)) hr₀
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ
    hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL
    hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴
    H hH εC hεC0 hmr hsa hεC hE hεnum
  have hκ1 : 1 ≤ κdec := by linarith
  have hE1 : 0 ≤ Real.exp ((κdec - 1) * cG d L) := (Real.exp_pos _).le
  have hBτ' : ∀ τ, 0 ≤ Bτ τ * (Real.exp ((κdec - 1) * cG d L)) := fun τ => mul_nonneg (hBτ τ) hE1
  have hCI' : 0 ≤ CI * (Real.exp ((κdec - 1) * cG d L)) := mul_nonneg hCI hE1
  have hKL' : 0 ≤ KL * (Real.exp ((κdec - 1) * cG d L)) := mul_nonneg hKL hE1
  have hEbI' : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
      Bτ τ * (Real.exp ((κdec - 1) * cG d L)) ≤ CI * (Real.exp ((κdec - 1) * cG d L)) * P.E₀ * (((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃)) :=
    fun τ h => by
      have := mul_le_mul_of_nonneg_right (hEbI τ h) hE1
      calc _ ≤ _ := this
        _ = _ := by ring
  have hEbL' : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ * (Real.exp ((κdec - 1) * cG d L)) ≤ KL * (Real.exp ((κdec - 1) * cG d L)) * P.E₀ := fun τ h => by
    have := mul_le_mul_of_nonneg_right (hEbL τ h) hE1
    calc _ ≤ _ := this
      _ = _ := by ring
  have hsupp : ∀ τ : {τ // τ ∈ 𝒯E}, treeLenCovOne C.m₀ τ.1.1 (XL τ) ≤
      treeLenCovOne C.m₀ τ.1.1 τ.1.2.2 + cG d L := fun τ => by
    rw [hXL τ]
    exact treeLenCovOne_support_le hN ((hjk τ).trans (Nat.le_succ k)) (hXp τ) (hy τ)
  have hEbd' : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
      ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
        Bτ τ * (Real.exp ((κdec - 1) * cG d L)) * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 (XL τ)) :=
    fun τ r hr => irrel_bound_transfer (hBτ τ) hκ1 (hsupp τ) (hEbd τ r hr)
  exact @HC' C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS
    hE₀ i₀ i₁ hdom XL 𝒦X hXL hcov hN hm0 s hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
    Gk Gj X₀ X₁f hX₁ hBs hFs cψ hcψ hMX δc hdm hα hsm hconn hrow hopt κdec κ₀ hκ₀ hκdec hκ h1
    hlog 𝒮 hchart (fun τ => Bτ τ * Real.exp ((κdec - 1) * cG d L)) hBτ' hEbd' (CI * Real.exp ((κdec - 1) * cG d L)) (KL * Real.exp ((κdec - 1) * cG d L)) α₃ n₁ hCI' hKL' hα₃
    hEbI' hEbL' hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hSg hc7 R hR hsmR
    hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE
    hεnum


open Classical in
/-- The class chain (XCollar), with `B` bounded by an explicit constant. -/
theorem e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet_agree_collar_phi {κmin : ℝ} (T₀ : StepTower κmin)
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
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : r₀ ≤ 1431)
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
        -- the sets `𝒮 τ` (containing the composed step data) lie in the term domain, `Ψ(y)·Ψ(y)` in
        -- the slit plane
        {𝒮 : {τ // τ ∈ 𝒯E} → Set (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)}
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
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
        (_ : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
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
      (Φ : (physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) → ℝ → Prop) →
      (∀ (e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ) (B : ℝ),
        -- the spin covariance of `e`
        (∀ Q : Matrix (Fin 2) (Fin 2) ℝ, Qᵀ * Q = 1 →
          ∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) =
            rotRaw (cmat Q) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
          ∀ T', e θ' T' = e θ T') →
        B ≤ CPE 3 3 (2 * (K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + rootUnionK 3 3 1 T.m₁ T.κ0) +
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
  obtain ⟨β₀, h3, H⟩ := StepTowerG.e0CoeffFamily_class_of_irrelBounds_X_onSet_agree_collar_phi
    T₀.toG rfl (T₀.hhull_toG_of_stepHullMin hHull) hA p hcR (alpha_three_cast hαR)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ hδ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS
    hp => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ (by simpa using h3N) hN ν hν0
    (by simpa using hν) β hβ (by rw [radius_three_cast]; exact hct) p₁ hp0 (by rw [e]; exact hp₁)
    (StepTower.scaleDataG_of_fixed T Dt) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm S hS hp
  obtain ⟨Jr, G'⟩ := G
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hr₀ hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, G''⟩ := @G' C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN (by omega) 4 (by omega) (by have h := index_condition_shift_collar hm7 hr₀; norm_num at h ⊢; linarith) (by rw [rhoSepG_three]; exact Fluctuation.rhoSep_le_minSep_three hrho) hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [e, h27, h18, ← corrF0_toG] at G''
  exact @G'' cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum

open Classical in
/-- The class chain (XCollar), with `B` bounded by an explicit constant. -/
theorem StepTowerG.e0CoeffFamily_class_of_irrelBounds_X_onSet_agree_collar {d L N : ℕ} [NeZero L] {κmin : ℝ} (T₀ : StepTowerG d L N κmin)
    (hm₀ : T₀.m₀ = 1) (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T₀.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T₀.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {cR αR : ℝ} (hcR : 0 < cR) (hαR : 2 * αR < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTowerG d L N κmin, T.m₀ = T₀.m₀ → T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → T.κ0 = T₀.κ0 → T.κ' = T₀.κ' → T.δ = T₀.δ →
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_ : L ^ T.m₀ ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      cR * (L : ℝ) ^ (-(αR * ((k : ℝ) + 1))) ≤ T.t →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      ∀ (_ : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (_ : ϱ = rhoSepG d L T.m₁)
        (S : StepSetting d L N₁ T.m₁ k N ϱ)
        (_ : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (hp : 0 < S.p₁),
      ∃ Jr : S.JointRep T.t (2 * p₁),
      ∀ (C : StepClass d L N₁ T.m₁ k N ϱ) (z : RootIdx d L N₁ T.m₁ (k + 1))
        (𝒯E : Finset (ℕ × CTorus d L N₁ T.m₁ (k + 1) × Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ T.m₁ (k + 1) ×
            Set (CTorus d L N₁ T.m₁ (k + 1))))).filter
          (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
        {P : Consts} {Dom : FieldDom d L N₁ T.m₁ (k + 1) N ϱ} {ϱ₁ ϱ₀ ϱ₃ : ℝ}
        {cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 d)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 < S.β) (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin N)
        (_ : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1)
            ϱ, (∀ i, j < i → G.Ω i = ∅) →
          ∀ Ψ : Fld d L N₁ T.m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
          (∀ x x', jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x = jBlock d L (N₁ * L ^ T.m₁) (k + 1) j x' →
            Ψ x = Ψ x') →
          Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
        (XL 𝒦X : {τ // τ ∈ 𝒯E} → Set (CTorus d L N₁ T.m₁ (k + 1)))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, XL τ = τ.1.2.2 ∪ box (cbase (cellSide L C.m₀ T.m₁ τ.1.1) τ.1.2.1 -
          natT fun _ => L / 2 * cellSide L C.m₀ T.m₁ τ.1.1) (L * cellSide L C.m₀ T.m₁ τ.1.1))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ChosenOne C.m₀ τ.1.1 (XL τ) (𝒦X τ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∃ (W₀ : Finset (CTorus d L N₁ T.m₁ (k + 1)))
          (E₀ : Finset (CTorus d L N₁ T.m₁ (k + 1) × CTorus d L N₁ T.m₁ (k + 1))),
          ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ τ.1.1 (𝒦X τ) W₀ ∧
            bondCost (scaleW L C.m₀ T.m₁ τ.1.1) E₀ = treeLenCovOne C.m₀ τ.1.1 (XL τ))
        (_ : L ^ C.m₀ ∣ N₁) (_ : 1 ≤ C.m₀) {s : ℕ} (_ : s ≤ C.m₀)
        (_ : (((5 * L + 13) * L ^ s : ℕ) : ℝ) + r₀ * (L : ℝ) ≤ (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (C.m₀ + 1))
        (_ : rhoSepG d L T.m₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s)))
        (_ : bgR0 d L ≤ ϱ₁) (_ : ϱ₁ ≤ Balaban.LargeField.minSep L (L ^ (T.m₁ + s)))
        (Gk0 : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₀)
        (Gj0 : GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₃)
        {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ T.m₁ (k + 1))} {j₁ : ℕ}
        (_ : BgSetting N S.G' Gk0 Gj0 S.a₁ S.ν cB BG κ r₀ T.t δ₃ X₀' X₁f' j₁)
        (_ : FlSetting N S.G' Gk0 (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG T.t δ₃ KcL Cx
          c₂ BG₂ δ₁ δfl X₁f''),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ₁)
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet d L (N₁ * L ^ T.m₁) (k + 1) ϱ)
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus d L N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν cB BG κ r₀ T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν κ BG T.t δ₃
          KcL Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀ {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ T.m₁) {δc : ℝ}
        (_ : decDomMargin d L N BG κ (xiC1 d * T.t) < δc)
        (_ : K4 d L N BG κ * (xiC1 d * T.t) < coerciveConst d / 2)
        (_ : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) S.ν)
        {κdec κ₀ : ℝ} (_ : 0 ≤ κ₀) (_ : 3 * κ₀ + 3 ≤ κdec)
        (_ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (_ : 1 ≤ (κ / 2 - 1) / 2)
        (_ : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) /
            2)
        -- the sets `𝒮 τ` (containing the composed step data) lie in the term domain, `Ψ(y)·Ψ(y)` in
        -- the slit plane
        {𝒮 : {τ // τ ∈ 𝒯E} → Set (RawData d L (N₁ * L ^ T.m₁) (k + 1) N)}
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
        {CI KL α₃ : ℝ} (n₁ : ℕ) (_ : 0 ≤ CI) (_ : 0 ≤ KL) (_ : 0 < α₃)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, τ.1.1 + n₁ ≤ k →
          Bτ τ ≤ CI * P.E₀ * ((((L : ℝ)⁻¹ ^ (k - τ.1.1)) ^ ((d : ℝ) + α₃))))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, k < τ.1.1 + n₁ → Bτ τ ≤ KL * P.E₀)
        (_ : aEnt d L + 1 ≤ κ₀) (_ : 0 ≤ 2 * T.κdec - 1)
        (_ : (2 * T.κdec - 1) * ((L : ℝ) ^ (C.m₀ - 1) + 2 * (d : ℝ) *
          (L : ℝ) ^ C.m₀ * ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L) + 1 ≤ 2 * κdec)
        (F₁L : {τ // τ ∈ 𝒯E} → DecParams S.G' × RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
          ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (s : DecParams S.G') (D : BgData S.G' N),
          (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : {τ // τ ∈ 𝒯E} → Dec2.DecParams (coverOf S.G') ×
          Edat (stepG d L N₁ T.m₁ k ϱ) N →
          ((stepG d L N₁ T.m₁ k ϱ).Ω 1 × Fin N → ℂ) ×
            ((stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
          StrictDataM (stepG d L N₁ T.m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ p : Dec2.DecParams (coverOf S.G') ×
            Edat (stepG d L N₁ T.m₁ k ϱ) N,
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
            Background.Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2
              (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
            Background.Small (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).2 (cK2' d L N (famConst d L BG₂ κ)
                * δ₁) ∧
            SupBounds (stepG d L N₁ T.m₁ k ϱ) (SolL τ p).1
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
            (∀ δα' : (stepG d L N₁ T.m₁ k ϱ).Ω 1 → ℂ,
              Background.Small (stepG d L N₁ T.m₁ k ϱ) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
              Dec2.DecFixed (coverOf S.G') (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁)
                  S.ν p.1
                false p.2.2.1 p.2.1
                (pertSource (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1
                    p.2.2.2.2) δα' →
              δα' = (SolL τ p).2))
        (FkL : ∀ τ : {τ // τ ∈ 𝒯E}, RawData d L (N₁ * L ^ T.m₁) (k + 1) N →
          ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (FkL τ) {p | ∃ D : BgData (Gk τ) N,
          InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ D : BgData (Gk τ) N,
          InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
          FkL τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
            bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
        (_ : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ T.m₁ k ϱ) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG d L N₁ T.m₁ k ϱ) (compWeight L S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        (_ : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (_ : 2 ≤ R)
        (_ : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * T.t))) + 5 * (R * δ₁) ≤ bgC1 d L N)
        (_ : R * δ₁ ≤ deltaStar d L N) (_ : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
        (_ : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        (_ : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
          c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (G₁ : physParam N S →
          {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ T.m₁ (k + 1))))
            (fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ)) z} →
          ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ q u Φ, G₁ θ q u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ q.1.1.1.1 (𝒦X q.1.1) S.a₁ S.ν
              S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L q.1.1) (SolL q.1.1)
              (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ T.m₁ k
                  ϱ)
                (compWeight L S.a₁) (FkL q.1.1)
                (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ q.1.1.1.1 q.1.1.1.2.1
                  q.1.1.1.2.2 r.1 r.2))
              (S.blockU z) u t q.1.2
              ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
          else 0)
        (_ : S.p₁ ≤ ρ)
        (𝒴C : Finset (Set (CTorus d L N₁ T.m₁ (k + 1))))
        (_ : 𝒴C = Finset.univ.biUnion fun τ => polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ))
        (H : physParam N S → {Y // Y ∈ 𝒴C} → ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
        (_ : ∀ θ Y u Φ, H θ Y u Φ =
          if (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ∈
              XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 T.t ∧ ‖u‖ < corrU then
            ∑ τ, if Y.1 ∈ polyDom S.G' (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) then
              (S.β : ℂ) * (evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k ϱ)
                  (compWeight L S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2
                    r.1 r.2)) (S.blockU z) u 0
                  Y.1 ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ) -
                evDec (X₁f τ) C.m₀ τ.1.1 (𝒦X τ) S.a₁ S.ν S.hG'
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁L τ) (SolL τ)
                (eTermFun S.G' (Gk τ) (Gj τ) (stepG d L N₁ T.m₁ k ϱ)
                  (compWeight L S.a₁) (FkL τ)
                  (fun r => (S.β : ℂ)⁻¹ * irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2
                    r.1 r.2)) (S.blockU z) 0 0
                  Y.1 ((θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N), S.hatOf 1 ρ hp Φ))
            else 0
          else 0)
        {εC : ℝ} (_ : 0 ≤ εC)
        (_ : 0 < markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (_ : 2 * corrU * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (_ : corrU / (δ₁ / (2 * markedRad d L N k S.a₁ κ cψ
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ L ^ d : ℕ) : ℝ) * (c1 d L * ((((L : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ d) * P.E₀ *
          (2 * K0 d L κ₀ * (CI * Real.exp ((κdec - 1) * cG d L) * (1 - (L : ℝ) ^ (-α₃))⁻¹ +
            n₁ * (KL * Real.exp ((κdec - 1) * cG d L)) * (((L : ℝ) ^ (n₁ - 1)) ^ d)))) *
          Real.exp ((2 * T.κdec - 1) * (2 * (d : ℝ) * (L : ℝ) ^ C.m₀ *
            ((((L ^ (C.m₀ - 1)) ^ d : ℕ)) : ℝ) * c1 d L)))) ≤ εC),
      -- the old densities are analytic along the path
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
        AnalyticAt ℂ
          (fun q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N =>
            Edens C.m₀ C.Tm j q.1 q.2)
          (Jr.PJ j (rawOf D, (s : ℂ) • Balaban.Fluctuation.yhat x))) →
      -- the numerical condition of the composed activity
      max (2 ^ 2 * (2 * (S.β * prop33EpsEtaScaled d L N T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
          (lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) 0 0 (1 / S.β)))) εC ≤
        1 / (8 * (2 * (K0 d L T.κ0 + 1) + (K0 d L T.κ0 + rootUnionK d L 1 T.m₁ T.κ0) +
          rootUnionK d L 1 T.m₁ T.κ0) ^ 3 * c1 d L *
          Real.exp (((2 * T.κdec - 1) - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) →
      ∃ e : physParam N S → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
          (K := k + 1) 1 (k + 1) Set.univ) → ℂ, ∃ B : ℝ,
        (∀ T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ),
          AnalyticOnNhd ℂ (fun θ => e θ T') (physV S S.a₁ S.ν T.t) ∧
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
              B * Real.exp (-T.κ' * dExt T')) ∧
          (∀ θ, e θ T' ≠ 0 → rootCube (m₀ := 1) z ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T'))) ∧
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          Jr.E0locJ C z (rawOf D) = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T' ∧
          (S.withDatumH D).E0locH C z = ∑ T', e ((⟨rawOf D, rawOf_mem_rawSub _⟩ :
            rawSub N S.G'), (0 : CTorus d L N₁ T.m₁ (k + 1) → Fin N → ℂ)) T') ∧
        ∀ ε : ℝ, ε ≤ T.t → ∀ q : Fld d L N₁ T.m₁ (k + 1) N × Fld d L N₁ T.m₁ (k + 1) N,
          XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2 →
          Jr.densE0 C (rootSite z) q = ∑ T',
            (if h : clipRaw S.G' q ∈ rawSub N S.G' then
              e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T' else 0)
:= by
  obtain ⟨β₀, hβ₀, Hφ⟩ := StepTowerG.e0CoeffFamily_class_of_irrelBounds_X_onSet_agree_collar_phi T₀ hm₀ hhull hA p hcR hαR
  refine ⟨β₀, hβ₀, fun T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ => ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt ϱ hϱ S hS hp
  obtain ⟨Jr, Hφ'⟩ := Hφ T hm₀T hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ h3N hN₁ ν hν0 hν β hβ hct p₁
    hp0 hp₁ Dt hϱ S hS hp
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm0 s hm7 hr₀ hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, HG⟩ := @Hφ' C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm0 s hm7 hr₀ hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum
  obtain ⟨e, B, -, h⟩ := @HG cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum
    (fun _ _ => True) (fun _ _ _ _ => trivial)
  exact ⟨e, B, h⟩

open Classical in
/-- **The class chain with the per-label bound in `d(X)`, at every tower radius, at a collar
`r₀ ≤ 1431`.** -/
theorem e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet_agree_collar {κmin : ℝ} (T₀ : StepTower κmin)
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
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀) (_ : r₀ ≤ 1431)
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
        -- the sets `𝒮 τ` (containing the composed step data) lie in the term domain, `Ψ(y)·Ψ(y)` in
        -- the slit plane
        {𝒮 : {τ // τ ∈ 𝒯E} → Set (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)}
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          Dom.dom τ.1.1 (C.Tm.gs τ.1.1 τ.1.2.2) r.1 r.2 ∧
            dot (r.1 τ.1.2.1) (r.1 τ.1.2.1) ∈ Complex.slitPlane)
        -- the per-label bounds of the irrelevant parts in `d(X)` (P1 (3.128), open)
        (Bτ : {τ // τ ∈ 𝒯E} → ℝ) (_ : ∀ τ, 0 ≤ Bτ τ)
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ r ∈ 𝒮 τ,
          ‖irrelTorus C.m₀ C.Tm i₀ i₁ τ.1.1 τ.1.2.1 τ.1.2.2 r.1 r.2‖ ≤
            Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1.1 τ.1.2.2))
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
        (_ : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν BG κ T.t
            (X₁f τ) BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
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
  classical
  obtain ⟨β₀, h3, H⟩ := StepTowerG.e0CoeffFamily_class_of_irrelBounds_X_onSet_agree_collar T₀.toG rfl
    (T₀.hhull_toG_of_stepHullMin hHull) hA p hcR (alpha_three_cast hαR)
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ hδ k hk N₁ _ h3N hN ν hν0 hν β hβ hct p₁ hp0 hp₁ Dt S hS
    hp => ?_⟩
  obtain ⟨h0, -, h'⟩ := StepTower.agree_rates T₀ T
  have e : (((3 : ℕ) : ℝ)) ^ (k * (3 - 2)) = 3 ^ k := by norm_num
  have G := H T.toG rfl hm₁ hBG hBG₂ hκ h0 h' hδ k hk N₁ (by simpa using h3N) hN ν hν0
    (by simpa using hν) β hβ (by rw [radius_three_cast]; exact hct) p₁ hp0 (by rw [e]; exact hp₁)
    (StepTower.scaleDataG_of_fixed T Dt) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm S hS hp
  obtain ⟨Jr, G'⟩ := G
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 hr₀ hrho hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, G''⟩ := @G' C z 𝒯E h𝒯 P Dom ϱ₁ ϱ₀ ϱ₃ cB BG κ r₀ δ₃ KcL Cx c₂ BG₂ δ₁ δfl bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN (by omega) 4 (by omega) (by have h := index_condition_shift_collar hm7 hr₀; norm_num at h ⊢; linarith) (by rw [rhoSepG_three]; exact Fluctuation.rhoSep_le_minSep_three hrho) hϱ₁ hs₁ Gk0 Gj0 X₀' X₁f' X₁f'' j₁ hB0 hF0
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum
  have h27 : ∀ a b : ℝ, ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) * a / b) = 27 * a / b := by
    intro a b
    norm_num
    ring
  have h18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  simp only [e, h27, h18] at G''
  exact @G'' cψ hcψ hMX δc hdm hα hsm hconn hrow κdec κ₀ hκ₀ hκdec hκ h1 hlog 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hκe hκH hrate F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 hc7 R hR hsmR hRs hsmall hnum hnum' ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum

end Balaban.Inhabited
