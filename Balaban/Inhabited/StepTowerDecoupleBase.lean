/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelChainX
public import Balaban.Fluctuation.LocalClassDensityIrrelBaseSet

/-!
# The class chain at the base settings with the fluctuation radius free (`StepTowerDecoupleBase`)

The landed chain theorem `e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet` takes the radius
`δ₁` of the ball of the layer-constant fluctuation as a variable; the base theorem
`e0CoeffFamily_class_fromTower_of_irrelBounds_base_onSet` fixes it to the step radius `T.t`.
Here it is free:

* `FlNum.mono_fluct`: the numerics `FlNum` hold at every smaller fluctuation radius `δ₁'` and
  bound `δ_fl'` with `N (5 K₂' δ₁' + δ₁') ≤ δ_fl'` (the other conditions on `δ₁`, `δ_fl` are upper
  bounds); `FlNum.at_fluct`: the smallest bound `δ_fl' = N (5 K₂' δ₁' + δ₁')`;
* `step_flSetting_base_dec`: the base `FlSetting` of the step at the fluctuation radius `δ₁` of
  `FlNum … T.t δ₃ δ₁ δfl`;
* `e0CoeffFamily_class_fromTower_of_irrelBounds_base_onSet_dec`: the base theorem at a fluctuation
  radius `δ₁ ≤ T.t`; the step radius `T.t` stays the radius of the step chart, of the background
  data and of `JointRep`.  The conditions of the radius `R δ₁`, `R = 2`, follow from those of the
  tower at `T.t`.  The landed base theorem is the case `δ₁ = T.t`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited Balaban.Polymer
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Matrix Metric Set
  MeasureTheory Balaban.Inhabited.MarkBudgetAudit Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis

/-- **`FlNum` at a smaller fluctuation radius**: the conditions on `δ₁` and `δ_fl` other than
`N (5 K₂' δ₁ + δ₁) ≤ δ_fl` are upper bounds. -/
theorem _root_.Balaban.Localization.FlNum.mono_fluct {d L N : ℕ} [NeZero L]
    {BG BG₂ κ eps δ₃ δ₁ δfl δ₁' δfl' : ℝ} (h : FlNum d L N BG BG₂ κ eps δ₃ δ₁ δfl)
    (hδ0 : 0 < δ₁') (hδ : δ₁' ≤ δ₁) (hfl0 : 0 ≤ δfl') (hfl : δfl' ≤ δfl)
    (hflb : N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁') + δ₁') ≤ δfl') :
    FlNum d L N BG BG₂ κ eps δ₃ δ₁' δfl' := by
  have hc2 : 0 ≤ cK2 d L N := (cK2_pos d L N).le
  have hx2 : 0 ≤ xiK2 d L N := by
    have := cK2_pos d L N
    unfold xiK2; positivity
  have hX1 : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  have hp : (0 : ℝ) ≤ (4 * d + 6) * (2 * d + 1) := by positivity
  have h2 : xiK2 d L N * δfl' ≤ xiK2 d L N * δfl := mul_le_mul_of_nonneg_left hfl hx2
  have h3 : (4 * d + 6) * (2 * d + 1) * (xiK2 d L N * δfl') ≤
      (4 * d + 6) * (2 * d + 1) * (xiK2 d L N * δfl) := mul_le_mul_of_nonneg_left h2 hp
  have h4 : xiC1 d * (xiK2 d L N * δfl') ≤ xiC1 d * (xiK2 d L N * δfl) :=
    mul_le_mul_of_nonneg_left h2 hX1
  exact {
    δ₁_pos := hδ0
    δ₁_le := hδ.trans h.δ₁_le
    B_le := h.B_le
    B_one := h.B_one
    phi_lt := h.phi_lt
    flb := hflb
    δfl_nn := hfl0
    δfl_le_one := hfl.trans h.δfl_le_one
    c1_f := by linarith [h.c1_f]
    star_f := hfl.trans h.star_f
    K1s_f := h.K1s_f
    sm_f := by nlinarith [h.sm_f, mul_le_mul_of_nonneg_left hfl hc2]
    small₃ := by nlinarith [h.small₃]
    th₃ := by nlinarith [h.th₃] }

/-- **`FlNum` at a smaller fluctuation radius `δ₁'` with the smallest fluctuation bound**
`δ_fl' = N (5 K₂' δ₁' + δ₁')`. -/
theorem _root_.Balaban.Localization.FlNum.at_fluct {d L N : ℕ} [NeZero L]
    {BG BG₂ κ eps δ₃ δ₁ δfl δ₁' : ℝ} (h : FlNum d L N BG BG₂ κ eps δ₃ δ₁ δfl)
    (hfam : 0 ≤ famConst d L BG₂ κ) (hδ0 : 0 < δ₁') (hδ : δ₁' ≤ δ₁) :
    FlNum d L N BG BG₂ κ eps δ₃ δ₁' (N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁') + δ₁')) := by
  have hc' : 0 ≤ cK2' d L N (famConst d L BG₂ κ) := Balaban.Localization.cK2'_nonneg hfam
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine h.mono_fluct hδ0 hδ (by positivity) (le_trans ?_ h.flb) le_rfl
  apply mul_le_mul_of_nonneg_left _ hN
  have := mul_le_mul_of_nonneg_left hδ hc'
  linarith

section Base

variable {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **`FlSetting` of the step from the tower at a fluctuation radius `δ₁`**: the fields of the
fluctuation problem come from `FlCore` of the scale record, the numerics from
`FlNum … T.t δ₃ δ₁ δfl`. -/
theorem step_flSetting_base_dec (Dt : StepScaleData T k hk N₁ ν β p₁) {δ₃ δ₁ δfl : ℝ}
    (hnum : FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl) :
    FlSetting 2 (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
      (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν
      T.κ T.BG T.t δ₃ (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ δ₁ δfl Finset.univ := by
  have hC := Dt.core
  exact {
    hS2 := hC.hS2
    SM := hC.SM
    hM2 := hC.hM2
    hPm := precedes_refl _
    hPmp := hC.hPmp
    depm := fun _ _ y _ => Finset.mem_univ y
    num := hnum }

end Base

open Classical in
/-- **The class chain at the tower, base settings and numerics discharged, at a fluctuation radius
`δ₁ ≤ T.t`.**  The statement of `e0CoeffFamily_class_fromTower_of_irrelBounds_base_onSet` with the
radius of the ball of the layer-constant fluctuation (in `FlNum`, `FlSetting`, `FlRealLC`, the
fluctuation solution `SolL` and the marked-radius conditions) a variable `δ₁ ≤ T.t`; the step
radius `T.t` is unchanged elsewhere. -/
theorem e0CoeffFamily_class_fromTower_of_irrelBounds_base_onSet_dec {κmin : ℝ} (T : StepTower κmin)
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
        {P : Consts} {Dom : FieldDom 3 3 N₁ T.m₁ (k + 1) 2 (rhoSep T.m₁)} {δ₃ δ₁ δfl : ℝ}
        {bL : ℝ} (_ : 1 ≤ bL) (_ : bL ≤ scaledC0 3)
        (_ : P.m₀ = C.m₀) (_ : SFTermClauses P Dom C.Tm)
        (_ : 0 ≤ P.E₀) (i₀ i₁ : Fin 2)
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
        (_ : 3 ^ C.m₀ ∣ N₁) (_ : 7 ≤ C.m₀)
        (_ : ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃)
        (_ : FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ δ₁ δfl) (_ : δ₁ ≤ T.t),
      ∃ (Gk : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (Gj : {τ // τ ∈ 𝒯E} → GeneratingSet 3 3 (N₁ * 3 ^ T.m₁) (k + 1) (rhoSep T.m₁))
        (X₀ X₁f : {τ // τ ∈ 𝒯E} → Finset (CTorus 3 3 N₁ T.m₁ (k + 1))),
        (∀ τ, (↑(X₁f τ) : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) = X1 S.G' C.m₀ τ.1.1 (𝒦X τ)) ∧
        (∀ τ, BgSetting 2 S.G' (Gk τ) (Gj τ) S.a₁ S.ν T.c T.BG T.κ 324 T.t δ₃ (X₀ τ) (X₁f τ) τ.1.1) ∧
        (∀ τ, FlSetting 2 S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.κ T.BG T.t δ₃
          (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ δ₁ δfl (X₁f τ)) ∧
        ∀ {cψ : ℝ} (_ : 0 ≤ cψ)
        (_ : HatConn S.G')
        (_ : RowInHat (coverOf S.G') (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) S.ν)
        {κdec : ℝ} (_ : 4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ)
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
        (_ : (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (C.m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
          ((3 : ℕ) : ℝ) ^ C.m₀ * ((((3 ^ (C.m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec)
        (F₁L : {τ // τ ∈ 𝒯E} → DecParams S.G' × RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          (S.G'.Ω 1 × Fin 2 → ℂ) × (S.G'.Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (F₁L τ) {q | (∀ P, ‖q.1 P‖ < Real.exp T.κ) ∧
          ∃ D : BgData S.G' 2, InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) S.ν D ∧
            q.2 = (D.Ψ, D.h)})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ (s : DecParams S.G') (D : BgData S.G' 2),
          (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC S.G' (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin 2 → ℂ)
            (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight 3 S.a₁) S.ν (rho4 3 3 2 T.BG T.κ) s D φ α →
            F₁L τ (s, rawOf D) = (φ, α))
        (SolL : {τ // τ ∈ 𝒯E} → Dec2.DecParams (coverOf S.G') ×
          Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 →
          ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ))
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, AnalyticOnNhd ℂ (SolL τ) {p | (∀ P, ‖p.1 P‖ < Real.exp T.κ) ∧
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 *
              T.t)))
            δ₁ p.2})
        (_ : ∀ τ : {τ // τ ∈ 𝒯E}, ∀ p : Dec2.DecParams (coverOf S.G') ×
            Edat (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2,
          (∀ P, ‖p.1 P‖ < Real.exp T.κ) →
          StrictDataM (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) 2 false (2 * (K4 3 3 2 T.BG T.κ * (xiC1 3 *
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
              (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8)) ∧
            Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).2 (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ)
                * δ₁) ∧
            SupBounds (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (SolL τ p).1
              (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * δ₁) ∧
            (∀ δα' : (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ,
              Small (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) δα' (c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1
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
        (_ : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) S.a₁ S.ν T.BG T.κ T.t
            (X₁f τ) T.BG₂ δ₁,
          D2raw (Gk τ) (Gj τ) (compWeight 3 S.a₁) (FkL τ)
            (d1Triple S.G' (Gk τ) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 S.a₁) t.1.1
              t.2.1 t.2.2) ∈ 𝒮 τ)
        {ρ : ℝ} (_ : 0 < ρ) (_ : ρ ≤ cψ) (_ : ρ < 2 * p₁)
        {bb : ℝ} (_ : 0 < bb)
        (_ : (corrU + bb) * markedRad 3 3 2 k S.a₁ T.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
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
        (_ : 0 < markedRad 3 3 2 k S.a₁ T.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        (_ : 2 * corrU * markedRad 3 3 2 k S.a₁ T.κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
        (_ : corrU / (δ₁ / (2 * markedRad 3 3 2 k S.a₁ T.κ cψ
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) *
          (((2 ^ 3 ^ 3 : ℕ) : ℝ) * (c1 3 3 * ((((3 : ℕ) : ℝ) ^ (1 + C.m₀ + T.m₁)) ^ 3 * P.E₀ *
          (2 * K0 3 3 T.κ0 * (CI * Real.exp ((κdec - 1) * cG 3 3) * (1 - ((3 : ℕ) : ℝ) ^ (-α₃))⁻¹ +
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
  obtain ⟨β₀, hβ₀, HC⟩ := e0CoeffFamily_class_fromTower_of_irrelBounds_X_onSet T hHull hA p
  refine ⟨β₀, hβ₀, ?_⟩
  intro k hk N₁ _ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  obtain ⟨Jr, HC'⟩ := HC k hk N₁ h3N hN₁ ν hν0 hν β hβ p₁ hp0 hp₁ Dt S hS hp
  refine ⟨Jr, ?_⟩
  intro C z 𝒯E h𝒯 P Dom δ₃ δ₁ δfl bL hb₁ hbC hm hcl hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7
    hnumB hnumF hδ₁T
  subst hS
  have hB0 := step_bgSetting_base T Dt hnumB
  have hF0 := step_flSetting_base_dec T Dt hnumF
  have hβS : 0 < (T.step k hk N₁ ν β p₁).β := by
    show 0 < β
    linarith
  obtain ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, HG⟩ := @HC' C z 𝒯E h𝒯 P Dom (rhoSep T.m₁)
    (rhoSep T.m₁) (rhoSep T.m₁) T.c T.BG T.κ 324 δ₃ (levelKc 3 3) (Cchi 3 3) T.c₂ T.BG₂ δ₁ δfl
    bL hb₁ hbC hm hcl hβS hE₀ i₀ i₁ hdom XL 𝒦X hXL h𝒦 hopt hN hm7 le_rfl
    (rhoSep_numeric_of_four T.m₁_four) (bgR0_le_rhoSep _) (rhoSep_le_minSep_of_four T.m₁_four)
    (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
    (X₀' := dataSites (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))) (X₁f' := Finset.univ)
    (X₁f'' := Finset.univ) (j₁ := 1) hB0 hF0
  refine ⟨Gk, Gj, X₀, X₁f, hX₁, hBs, hFs, ?_⟩
  intro cψ hcψ hconn hrow κdec hκ 𝒮 hchart Bτ hBτ hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL hrate
    F₁L hF₁an hF₁ SolL hSolan hSolprop FkL hFkan hFk h𝒮 ρ hρ hρc hρpp bb hbb hab G₁ hG₁ hρp 𝒴C
    h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum
  have hκT3 : 3 ≤ T.κdec := by
    have := T.κdec_lower
    have := T.κ0_nonneg
    linarith
  obtain ⟨hκle, hlog⟩ := rate_consequences hm7 hκT3 (one_le_c1 3 3) hκ hrate
  -- the conditions of the radius `2 δ₁` from those of the tower at `2 T.t`
  have hc2 : 0 < cK2 3 3 2 := cK2_pos 3 3 2
  have hc2' : 0 ≤ cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) := cK2'_nonneg T.fam_nonneg
  have hbg1 : 2 * (compC4 3 * (bgK1 3 3 2 * (xiC1 3 * T.t))) + 5 * (2 * δ₁) ≤ bgC1 3 3 2 := by
    linarith [T.bg1_cap]
  have hstar : 2 * δ₁ ≤ deltaStar 3 3 2 := by linarith [T.t_cap]
  have hbg0 : cK2 3 3 2 * (2 * δ₁) < bgC0 3 3 2 / 2 := by
    have := mul_le_mul_of_nonneg_left (show 2 * δ₁ ≤ 2 * T.t by linarith) hc2.le
    linarith [T.bg0_cap]
  have hcK2 : cK2 3 3 2 * δ₁ ≤ c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8) := by
    have := mul_le_mul_of_nonneg_left hδ₁T hc2.le
    linarith [T.cK2_cap]
  have hcK2' : cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * δ₁ ≤
      c6' 3 3 2 (famConst 3 3 T.BG₂ T.κ) (gamma1 3 / 8) := by
    have := mul_le_mul_of_nonneg_left hδ₁T hc2'
    linarith [T.cK2'_cap]
  exact @HG cψ hcψ (by simpa using T.large_block) T.δc T.dom_margin T.coer_margin T.δc_small
    hconn hrow κdec T.κ0 T.κ0_nonneg (by linarith [T.κdec_lower]) hκ T.κ_one hlog 𝒮 hchart Bτ hBτ
    hEbd CI KL α₃ n₁ hCI hKL hα₃ hEbI hEbL T.κ0_ent (by linarith) hrate F₁L hF₁an hF₁ SolL
    hSolan hSolprop FkL hFkan hFk h𝒮 T.c7_cap 2 le_rfl hbg1 hstar hbg0 hcK2 hcK2' ρ hρ hρc hρpp
    bb hbb hab G₁ hG₁ hρp 𝒴C h𝒴 H hH εC hεC0 hmr hsa hεC hE hεnum

end Balaban.Inhabited
