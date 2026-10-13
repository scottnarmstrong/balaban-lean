/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.DetPackageFromTowerG
public import Balaban.Inhabited.LevelStepSettingGeneral

/-!
# Analyticity of the regrouped determinant terms on the chart

The regrouped determinant term `E.detGrouped D X` is the finite sum of the terms `E.term D T` over
the sets `T` of cubes with collar hull `X`; this index set `detCollarFibre m₀ X` does not depend on
the datum.  Hence the regrouped term is analytic wherever each term is.

* `DetExpansionLocC.detGrouped_analyticOnNhd_rawSub`: in the parametrization of the landed
  `analyticOnNhd_rawSub` (a raw datum of the subspace `rawSub`, the datum being `bgOfRaw`), the
  map `e ↦ E.detGrouped (bgOfRaw e.1 e.2) X` is analytic on the preimage in `rawSub` of the chart
  `XiCRaw`.
* `DetExpansionLocC.detGrouped_analyticOnNhd_physV`: the same on the parameter space
  `physParam = rawSub × sources`, on the open set `physV`; the source coordinate does not enter.
* `DetExpansionLocC.detGrouped_chart_family`: the bundle of analyticity on both charts, the bound
  at the hull rate and locality on the hull, for chart data.
* `DetExpansionLocC.detGroupedC_chart_family`: the same for the centred regrouped terms `detGroupedC q`.
* `StepTowerG.detGrouped_chart_family_fromTowerG`: the bundle at the family of
  `StepTowerG.detPackage_fromTowerG` (odd `L = 2 q + 1`, general `d`, `N`).
* `detGrouped_chart_family_fromTower`: the case `d = L = 3`, `N = 2`, `q = 1` of the previous one.

The analyticity is in the raw datum of the subspace of data, as for the terms.  Nothing is asserted
about the inclusion of the class domain in the chart.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Polymer Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

/-- **Analyticity of the regrouped terms on the relative chart.**  The map
`e ↦ E.detGrouped (bgOfRaw e.1 e.2) X` is analytic on the preimage in `rawSub` of `XiCRaw`: a
finite sum, over the fibre `detCollarFibre m₀ X` independent of the datum, of the terms of
`analyticOnNhd_rawSub`. -/
theorem DetExpansionLocC.detGrouped_analyticOnNhd_rawSub
    (E : DetExpansionLocC S m₀ z eps κ'' cdet) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun e : rawSub N S.G' => E.detGrouped (bgOfRaw e.1 e.2) X)
      (((↑) : rawSub N S.G' → RawData d L (N₁ * L ^ m₁) (k + 1) N) ⁻¹'
        XiCRaw S.G' S.a S.ν (k + 1) 1 eps) := by
  unfold DetExpansionLocC.detGrouped detCollarGrouped
  have h := fun T => E.analyticOnNhd_rawSub H T
  intro e he
  have := Finset.analyticAt_fun_sum (detCollarFibre m₀ X) fun T _ => h T e he
  exact this

/-- **Analyticity of the regrouped terms on the physical chart.**  On the parameter space
`physParam = rawSub × sources`, the map `e ↦ E.detGrouped (bgOfRaw e.1.1 e.1.2) X` is analytic on
`physV`; the source coordinate does not enter. -/
theorem DetExpansionLocC.detGrouped_analyticOnNhd_physV
    (E : DetExpansionLocC S m₀ z eps κ'' cdet) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun e : physParam N S => E.detGrouped (bgOfRaw e.1.1 e.1.2) X)
      (physV S S.a₁ S.ν eps) := by
  have h := E.detGrouped_analyticOnNhd_rawSub H X
  let g : physParam N S →L[ℂ] rawSub N S.G' := ContinuousLinearMap.fst ℂ _ _
  refine h.comp (g.analyticOnNhd _) fun e he => ?_
  exact he.1

/-- **The regrouped determinant terms on the chart.**  Under `3 ≤ L`, `L ^ m₀ ∣ N₁`,
`3 ≤ L ^ (m₀ + m₁)`, `0 ≤ cdet`, `0 ≤ κ''` and `BgHyp`, for every `X`:
1. analytic on the relative chart (in `rawSub`);
2. analytic on `physV` in `physParam`;
3. for data of the chart, `‖E.detGrouped D X‖ ≤ hullConst · exp (-hullRate · sizeJ X)`;
4. for data of the chart agreeing at every site of `X`, the regrouped terms at `X` are equal. -/
theorem DetExpansionLocC.detGrouped_chart_family
    (E : DetExpansionLocC S m₀ z eps κ'' cdet) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    (hL : 3 ≤ L) (hN : L ^ m₀ ∣ N₁) (h3 : 3 ≤ L ^ (m₀ + m₁)) (hc : 0 ≤ cdet) (hκ : 0 ≤ κ'')
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun e : rawSub N S.G' => E.detGrouped (bgOfRaw e.1 e.2) X)
        (((↑) : rawSub N S.G' → RawData d L (N₁ * L ^ m₁) (k + 1) N) ⁻¹'
          XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      AnalyticOnNhd ℂ (fun e : physParam N S => E.detGrouped (bgOfRaw e.1.1 e.1.2) X)
        (physV S S.a₁ S.ν eps) ∧
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ‖E.detGrouped D X‖ ≤
          hullConst d L κ'' cdet * Real.exp (-hullRate d L κ'' * sizeJ m₀ (k + 1) X)) ∧
      (∀ D D₂ : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        XiCData S.G' S.a S.ν (k + 1) 1 eps D₂ →
        (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          E.detGrouped D X = E.detGrouped D₂ X) :=
  ⟨E.detGrouped_analyticOnNhd_rawSub H X, E.detGrouped_analyticOnNhd_physV H X,
    fun _ hD => E.detGrouped_bound hL hN hc hκ hD X,
    fun _ _ hD hD₂ h => E.detGrouped_local hL hN h3 hD hD₂ h⟩

/-- **Analyticity of the centred regrouped terms on the relative chart.**  The map
`e ↦ E.detGroupedC q (bgOfRaw e.1 e.2) X` is analytic on the preimage in `rawSub` of `XiCRaw`: a
finite sum, over the fibre `detCollarFibreC q X` independent of the datum, of the terms of
`analyticOnNhd_rawSub`. -/
theorem DetExpansionLocC.detGroupedC_analyticOnNhd_rawSub
    (E : DetExpansionLocC S m₀ z eps κ'' cdet) (H : BgHyp d L (k + 1) ϱ S.a S.ν) (q : ℕ)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun e : rawSub N S.G' => E.detGroupedC q (bgOfRaw e.1 e.2) X)
      (((↑) : rawSub N S.G' → RawData d L (N₁ * L ^ m₁) (k + 1) N) ⁻¹'
        XiCRaw S.G' S.a S.ν (k + 1) 1 eps) := by
  unfold DetExpansionLocC.detGroupedC detCollarGroupedC
  have h := fun T => E.analyticOnNhd_rawSub H T
  intro e he
  exact Finset.analyticAt_fun_sum _ fun T _ => h T e he

/-- The centred regrouped terms on the physical chart. -/
theorem DetExpansionLocC.detGroupedC_analyticOnNhd_physV
    (E : DetExpansionLocC S m₀ z eps κ'' cdet) (H : BgHyp d L (k + 1) ϱ S.a S.ν) (q : ℕ)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun e : physParam N S => E.detGroupedC q (bgOfRaw e.1.1 e.1.2) X)
      (physV S S.a₁ S.ν eps) := by
  have h := E.detGroupedC_analyticOnNhd_rawSub H q X
  let g : physParam N S →L[ℂ] rawSub N S.G' := ContinuousLinearMap.fst ℂ _ _
  refine h.comp (g.analyticOnNhd _) fun e he => ?_
  exact he.1

/-- **The centred regrouped determinant terms on the chart.**  Under `q + 2 ≤ L`, `1 ≤ q`,
`L ^ m₀ ∣ N₁`, `3 ≤ L ^ (m₀ + m₁)`, `0 ≤ cdet`, `0 ≤ κ''` and `BgHyp`, for every `X`: analytic on
the relative chart, analytic on `physV`, bounded at the hull rate for data of the chart, local on
`X` for data of the chart. -/
theorem DetExpansionLocC.detGroupedC_chart_family
    (E : DetExpansionLocC S m₀ z eps κ'' cdet) (H : BgHyp d L (k + 1) ϱ S.a S.ν)
    {q : ℕ} (hq : 1 ≤ q) (hL : q + 2 ≤ L) (hN : L ^ m₀ ∣ N₁) (h3 : 3 ≤ L ^ (m₀ + m₁))
    (hc : 0 ≤ cdet) (hκ : 0 ≤ κ'')
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun e : rawSub N S.G' => E.detGroupedC q (bgOfRaw e.1 e.2) X)
        (((↑) : rawSub N S.G' → RawData d L (N₁ * L ^ m₁) (k + 1) N) ⁻¹'
          XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      AnalyticOnNhd ℂ (fun e : physParam N S => E.detGroupedC q (bgOfRaw e.1.1 e.1.2) X)
        (physV S S.a₁ S.ν eps) ∧
      (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        ‖E.detGroupedC q D X‖ ≤
          hullConst d L κ'' cdet * Real.exp (-hullRate d L κ'' * sizeJ m₀ (k + 1) X)) ∧
      (∀ D D₂ : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        XiCData S.G' S.a S.ν (k + 1) 1 eps D₂ →
        (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          E.detGroupedC q D X = E.detGroupedC q D₂ X) :=
  ⟨E.detGroupedC_analyticOnNhd_rawSub H q X, E.detGroupedC_analyticOnNhd_physV H q X,
    fun _ hD => E.detGroupedC_bound (by omega) hN hc hκ hD X,
    fun _ _ hD hD₂ h => E.detGroupedC_local hq hL hN h3 hD hD₂ h⟩

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Localization.DecEquiv Matrix

open Classical in
/-- **The bundle at the general tower.**  For `T : StepTowerG d L N κmin`, odd `L = 2 q + 1`, a
scale `k ≥ 1` and the scale conditions of `StepTowerG.detPackage_fromTowerG`, there is one family
`z ↦ E z` of records with the term formula such that for every root `z` and every `X` the centred
regrouped terms `detGroupedC q` are analytic on the relative chart and on `physV`, bounded at the
hull rate for data of the chart, and local on the hull.  No class-domain inclusion is asserted. -/
theorem StepTowerG.detGrouped_chart_family_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {q : ℕ} (hLq : L = 2 * q + 1)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t
          ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
          ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight L 1) 1 ν (rho4 d L N T.BG T.κ) D y T') ∧
      ∀ z (X : Set (CTorus d L N₁ T.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun e : rawSub N (T.step k hk N₁ ν β p₁).G' =>
            (E z).detGroupedC q (bgOfRaw e.1 e.2) X)
          (((↑) : rawSub N (T.step k hk N₁ ν β p₁).G' →
              RawData d L (N₁ * L ^ T.m₁) (k + 1) N) ⁻¹'
            XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t) ∧
        AnalyticOnNhd ℂ (fun e : physParam N (T.step k hk N₁ ν β p₁) =>
            (E z).detGroupedC q (bgOfRaw e.1.1 e.1.2) X)
          (physV (T.step k hk N₁ ν β p₁) 1 ν T.t) ∧
        (∀ D : BgData (T.step k hk N₁ ν β p₁).G' N,
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
          ‖(E z).detGroupedC q D X‖ ≤
            hullConst d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
                ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L T.κ /
                  (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ)))) *
              Real.exp (-hullRate d L
                ((T.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) *
                sizeJ 1 (k + 1) X)) ∧
        (∀ D D₂ : BgData (T.step k hk N₁ ν β p₁).G' N,
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D →
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D₂ →
          (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGroupedC q D X = (E z).detGroupedC q D₂ X) := by
  obtain ⟨E, hE, -⟩ := T.detPackage_fromTowerG hLq k hk N₁ hLN hN5 hν0 hν β p₁
  have hN : L ^ 1 ∣ N₁ := by simpa using hLN
  have hq1 : 1 ≤ q := by have := T.hL; omega
  have h3 : 3 ≤ L ^ (1 + T.m₁) :=
    calc 3 ≤ L := T.hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (1 + T.m₁) := Nat.pow_le_pow_right (by have := T.hL; omega) (by omega)
  have hH := bgHyp_lvG (k := k) T.hd T.hL (bgR0_le_rhoSepG (m₁ := T.m₁) T.hd T.hL) hν0 hν
  exact ⟨E, hE, fun z X =>
    (E z).detGroupedC_chart_family hH hq1 (by have := T.hL; omega) hN h3 T.detConst_nonneg
      T.detRate_nonneg X⟩

open Classical in
/-- **The bundle at the shared tower.**  For a tower `T`, a scale `k ≥ 1` and the scale
conditions of `detPackage_fromTower`, there is one family `z ↦ E z` of records with the term
formula such that for every root `z` and every `X` the regrouped terms are analytic on the
relative chart and on `physV`, bounded at the hull rate for data of the chart, and local on the
hull.  No class-domain inclusion is asserted. -/
theorem detGrouped_chart_family_fromTower {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN5 : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t (towerDetRate T.κ)
          (towerDetConst T.κ),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D y T') ∧
      ∀ z (X : Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
        AnalyticOnNhd ℂ (fun e : rawSub 2 (T.step k hk N₁ ν β p₁).G' =>
            (E z).detGrouped (bgOfRaw e.1 e.2) X)
          (((↑) : rawSub 2 (T.step k hk N₁ ν β p₁).G' →
              RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ⁻¹'
            XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t) ∧
        AnalyticOnNhd ℂ (fun e : physParam 2 (T.step k hk N₁ ν β p₁) =>
            (E z).detGrouped (bgOfRaw e.1.1 e.1.2) X)
          (physV (T.step k hk N₁ ν β p₁) 1 ν T.t) ∧
        (∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) *
            Real.exp (-hullRate 3 3 (towerDetRate T.κ) * sizeJ 1 (k + 1) X)) ∧
        (∀ D D₂ : BgData (T.step k hk N₁ ν β p₁).G' 2,
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D₂ →
          (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGrouped D X = (E z).detGrouped D₂ X) := by
  classical
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h := T.toG.detGrouped_chart_family_fromTowerG (q := 1) rfl k hk N₁ h3N hN5 hν0
    (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTower.toG_m₁, StepTower.toG_κ, StepTower.toG_t, StepTower.toG_BG,
    StepTower.toG_δ] at h
  have e1 : (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate T.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 T.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ))) = towerDetConst T.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  obtain ⟨E, hE, hf⟩ := h
  have hC1 : ∀ z D X, (E z).detGroupedC 1 D X = (E z).detGrouped D X :=
    fun z D X => (E z).detGroupedC_one hN D X
  refine ⟨E, hE, fun z X => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hf z X
  simp only [hC1] at a1 a2 a3 a4
  exact ⟨a1, a2, a3, a4⟩

end Balaban.Inhabited
