/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHull
public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Inhabited.DetPackageFromTower

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
* `detGrouped_chart_family_fromTower`: the bundle at the family of `detPackage_fromTower`.

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

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Localization.DecEquiv Matrix

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
  obtain ⟨E, hE, -⟩ := detPackage_fromTower T k hk N₁ h3N hN5 hν0 hν β p₁
  have hN : (3 : ℕ) ^ 1 ∣ N₁ := by simpa using h3N
  have h3 : 3 ≤ 3 ^ (1 + T.m₁) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ (1 + T.m₁) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hH := bgHyp_lv (k := k) T.m₁ hν0 hν
  exact ⟨E, hE, fun z X =>
    (E z).detGrouped_chart_family hH (by norm_num) hN h3 (towerDetConst_nonneg T)
      (towerDetRate_nonneg T) X⟩

end Balaban.Inhabited
