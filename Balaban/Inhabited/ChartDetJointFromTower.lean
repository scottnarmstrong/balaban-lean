/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerOfG
public import Balaban.Inhabited.UniformChartMargins
public import Balaban.Inhabited.SourceActivityFromTower
public import Balaban.Inhabited.DetPackageFromTower
public import Balaban.Inhabited.ExpSourceChartFromTower
public import Balaban.Inhabited.SourceFamilyRelativeFromTower
public import Balaban.Inhabited.StepOutputPhysical
public import Balaban.Inhabited.StepTowerScaleLemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The chart, margins and determinant family at one shared tower

`scale_chart_det_joint_fromTower` restates the conclusion of `scale_chart_det_joint` for one tower
`T : StepTower κmin` and its per-scale package `D : StepScaleData T …`.  There is no second tower
call: the marked-disc statements are proved from `D.core`, the zero-source activity records come
from `sourceActivityC_scale_fromTower`, the chart datum is `D.xi`, and the determinant family is the
one of `detPackage_fromTower`.

`stepPieces_fromTower` puts the landed from-tower conclusions (source activity on one label system,
determinant package, exponential chart identity, source family, hull-rate inequality, constants
record) side by side for the same `T` and the same `D`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology Metric Matrix Balaban.Localization.DecEquiv

section Joint

variable {κmin : ℝ}

open Classical in
/-- **The chart ball, the marked-disc statements, the zero-source activity records, the chart
datum and the determinant family at one tower.**  After `T`, choose `β₀, C_E, C_F`.  For every
scale, torus, mass, `β ≥ β₀`, cutoff `0 < p₁ ≤ A₁ (log β_k)^p` and `D : StepScaleData T …`, at the
step `T.step k hk N₁ ν β p₁`: the chart ball of `hatStepK_chartBall`; the margins of
`scale_markedDisc_margin` for `b = β_k` at `T.κ`, `T.t`; the membership of the masked tangent in
`FlBallLC` (the statement of `scale_markedDisc_mem_flBallLC` at the constants of `T`, proved from
`D.core`); the zero-source activity records (real and complex, one label system, rate
`κ_H = 2 κ_dec - 1`); the chart datum `D.xi`; and one family `z ↦ E z` of determinant records with
the term formula. -/
theorem scale_chart_det_joint_fromTower (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
      (∃ r : ℝ, 0 < r ∧
        (∀ q : ↥(rawSub 2 (T.step k hk N₁ ν β p₁).G'),
          ‖(q : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) - rawOf (T.step k hk N₁ ν β p₁).D'‖ < r →
            (q : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) ∈
              XiCRaw (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t) ∧
        (∀ g₀ ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2,
          ∀ (q : ↥(rawSub 2 (T.step k hk N₁ ν β p₁).G'))
            (g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ),
          ‖(q : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) - rawOf (T.step k hk N₁ ν β p₁).D'‖ < r →
          ∑ x, ∑ i, ‖g x i - g₀ x i‖ < 1 - ∑ x, ∑ i, ‖g₀ x i‖ →
            (q, g) ∈ physV (N := 2) (T.step k hk N₁ ν β p₁) 1 ν T.t)) ∧
      (Real.sqrt ((2 : ℕ) : ℝ) *
          (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
            (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) ≤
          T.t * covSupMaxC 3 3 2 T.κ / (2 * (covSupMaxC 3 3 2 T.κ + 1)) ∧
        T.t * covSupMaxC 3 3 2 T.κ / (2 * (covSupMaxC 3 3 2 T.κ + 1)) < T.t / 2 ∧
        ((17 / 16 : ℝ) + 1 / 16) * ((17 / 16 : ℝ) + 1 / 16) *
          (Real.sqrt ((2 : ℕ) : ℝ) *
            (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
              (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ *
                lvCpsi T.κ T.t (β * 3 ^ k)))) ≤ 81 * T.t / 128 ∧
        81 * T.t / 128 < T.t) ∧
      (∀ F₁ : DecParams (lvTop N₁ T.m₁ k (rhoSep T.m₁)) ×
            RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ),
        (∀ (s : DecParams (lvTop N₁ T.m₁ k (rhoSep T.m₁)))
            (D₀ : BgData (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 2),
          (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) ν D₀ →
          ∀ (φ : (lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ)
            (α : (lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ),
          IsDecBg (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (rho4 3 3 2 T.BG T.κ)
            s D₀ φ α → F₁ (s, rawOf D₀) = (φ, α)) →
        ∀ (s : DecParams (lvTop N₁ T.m₁ k (rhoSep T.m₁))), (∀ P, ‖s P‖ < Real.exp T.κ) →
        ∀ D₀ : BgData (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 2,
          XiCData (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (k + 1) 1 T.t D₀ →
        ∀ ψh : unitPts (lvTop N₁ T.m₁ k (rhoSep T.m₁)) × Fin 2 → ℂ,
          (∀ q, ‖ψh q‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)) →
        ∀ (Z : Finset (unitPts (lvTop N₁ T.m₁ k (rhoSep T.m₁)))) (u w ρ τ : ℂ),
          ‖u‖ < 17 / 16 → ‖w‖ < 1 / 16 → ‖ρ‖ < 17 / 16 → ‖τ‖ ≤ 1 / 16 →
          (ρ + τ) • markedHatPsiF 1 ν
              (isLevel_lvTop (N₁ := N₁) (m₁ := T.m₁) (k := k) (ϱ := rhoSep T.m₁))
              (((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Z u w s (rawOf D₀) ψh ∈
            FlBallLC (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.t) ∧
      (∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
        ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
        ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁)
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 0,
        ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁)
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) 0,
          BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
          BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
          BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) ∧
      (T.κ' + 3 * T.κ0 + c1 3 3 + 3 / 2 ≤ 2 * T.κdec - 1 ∧
        ∃ κout : ℝ, κout = 3 / 2 * T.κdec ∧ T.κdec ≤ κout ∧
          κout ≤ min T.κ' (T.κ' - T.κ0 - 1)) ∧
      XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
        (T.step k hk N₁ ν β p₁).D' ∧
      ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp T.κ) < 1 ∧
      T.κ' ≤ (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
        (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) ∧
      ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
          DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t (towerDetRate T.κ) (towerDetConst T.κ),
        ∀ z D' T', (E z).term D' T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D' y T' := by
  classical
  obtain ⟨β₀, CE, CF, h2, hCE, hCF, H⟩ := sourceActivityC_scale_fromTower T hA p
  refine ⟨β₀, CE, CF, h2, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  have hb : 0 < β * 3 ^ k := by have := D.beta_pos; positivity
  obtain ⟨r, hr, hr'⟩ := hatStepK_chartBall (N₁ := N₁) k T.m₁ hk hν0.le hν T.t_pos
  obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := scale_markedDisc_margin T.κ T.t_pos hk hb
  have hbU : (T.step k hk N₁ ν β p₁).betaU = β * 3 ^ k := hatStepK_betaU k T.m₁ hk ν β p₁ T.δ
  -- the marked disc, from `D.core`
  have hmark : ∀ F₁ : DecParams (lvTop N₁ T.m₁ k (rhoSep T.m₁)) ×
            RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 →
          ((lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ),
        (∀ (s : DecParams (lvTop N₁ T.m₁ k (rhoSep T.m₁)))
            (D₀ : BgData (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 2),
          (∀ P, ‖s P‖ < Real.exp T.κ) →
          InUnionDomainC (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (bgC0 3 3 2) (c7 3 3 2 T.BG T.κ) ν D₀ →
          ∀ (φ : (lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 × Fin 2 → ℂ)
            (α : (lvTop N₁ T.m₁ k (rhoSep T.m₁)).Ω 1 → ℂ),
          IsDecBg (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (rho4 3 3 2 T.BG T.κ)
            s D₀ φ α → F₁ (s, rawOf D₀) = (φ, α)) →
        ∀ (s : DecParams (lvTop N₁ T.m₁ k (rhoSep T.m₁))), (∀ P, ‖s P‖ < Real.exp T.κ) →
        ∀ D₀ : BgData (lvTop N₁ T.m₁ k (rhoSep T.m₁)) 2,
          XiCData (lvTop N₁ T.m₁ k (rhoSep T.m₁)) (compWeight 3 1) ν (k + 1) 1 T.t D₀ →
        ∀ ψh : unitPts (lvTop N₁ T.m₁ k (rhoSep T.m₁)) × Fin 2 → ℂ,
          (∀ q, ‖ψh q‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)) →
        ∀ (Z : Finset (unitPts (lvTop N₁ T.m₁ k (rhoSep T.m₁)))) (u w ρ τ : ℂ),
          ‖u‖ < 17 / 16 → ‖w‖ < 1 / 16 → ‖ρ‖ < 17 / 16 → ‖τ‖ ≤ 1 / 16 →
          (ρ + τ) • markedHatPsiF 1 ν
              (isLevel_lvTop (N₁ := N₁) (m₁ := T.m₁) (k := k) (ϱ := rhoSep T.m₁))
              (((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ Z u w s (rawOf D₀) ψh ∈
            FlBallLC (lvLow N₁ T.m₁ k (rhoSep T.m₁)) T.t := by
    intro F₁ hF₁ s hs D₀ hD₀ ψh hψh Z u w ρ τ hu hw hρ hτ
    have hcψ : 0 ≤ lvCpsi T.κ T.t (β * 3 ^ k) := D.cψ_pos.le
    have hB : 0 ≤ Real.sqrt ((2 : ℕ) : ℝ) * (‖(((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k))) := by
      have hmem := compWeight_three_mem hk
      have hC0 : 0 ≤ covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ :=
        covSupConstC_nonneg (by norm_num) (by norm_num) (by linarith [hmem.1]) T.κ
      positivity
    have hrad : ((17 / 16 : ℝ) + 1 / 16) * ((17 / 16 : ℝ) + 1 / 16) *
        (Real.sqrt ((2 : ℕ) : ℝ) * (‖(((β * 3 ^ k) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
          (covSupConstC 3 3 2 (compWeight 3 (1 : ℝ) k) T.κ * lvCpsi T.κ T.t (β * 3 ^ k)))) <
        T.t :=
      lt_of_le_of_lt hm4 hm5
    exact markedDisc_hatPsiF_mem_flBallLC D.core hk (isLevel_lvLow hk) isLevel_lvTop _ hcψ
      T.large_block T.dom_margin T.coer_margin T.δc_small hF₁ hs hD₀ hψh Z hB hrad hu hw hρ hτ
  -- the zero-source activity records
  have h0 : (0 : Fld 3 3 N₁ T.m₁ (k + 1) 2) ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 := by
    show ∑ x, ∑ i, ‖(0 : Fld 3 3 N₁ T.m₁ (k + 1) 2) x i‖ < 1
    simp
  obtain ⟨𝒴, hdom, Hg⟩ := H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp hp₁ D
  obtain ⟨BR, BC, hact⟩ := Hg 0 h0
  have hκ' : 0 ≤ T.κ0 := T.κ0_nonneg
  have hdet := detPackage_fromTower T k hk N₁ h3N hN hν0.le hν β p₁
  obtain ⟨E, hE, -⟩ := hdet
  refine ⟨⟨r, hr, (hr' β p₁ T.δ).1, (hr' β p₁ T.δ).2⟩, ⟨?_, hm3, ?_, hm5⟩, hmark,
    ⟨𝒴, hdom, BR, BC, hact⟩, ⟨?_, ?_⟩, D.xi, T.det_z, ?_, E, hE⟩
  · rw [hbU, hm1]; exact hm2
  · rw [hbU]; exact hm4
  · rw [T.κ'_eq, T.κdec_eq]; have := one_le_c1 3 3; have := T.κ0_nonneg; linarith
  · refine ⟨3 / 2 * T.κdec, rfl, ?_, ?_⟩
    · have := T.κdec_lower; have := T.κ0_nonneg; linarith
    · have := T.κ'_eq; have := T.κ0_nonneg
      exact le_min (by linarith) (by linarith)
  · have := T.det_rate
    rw [StepTower.det_rate_den]; exact this

end Joint

section Pieces

variable {κmin : ℝ}

open Classical in
/-- **The landed from-tower pieces share one tower and one scale package.**  For a tower
`T : StepTower κmin` with `stepHullMin ≤ κmin`: the hull-rate inequality and the constants record
of `stepOutputPhysical` (independent of the scale); then, after one threshold `β₀` (the maximum of
the thresholds of `sourceActivityC_scale_fromTower` and `sourceFamilyRelative_scale_fromTower`) and
the amplitude constants, for every scale and one `D : StepScaleData T …`, at the step
`T.step k hk N₁ ν β p₁`, all together: the source activity records for every source of the strict
`l^1` ball on one label system, the determinant package (one family `z ↦ E z` with sum, bound,
anchor, locality, covariance and rotation clauses), the chart identity of the exponentiated source,
and the source direct terms as a family over the relative chart. -/
theorem stepPieces_fromTower (T : StepTower κmin) (hT : stepHullMin ≤ κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    3 / 2 * T.κdec ≤ hullRate 3 3
      ((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) ∧
    (∃ C : StepOutputConsts 3 3, C.k0 = T.κ0 ∧ C.kdec = T.κdec ∧ C.k' = T.κ' ∧
      C.kout = 3 / 2 * T.κdec ∧ C.kH = 2 * T.κdec - 1 ∧ C.kapp = T.κ ∧
      C.kdet = (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18 ∧
      C.Bhull = collarB 3 3 ∧ C.lhull = hullRate 3 3 C.kdet ∧
      C.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧
      C.Kall = max (2 * K0 3 3 T.κ0) (rootUnionK 3 3 1 T.m₁ T.κ0) ∧ C.Ktot = C.Kc + C.Kall) ∧
    ∃ β₀ CE CF CE' CF' : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < CE' ∧ 0 < CF' ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
      (∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
        ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
        ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
        ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁)
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
        ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁)
            (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
          BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp0) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
          BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
          BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
            CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)) ∧
      (
      ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1))),
          DetExpansionLocC (T.step k hk N₁ ν β p₁) 1 z T.t (towerDetRate T.κ)
            (towerDetConst T.κ),
        (∀ z D T', (E z).term D T' = ∑ y ∈ (T.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 T.BG T.κ) D y T') ∧
        (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
              (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull, (E z).detGrouped D X =
            rootTrace (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a 1 ν
              (unitQ (T.step k hk N₁ ν β p₁).G') (unitP (T.step k hk N₁ ν β p₁).G')
              ((T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
              (svec (T.step k hk N₁ ν β p₁).G' (bgFieldC (T.step k hk N₁ ν β p₁).G'
                (T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D))
              (bgMultC (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D)) ∧
        (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
            ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate T.κ) (towerDetConst T.κ) *
              Real.exp (-hullRate 3 3 (towerDetRate T.κ) * sizeJ 1 (k + 1) X)) ∧
        (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)), (E z).detGrouped D X ≠ 0 →
            IsPolyDom 1 (k + 1) X ∧
              box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 T.m₁ (k + 1)) ⊆ X) ∧
        (∀ z (D D₂ : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D₂ →
          ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
            (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
            (E z).detGrouped D X = (E z).detGrouped D₂ X) ∧
        (∀ {σ : Equiv.Perm (CTorus 3 3 N₁ T.m₁ (k + 1))},
          GenSymm 3 N₁ T.m₁ (k + 1) (k + 1) 1 σ →
          ∃ Sy : LatSymm (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).G' σ,
            (∀ D : BgData (T.step k hk N₁ ν β p₁).G' 2,
              XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
              XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t (Sy.sym D)) ∧
            ∀ z, (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2) T',
                (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
              ∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
                (X : Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
                (E (rootAct σ z)).detGrouped (Sy.sym D) (σ '' X) = (E z).detGrouped D X) ∧
        (∀ z (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          ∀ {R : Matrix (Fin 2) (Fin 2) ℂ}, Rᵀ * R = 1 →
            (∀ T', (E z).term (D.rot R) T' = (E z).term D T') ∧
            ∀ X : Set (CTorus 3 3 N₁ T.m₁ (k + 1)),
              (E z).detGrouped (D.rot R) X = (E z).detGrouped D X) ∧
        (∀ (D : BgData (T.step k hk N₁ ν β p₁).G' 2),
          XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D →
          ∀ {Q : Matrix (Fin 2) (Fin 2) ℝ}, Qᵀ * Q = 1 →
            XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t
              (D.rot (cmat Q)))) ∧
      (
      ∃ Jr : (T.step k hk N₁ ν β p₁).JointRep T.t (2 * p₁),
      ∃ val : ((((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) ×
            ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ))) →
          (((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 ×
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ,
        (∀ x w σ Θ, val x w σ Θ =
          (-((T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3
            (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
              (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
              (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne (T.step k hk N₁ ν β p₁).hG (T.step k hk N₁ ν β p₁).hG'
                (le_refl (k + 1)) (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν T.t))
            taylorWeight x.1 w.1 σ Θ.1 +
          ((T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2,
            Θ.2 s.1 s.2 *
            dirTermSrc (hatFun (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
              (T.step k hk N₁ ν β p₁).ν T.t (T.step k hk N₁ ν β p₁).hG'
              (((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (onXi (T.step k hk N₁ ν β p₁).G' (T.step k hk N₁ ν β p₁).a₁
                (T.step k hk N₁ ν β p₁).ν T.t
                (fun D' ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                  (flFieldOne (T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    T.BG₂ T.κ (T.step k hk N₁ ν β p₁).a₁ (T.step k hk N₁ ν β p₁).ν D' ψ')
                  s.1 s.2)))
              (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
        ∀ (g : Fld 3 3 N₁ T.m₁ (k + 1) 2) (x : (T.step k hk N₁ ν β p₁).EC),
          (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
          ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
            Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g
                (rawOf (T.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
              val (x, x) (x, x) (τ : ℂ)
                  (rawOf (T.step k hk N₁ ν β p₁).D',
                    fun y i => g y i / ((T.step k hk N₁ ν β p₁).β : ℂ)) -
                val (x, x) (x, x) (τ : ℂ) (rawOf (T.step k hk N₁ ν β p₁).D', 0)) ∧
      (∀ q : ℝ, 0 < q → q ≤ 1 →
        ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁), S = T.step k hk N₁ ν β p₁ →
        ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
              ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
            (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
            (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
              ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
              (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
            (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                  (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                    (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                  (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                  (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                  (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val (physAgΘ S)
                  (AgFDirPair S)),
            I.𝒴 = 𝒴 ∧ I.T = Tt ∧
            ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
                (physVq S 1 ν T.t q),
              (∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
                ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν T.t q,
                  physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                    (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                  (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = Tt) ∧
              ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                    (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β),
                4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                    (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                  CE' * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                    q * CF' * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
                ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
                (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                  AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                    (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                      (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                      T.κ0_ent hKc r.1 r.2).H y Φ)
                    (physVq S 1 ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
                (∀ e (he : e ∈ physVq S 1 ν T.t q) (u : ℂ),
                  labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                      (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                      T.κ0_ent hKc e u =
                    dtAct S 1 (I.atThetaOn S 1 _ hF he)
                      (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                      T.κ0_ent hKc u) ∧
                (∀ e ∈ physVq S 1 ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                  ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                  (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                      (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                      T.κ0_ent hKc e u).H y Φ =
                    I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                      (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                      (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e))) := by
  classical
  obtain ⟨β₁, CE, CF, h2, hCE, hCF, H1⟩ := sourceActivityC_scale_fromTower T hA p
  obtain ⟨β₂, CE', CF', h2', hCE', hCF', H2⟩ := sourceFamilyRelative_scale_fromTower T hA p
  refine ⟨T.kout_le_hullRate hT, stepOutput_consts_physical T hT, max β₁ β₂, CE, CF, CE', CF',
    le_trans h2 (le_max_left _ _), hCE, hCF, hCE', hCF', ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁ D
  refine ⟨H1 k hk N₁ h3N hN ν hν0 hν β (le_trans (le_max_left _ _) hβ) p₁ hp0 hp₁ D,
    detPackage_fromTower T k hk N₁ h3N hN hν0.le hν β p₁,
    expSourceChart_scale_fromTower T k hk N₁ ν hν0 hν β p₁ hp0 D, ?_⟩
  intro q hq hq1 S hS hp
  exact H2 k hk N₁ h3N hN ν hν0 hν β (le_trans (le_max_right _ _) hβ) p₁ hp0 hp₁ q hq hq1 D S
    hS hp

end Pieces

section Instance

open Classical in
/-- **Non-vacuity of `stepPieces_fromTower` at `k = 1`, `N₁ = 18`, `ν = 1/81`, `p₁ = 1`.**  For the
tower of `exists_stepTower stepHullMin` there is a coupling `β` above the threshold of the pieces
(with `A₁ = 1`, `p = 0`) at which `StepScaleData` holds, and at which the hull-rate inequality, the
zero-source activity record with `κ_H = 2 κ_dec - 1` on one label system, and the determinant
family with the term formula are all present. -/
theorem stepPieces_instance :
    ∃ T : StepTower stepHullMin, ∃ β : ℝ, 2 ≤ β ∧
      Nonempty (StepScaleData T 1 le_rfl 18 (1 / 81) β 1) ∧
      3 / 2 * T.κdec ≤ hullRate 3 3
        ((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) ∧
      (∃ 𝒴 : Finset (Set (CTorus 3 3 18 T.m₁ (1 + 1))),
        ∃ _hdom : ∀ Y ∈ 𝒴, IsDj 1 (1 + 1) Y,
        ∃ BR : StepActivityBound (T.step 1 le_rfl 18 (1 / 81) β 1)
            (zeroClass 3 3 18 T.m₁ 1 2 (rhoSep T.m₁)) 0,
        ∃ BC : StepActivityBoundC (T.step 1 le_rfl 18 (1 / 81) β 1)
            (zeroClass 3 3 18 T.m₁ 1 2 (rhoSep T.m₁)) 0,
          BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH) ∧
      ∃ E : ∀ z : Torus 3 (18 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))),
          DetExpansionLocC (T.step 1 le_rfl 18 (1 / 81) β 1) 1 z T.t (towerDetRate T.κ)
            (towerDetConst T.κ),
        ∀ z D' T', (E z).term D' T' = ∑ y ∈ (T.step 1 le_rfl 18 (1 / 81) β 1).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 (1 / 81) (rho4 3 3 2 T.BG T.κ) D' y T' := by
  classical
  obtain ⟨T⟩ := exists_stepTower stepHullMin
  obtain ⟨βray, hβray, hscale⟩ := T.scale (A₁ := 1) one_pos 0
  obtain ⟨hull, -, β₀, CE, CF, CE', CF', h2, -, -, -, -, H⟩ :=
    stepPieces_fromTower T le_rfl (A₁ := 1) one_pos 0
  have hβ : max βray β₀ ≥ βray := le_max_left _ _
  have hβ' : β₀ ≤ max βray β₀ := le_max_right _ _
  have hp : (1 : ℝ) ≤ pLog 1 0 (max βray β₀ * 3 ^ 1) := by simp [pLog]
  obtain ⟨D⟩ := hscale 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num)
    (by norm_num) (max βray β₀) hβ 1 one_pos hp
  obtain ⟨hact, hdet, -⟩ := H 1 le_rfl 18 (by norm_num) (by norm_num) (1 / 81) (by norm_num)
    (by norm_num) (max βray β₀) hβ' 1 one_pos hp D
  obtain ⟨𝒴, hdom, Hg⟩ := hact
  have h0 : (0 : Fld 3 3 18 T.m₁ (1 + 1) 2) ∈ l1Ball 3 3 18 T.m₁ (1 + 1) 2 := by
    show ∑ x, ∑ i, ‖(0 : Fld 3 3 18 T.m₁ (1 + 1) 2) x i‖ < 1
    simp
  obtain ⟨BR, BC, -, -, hLb, hLbC, -, -, -, -, -, -, -, -, hκH, hκHC, -⟩ := Hg 0 h0
  obtain ⟨E, hE, -⟩ := hdet
  exact ⟨T, max βray β₀, le_trans hβray hβ, ⟨D⟩, hull, ⟨𝒴, hdom, BR, BC, hLb, hLbC, hκH, hκHC⟩,
    E, hE⟩

end Instance

end Balaban.Inhabited
