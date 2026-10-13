/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetStepInstance
public import Balaban.Inhabited.DetCauchyBgActivityWitness
public import Balaban.Inhabited.LevelRayTower
public import Balaban.Inhabited.DetOutputTermsWitnessG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the localized determinant family

`d = L = 3`, `N = 2`.

* `detOutputTerms_nonempty`: at the step `hatStep m₁ 1 1 1` (`k = 1`, `N₁ = 9`, the constant unit
  block datum), for one choice of `(m₁, BG, κ, t)` supplied by the tower `directWitness_core_amp`:
  the rate condition holds, the datum of the step is a datum of the chart, and
  - for every `z` the record `DetExpansionLocC` has an element with the terms
    `∑_{y ∈ B(z)} detActivityBg D y T`, the rate `(κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18 > 0`
    and the scale-uniform constant `27 · covBLogMax 3 3 κ / (1 - z)` (which is at least `1`);
  - there is `r₀ > 0` such that every datum within `r₀` of the datum of the step is a datum of the
    chart, and the terms of every element of the record differ from those at the datum of the step
    by at most `2 c_det e^{-κ'' d(T)} ‖rawOf D₂ - rawOf D'‖ / r₀`;
  - the Jacobian `det C^{(k)1/2}` is the exponential of the sum of the terms of all roots;
  - Theorem 3.1 (a) holds with the determinant terms and this constant for all marks `E1MarksC`
    with rate at most the rate of the determinant terms.  (No element of `E1MarksC` is constructed
    here or elsewhere; this conjunct is the statement for all such marks.)
* `detExpansionLocC_nonempty`: the record `DetExpansionLocC` is inhabited (rule 10).
* `detExpansionLocC_scale_of_tower`: from the output of the numerical tower (the hypotheses are
  conclusions of `tower_core_rates`), at the step `hatStepK k m₁ hk ν β p₁ δ` of every scale
  `k ≥ 1`, every torus `3 ∣ N₁`, `5 < N₁`, and every mass `0 ≤ ν`, `ν · 3^{2(k+1)} ≤ 1`: the datum
  of the step is a datum of the chart and for every `z` the record has an element with the same
  rate and the same constant, which involve neither `k`, nor `N₁`, nor `ν`, nor `β`.
* `detExpansionLocC_scale`: the instance at the tower `tower_core_rates 2` with the rates
  `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1` of the general-scale
  activity bound: moreover `κ' ≤ (κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18`, so that the rate
  hypothesis of Theorem 3.1 (a) holds for marks of rate `κ'`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Analysis Balaban.SmallField.Def6 Balaban.Polymer Balaban.Inhabited.LevelStep

/-- `log 2 + 2 log (detDeg 3 3 + 1) < 57`. -/
theorem log_detDeg_three_lt :
    Real.log 2 + 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) < 57 := by
  have hΔ0 : (0 : ℝ) < ((detDeg 3 3 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hz := detDeg_three_rate (le_refl (57 : ℝ))
  have h := Real.log_neg (by positivity) hz
  rw [log_cutRate hΔ0 57] at h
  linarith

/-- `27 · covBLogMax 3 3 κ / (1 - z) ≥ 1` for `κ ≥ 0` and `0 ≤ z < 1`: the constant of the
determinant terms is not small. -/
theorem one_le_detConstMax_three {κ z : ℝ} (hκ : 0 ≤ κ) (hz0 : 0 ≤ z) (hz : z < 1) :
    (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ / (1 - z)) := by
  have h1 : (1 : ℝ) ≤ covBLogMax 3 3 κ :=
    one_le_covBLog 3 (L := 3) (by norm_num) (a := 2) (by norm_num) _ hκ
  have hden : 0 < 1 - z := by linarith
  have h2 : (1 : ℝ) ≤ (1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ / (1 - z) := by
    rw [le_div_iff₀ hden]
    push_cast
    nlinarith
  have h3 : (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ 3 := by norm_num
  nlinarith

open Classical in
/-- **Non-vacuity of the localized determinant family, of the uniform constant, of the oscillation
estimate and of the step theorems.**  At the step `hatStep m₁ 1 1 1` and one choice of
`(m₁, BG, κ, t)`: the rate condition holds, the rate of the determinant terms is positive, the
datum of the step is a datum of the chart, and

* for every `z` the record `DetExpansionLocC` has an element whose terms are the sums over
  `y ∈ B(z)` of the activities, with the scale-uniform constant;
* that constant is at least `1`;
* the terms of every element of the record are Lipschitz in the datum near the datum of the
  step, with a constant proportional to their bound;
* the Jacobian of the step is the exponential of the sum of the terms of all roots;
* Theorem 3.1 (a) holds with these determinant terms for all marks whose rate is at most the rate
  of the determinant terms. -/
theorem detOutputTerms_nonempty :
    ∃ (m₁ : ℕ) (BG κ t : ℝ) (S : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁)),
      S = hatStep m₁ 1 1 1 ∧ 0 < t ∧
      ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
      0 < (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
        (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) ∧
      XiCData S.G' S.a S.ν (1 + 1) 1 t S.D' ∧
      (∀ z, ∃ E : DetExpansionLocC S 0 z t
          ((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
            (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)))
          (((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
            (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
        ∀ D T, E.term D T = ∑ y ∈ S.blockU z,
          detActivityBg 0 S.a S.a₁ S.ν (rho4 3 3 2 BG κ) D y T) ∧
      (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ∧
      (∃ r₀ : ℝ, 0 < r₀ ∧ ∀ D₂ : BgData S.G' 2, ‖rawOf D₂ - rawOf S.D'‖ < r₀ →
        XiCData S.G' S.a S.ν (1 + 1) 1 t D₂ ∧
        ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) {κ'' cdet : ℝ}
          (E : DetExpansionLocC S 0 z t κ'' cdet) (T),
          ‖E.term D₂ T - E.term S.D' T‖ ≤
            2 * (cdet * Real.exp (-κ'' * dExt T)) / r₀ * ‖rawOf D₂ - rawOf S.D'‖) ∧
      (∀ {κ'' cdet : ℝ} (E : ∀ z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))),
          DetExpansionLocC S 0 z t κ'' cdet),
        S.covSqrtC.det = Complex.exp (∑ z, ∑ T, (E z).term S.D' T)) ∧
      ∀ (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))
        (C : StepClass 3 3 9 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0) (I : E1MarksC S C BS z),
        I.κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
          (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) →
        S.E0locC C z = ∑ T, (∑ y ∈ S.blockU z,
            detActivityBg 0 S.a S.a₁ S.ν (rho4 3 3 2 BG κ) S.D' y T + interpCoeff I T) ∧
        ∀ T, ‖∑ y ∈ S.blockU z,
            detActivityBg 0 S.a S.a₁ S.ν (rho4 3 3 2 BG κ) S.D' y T + interpCoeff I T‖ ≤
          (CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
              (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) +
            ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
              (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))) *
            Real.exp (-I.κ' * dExt T) := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, -⟩ := directWitness_core_amp 2 1
  have hκ57 : (57 : ℝ) ≤ κ := by
    have e : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
    rw [e] at hκ
    linarith
  have hz := detDeg_three_rate hκ57
  have hd0 : 0 < (3 : ℕ) := by norm_num
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin 3 3 2 BG κ (xiC1 3 * t) := by
      have : 0 < K4 3 3 2 BG κ := K4_pos hC.hS.fam.2.1 hd0
      have := one_le_xiC1 3
      unfold decDomMargin; positivity
    linarith
  set S := hatStep m₁ 1 1 1 with hS
  have hD : XiCData S.G' (compWeight 3 1) nuW (1 + 1) 1 t S.D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hconn : HatConn S.G' := LevelPair.hatConn
  have hN : (3 : ℕ) ^ 0 ∣ 9 := by norm_num
  have hlam : 0 < κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ) := by
    have := log_detDeg_three_lt
    linarith
  have hz0 : 0 ≤ ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) := by positivity
  refine ⟨m₁, BG, κ, t, S, rfl, ht0, hz, by positivity, hD, fun z =>
    exists_detExpansionLocC_of_chart_uniform (m₀ := 0) S hC hδc hMX hdm hα hsmX hconn hN hz z,
    one_le_detConstMax_three (by linarith) hz0 hz, ?_, fun E => ?_, fun z C BS I hI => ?_⟩
  · obtain ⟨r₀, hr₀, hdisc⟩ := exists_chart_disc hC.HBp hD
    refine ⟨r₀, hr₀, fun D₂ h => ⟨?_, fun z κ'' cdet E T => ?_⟩⟩
    · have h1 := hdisc D₂ 1 (by simpa using h)
      rw [one_smul, add_sub_cancel] at h1
      exact xiCData_of_rawOf_mem h1
    · obtain ⟨A, hA, hAv⟩ := E.analyticAt_raw T
      exact (norm_sub_le_of_chart_disc hA hAv (fun D' hD' => E.bound D' hD' T) hdisc h).2
  · exact det_covSqrtC_eq_exp_sum_term E hC hMX hdm hα hsmX hD
  · obtain ⟨h2, h3, -⟩ := thm31aC_of_chart (m₀ := 0) S hC hδc hMX hdm hα hsmX hconn hD hN hz z I hI
    exact ⟨h2, h3⟩

/-- **`DetExpansionLocC` is inhabited**: at the step `hatStep m₁ 1 1 1`, whose datum is a datum
of the chart `Ξ^c(𝔹_2; 1, t)`, for every root `z`, with a positive rate. -/
theorem detExpansionLocC_nonempty :
    ∃ (m₁ : ℕ) (t κ'' cdet : ℝ), 0 < t ∧ 0 < κ'' ∧
      XiCData (hatStep m₁ 1 1 1).G' (hatStep m₁ 1 1 1).a (hatStep m₁ 1 1 1).ν (1 + 1) 1 t
        (hatStep m₁ 1 1 1).D' ∧
      ∀ z, Nonempty (DetExpansionLocC (hatStep m₁ 1 1 1) 0 z t κ'' cdet) := by
  obtain ⟨m₁, BG, κ, t, S, rfl, ht, -, hκ, hD, hE, -⟩ := detOutputTerms_nonempty
  exact ⟨m₁, t, _, _, ht, hκ, hD, fun z => ⟨(hE z).choose⟩⟩

/-- **The localized determinant family at every scale and on every torus, from the output of the
numerical tower.**  Let `(m₁, c, BG, κ, t, c₂, BG₂, δc)` satisfy the conclusions of
`tower_core_rates` used here (`4 ≤ m₁`, `0 < t`, `FlCore` at the reference pair, the cap and the
margins of the covariance chart) and the rate condition `e^κ > 2 (detDeg 3 3 + 1)²`.  Then at the
step `hatStepK k m₁ hk ν β p₁ δ` of every scale `k ≥ 1`, every torus parameter `N₁` with `3 ∣ N₁`,
`5 < N₁` and every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`: the datum of the step is a datum of the
chart `Ξ^c(𝔹_{k+1}; 1, t)`, and for every `z` the record `DetExpansionLocC` (cubes of side
`3^{k+1+1+m₁}`, `m₀ = 1`) has an element whose terms are the sums over `y ∈ B(z)` of the
activities, with the rate `(κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18` and the constant
`27 · covBLogMax 3 3 κ / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)`.  The rate and the constant involve
neither `k`, nor `N₁`, nor `ν`, nor `β`, `p₁`, `δ`, nor `z`. -/
theorem detExpansionLocC_scale_of_tower {m₁ : ℕ} {c BG κ t c₂ BG₂ δc : ℝ} (h4 : 4 ≤ m₁)
    (ht0 : 0 < t)
    (hC₀ : FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3)
      (Cchi 3 3) c₂ BG₂ t)
    (hMX : cstarX 3 3 * Real.exp (N0 3 3 * κ) ≤ ((3 : ℕ) : ℝ) ^ m₁)
    (hdm : decDomMargin 3 3 2 BG κ (xiC1 3 * t) < δc)
    (hα : K4 3 3 2 BG κ * (xiC1 3 * t) < coerciveConst 3 / 2)
    (hsmX : δc ^ 2 * smallConstX 3 3 κ ≤ 1 / 4)
    (hz : ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) :
    XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
        (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' ∧
      ∀ z, ∃ E : DetExpansionLocC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 z t
          ((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
            (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)))
          (((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
            (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
        ∀ D T, E.term D T = ∑ y ∈ (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 BG κ) D y T := by
  have hC := Classical.choice (flCore_three_transport ⟨hC₀⟩)
  have h := detExpansionLocC_scale_of_towerG (d := 3) (L := 3) (N := 2) le_rfl le_rfl le_rfl h4
    ht0 hC hMX hdm hα hsmX hz k hk N₁ h3N hN hν0 (by simpa using hν) β p₁ δ
  rw [rhoSepG_three] at h
  exact h

/-- **The localized determinant family at every scale and on every torus.**  With the rates
`κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`, `κ' = (3/2) κ_dec + κ₀ + 1` of the general-scale
activity bound (`stepActivityBound_zeroClass_direct_physical_scale`), the tower
`tower_core_rates 2` supplies `m₁, t, BG, κ` such that

* the rate condition `e^κ > 2 (detDeg 3 3 + 1)²` holds;
* the rate of the determinant terms is at least `κ'`:
  `κ' ≤ (κ - log 2 - 2 log (detDeg 3 3 + 1)) / 18`, the rate hypothesis of Theorem 3.1 (a) for
  marks of rate `κ'`;
* the constant `27 · covBLogMax 3 3 κ / (1 - (detDeg 3 3 + 1)² · 2 / e^κ)` is at least `1`;
* at every scale `k ≥ 1`, on every torus `3 ∣ N₁`, `5 < N₁`, for every mass `0 ≤ ν` with
  `ν · 3^{2(k+1)} ≤ 1` and all `β, p₁, δ`, the datum of the step `hatStepK` is a datum of the
  chart and for every `z` the record `DetExpansionLocC` has an element with that rate and that
  constant, whose terms are the sums of the activities.

The constants `m₁, t, BG, κ`, the rate and the constant do not depend on `k`, `N₁`, `ν`, `β`. -/
theorem detExpansionLocC_scale {κ0 κdec κ' : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1)
    (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) (hκ'def : κ' = 3 / 2 * κdec + κ0 + 1) :
    ∃ (m₁ : ℕ) (t BG κ : ℝ), 0 < t ∧
      ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1 ∧
      κ' ≤ (κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
        (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) ∧
      (1 : ℝ) ≤ ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
        (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 ≤ ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β p₁ δ : ℝ,
        XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
            (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' ∧
          ∀ z, ∃ E : DetExpansionLocC (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 z t
              ((κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
                (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)))
              (((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 κ /
                (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
            ∀ D T, E.term D T = ∑ y ∈ (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).blockU z,
              detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 BG κ) D y T := by
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, -, -, -,
    hMX, hdm, hα, hsmX, -⟩ :=
    tower_core_rates 2 (κ0 := κ0) (κdec := κdec) (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have e : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
  rw [e] at hκ
  have hκ57 : (57 : ℝ) ≤ κ := by linarith
  have hz := detDeg_three_rate hκ57
  have hz0 : 0 ≤ ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) := by positivity
  have hlog := log_detDeg_three_lt
  refine ⟨m₁, t, BG, κ, ht0, hz, ?_, one_le_detConstMax_three (by linarith) hz0 hz,
    fun k hk N₁ _ h3N hN ν hν0 hν β p₁ δ =>
      detExpansionLocC_scale_of_tower h4 ht0 hC₀ hMX hdm hα hsmX hz k hk N₁ h3N hN hν0 hν β p₁ δ⟩
  have e18 : (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = 18 := by norm_num
  rw [e18, le_div_iff₀ (by norm_num), hκ'def]
  linarith

end Balaban.Inhabited
