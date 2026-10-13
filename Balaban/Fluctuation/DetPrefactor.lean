/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetOutputTerms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The prefactor of the determinant terms: uniformity in the scale, and the field dependence

The terms of the localized determinant family (`DetOutputTerms`) are bounded by
`c_det e^{-κ_det d(T)}` with `c_det = L^d · ½ N covBLog d L a_k (a₁/L²) κ / (1 - z)`,
`z = (detDeg d L + 1)² · 2 / e^κ`.

## Uniformity in the scale

The scale `k` enters `c_det` only through the weight `a_k ∈ [1/2, 2]`.

* `covBLogMax d L κ = covBLog d L 2 (2/L²) κ`: the value at the largest weights `a_k = 2`,
  `a₁ = 2`; explicitly `log (2 + 2/L²) + 2 L² √(92 valConstX d) e^{N0 d L κ}`
  (`covBLogMax_eq`).
* `covBLog_le_covBLogMax`: `covBLog d L a (a₁/L²) κ ≤ covBLogMax d L κ` for `a ∈ [1/2, 2]`,
  `0 ≤ a₁ ≤ 2`; `covBLog_compWeight_le_covBLogMax`: under `FlCore` at every scale `k ≥ 1`.  The
  maximum involves neither `k`, nor the torus, nor the datum.
* `exists_detExpansionLocC_of_chart_uniform`: the record `DetExpansionLocC` has an element with
  the constant `L^d · ½ N covBLogMax d L κ / (1 - z)`.

## The size of the prefactor

The constant carries no small factor: `covBLog d L a b κ ≥ 1` for every weight `a ≥ 1/2`
(`one_le_covBLog`; it is at least `½ L² √(92 valConstX d) e^{N0 d L κ}` and grows with `κ`), so
the constant of the record is at least `½ N` (`half_le_detConst`).  The terms themselves do not
involve the coupling `β` (the activities `detActivityBg` are functions of the generating set, the
weights, the mass and the datum only).  The amplitude of the interaction terms of the step is
`ε_H ≤ C (log β_k)^{3p} / √β_k`; the determinant terms have no such factor.  In the class an
energy term is bounded by `E₀ e^{-κ d(X)}`: the determinant terms can only be admitted with
`E₀ ≥ c_det`, or after their part which does not depend on the field has been moved to the vacuum
energy.  Neither is done here; what is proved is the smallness of the field dependence below.

## The field dependence

* `norm_sub_le_of_analyticAt_disc`: a function analytic at the points of a set `U` and bounded by
  `M` on `U` satisfies `‖A q - A p‖ ≤ 2 M / R` if the complex disc `p + t (q - p)`, `|t| < R`,
  `R > 1`, lies in `U` (Schwarz lemma along the complex line through `p` and `q`).
* `exists_chart_disc`: for a datum `D` of the chart there is `r₀ > 0` such that the chart contains
  `rawOf D + t (rawOf D₂ - rawOf D)` whenever `|t| ‖rawOf D₂ - rawOf D‖ < r₀` (the chart is open
  in the subspace `rawSub` of raw data of data; the norm is the supremum norm of raw data).
* `norm_detActivityBg_sub_le_of_disc`, `DetExpansionLocC.norm_term_sub_le_of_disc`: the
  oscillation of an activity, and of a term of the record, between two data joined by such a disc
  of radius `R` is at most `2 · (bound) / R`.
* `exists_norm_detActivityBg_sub_le`, `DetExpansionLocC.exists_norm_term_sub_le`: for every datum
  `D` of the chart there is `r₀ > 0` such that every datum `D₂` with
  `‖rawOf D₂ - rawOf D‖ < r₀` is a datum of the chart and
  `‖term D₂ T - term D T‖ ≤ 2 c_det e^{-κ'' d(T)} ‖rawOf D₂ - rawOf D‖ / r₀`.

The radius `r₀` depends on the datum `D`: the landed openness of the chart gives no radius which
is uniform over the chart, and no comparison of `r₀` with the radius `ε` of the chart.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Finset Matrix

/-! ### The maximum of the constant over the weights -/

section Prefactor

/-- **The maximum of `covBLog d L a_k (a₁/L²) κ` over the weights** `a_k ∈ [1/2, 2]`,
`0 ≤ a₁ ≤ 2`: its value at `a_k = 2`, `a₁ = 2`. -/
noncomputable def covBLogMax (d L : ℕ) (κ : ℝ) : ℝ := covBLog d L 2 (2 / (L : ℝ) ^ 2) κ

/-- `covB4 d L a κ / a = a √(L⁴ · 92 valConstX d e^{2 N0 κ})` for `a > 0`: linear in the weight. -/
theorem covB4_div (d L : ℕ) {a : ℝ} (ha : 0 < a) (κ : ℝ) :
    covB4 d L a κ / a =
      a * Real.sqrt ((L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2))) := by
  unfold covB4 covBsq
  have h : a ^ 4 * (L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2)) =
      (a ^ 2) ^ 2 * ((L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2))) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg a)]
  field_simp

/-- **Uniformity in the weights.**  For `a ∈ [1/2, 2]` and `0 ≤ a₁ ≤ 2`:
`covBLog d L a (a₁/L²) κ ≤ covBLogMax d L κ`. -/
theorem covBLog_le_covBLogMax (d L : ℕ) (κ : ℝ) {a a₁ : ℝ} (ha : a ∈ Set.Icc (1 / 2 : ℝ) 2)
    (h0 : 0 ≤ a₁) (h2 : a₁ ≤ 2) :
    covBLog d L a (a₁ / (L : ℝ) ^ 2) κ ≤ covBLogMax d L κ := by
  obtain ⟨h1, h2'⟩ := ha
  have ha0 : 0 < a := by linarith
  have hLsq : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hb0 : 0 ≤ a₁ / (L : ℝ) ^ 2 := div_nonneg h0 hLsq
  have hb2 : a₁ / (L : ℝ) ^ 2 ≤ 2 / (L : ℝ) ^ 2 := div_le_div_of_nonneg_right h2 hLsq
  have hc0 : (0 : ℝ) ≤ 2 / (L : ℝ) ^ 2 := by positivity
  set M : ℝ := Real.log (2 + 2 / (L : ℝ) ^ 2) with hM
  have hlog2 : Real.log 2 ≤ M := Real.log_le_log (by norm_num) (by linarith)
  have key : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 2 + 2 / (L : ℝ) ^ 2 → |Real.log x| ≤ M := by
    intro x hx1 hx2
    have hx0 : 0 < x := by linarith
    rw [abs_le]
    constructor
    · have h3 : Real.log (1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) hx1
      have e : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
      linarith
    · exact Real.log_le_log hx0 hx2
  have hmax : max |Real.log a| |Real.log (a + a₁ / (L : ℝ) ^ 2)| ≤ M :=
    max_le (key a h1 (by linarith)) (key _ (by linarith) (by linarith))
  have hmaxM : M ≤ max |Real.log 2| |Real.log (2 + 2 / (L : ℝ) ^ 2)| :=
    (le_abs_self _).trans (le_max_right _ _)
  unfold covBLogMax covBLog
  rw [covB4_div d L ha0, covB4_div d L (by norm_num : (0 : ℝ) < 2)]
  have hs := Real.sqrt_nonneg ((L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2)))
  exact add_le_add (hmax.trans hmaxM) (mul_le_mul_of_nonneg_right h2' hs)

/-- **The explicit value of the maximum**:
`covBLogMax d L κ = log (2 + 2/L²) + 2 L² √(92 valConstX d) e^{N0 d L κ}`. -/
theorem covBLogMax_eq (d L : ℕ) (κ : ℝ) :
    covBLogMax d L κ = Real.log (2 + 2 / (L : ℝ) ^ 2) +
      2 * ((L : ℝ) ^ 2 * Real.sqrt (92 * valConstX d) * Real.exp (N0 d L * κ)) := by
  have hc0 : (0 : ℝ) ≤ 2 / (L : ℝ) ^ 2 := by positivity
  have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : Real.log 2 ≤ Real.log (2 + 2 / (L : ℝ) ^ 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hmax : max |Real.log 2| |Real.log (2 + 2 / (L : ℝ) ^ 2)| =
      Real.log (2 + 2 / (L : ℝ) ^ 2) := by
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact max_eq_right h2
  have hv : 0 ≤ valConstX d := by unfold valConstX; positivity
  have hsq : Real.sqrt ((L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2))) =
      (L : ℝ) ^ 2 * Real.sqrt (92 * valConstX d) * Real.exp (N0 d L * κ) := by
    have e : (L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2)) =
        ((L : ℝ) ^ 2 * Real.exp (N0 d L * κ)) ^ 2 * (92 * valConstX d) := by ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
  unfold covBLogMax covBLog
  rw [covB4_div d L (by norm_num : (0 : ℝ) < 2), hmax, hsq]

/-- **The constant is not small**: `covBLog d L a b κ ≥ 1` for every weight `a ≥ 1/2`, every
`L ≥ 1` and `κ ≥ 0`.  (It is at least `½ L² √(92 valConstX d) e^{N0 d L κ}`.) -/
theorem one_le_covBLog (d : ℕ) {L : ℕ} (hL : 1 ≤ L) {a : ℝ} (ha : 1 / 2 ≤ a) (b : ℝ) {κ : ℝ}
    (hκ : 0 ≤ κ) : 1 ≤ covBLog d L a b κ := by
  have ha0 : 0 < a := by linarith
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hL)
  have he : (1 : ℝ) ≤ Real.exp (N0 d L * κ) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp (by positivity))
  have hv : (1 : ℝ) ≤ valConstX d := by
    unfold valConstX
    have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg ((5 : ℝ) ^ d - 1)]
  have hC : (2 : ℝ) ^ 2 ≤ (L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2)) := by
    have h3 : (1 : ℝ) ≤ valConstX d * Real.exp (N0 d L * κ) ^ 2 := by nlinarith
    nlinarith
  have hs : (2 : ℝ) ≤
      Real.sqrt ((L : ℝ) ^ 4 * (92 * (valConstX d * Real.exp (N0 d L * κ) ^ 2))) :=
    Real.le_sqrt_of_sq_le hC
  have hm : 0 ≤ max |Real.log a| |Real.log (a + b)| := (abs_nonneg _).trans (le_max_left _ _)
  unfold covBLog
  rw [covB4_div d L ha0]
  nlinarith

end Prefactor

/-! ### Uniformity in the scale -/

section Scale

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **Uniformity in the scale.**  Under `FlCore` at a scale `k ≥ 1` the weights `a_k` and `a₁`
lie in `[1/2, 2]`, so the constant `covBLog d L a_k (a₁/L²) κ` of the determinant terms is at most
`covBLogMax d L κ`, which involves neither the scale, nor the torus, nor the datum. -/
theorem covBLog_compWeight_le_covBLogMax
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) :
    covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ ≤ covBLogMax d L κ := by
  have hX := xSetting_of_flCore hC hk
  have hw := hC.Sp.weights k hk (Nat.le_succ k)
  exact covBLog_le_covBLogMax d L κ hw (by linarith [hX.haT1]) hX.haT2

omit [NeZero N₁] [NeZero L] in
/-- The same from the explicit ranges `L ≥ 3`, `9/16 ≤ a₁ ≤ 2`, `k ≥ 1`
(`compWeight_mem_Icc`). -/
theorem covBLog_compWeight_le_covBLogMax_of_range (d : ℕ) (κ : ℝ) (hL : 3 ≤ L) {a₁ : ℝ}
    (h1 : 9 / 16 ≤ a₁) (h2 : a₁ ≤ 2) {k : ℕ} (hk : 1 ≤ k) :
    covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ ≤ covBLogMax d L κ :=
  covBLog_le_covBLogMax d L κ (compWeight_mem_Icc hL h1 h2 hk) (by linarith) h2

end Scale

section ScaleStep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

/-- **The constant of the determinant terms is not small**: under `FlCore` and the rate condition
it is at least `½ N`, whatever the coupling `β` of the step. -/
theorem half_le_detConst
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    (1 / 2 : ℝ) * N ≤ (L : ℝ) ^ d * ((1 / 2 : ℝ) * N *
      covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLd : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
  have hw := hC.Sp.weights k S.hk1 (Nat.le_succ k)
  have h1 := one_le_covBLog d hL hw.1 (S.a₁ / (L : ℝ) ^ 2) hC.hκ.le
  have hz0 : 0 ≤ ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) := by positivity
  have hden : 0 < 1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) := by linarith
  have hN0 : (0 : ℝ) ≤ (1 / 2 : ℝ) * N := by positivity
  have h2 : (1 / 2 : ℝ) * N ≤ (1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) := by
    rw [le_div_iff₀ hden]
    nlinarith
  nlinarith

/-- **The localized determinant family with the scale-uniform constant.**  Under the hypotheses
of `exists_detExpansionLocC_of_chart` the record `DetExpansionLocC` has an element with the same
terms and rate and with the constant `L^d · ½ N covBLogMax d L κ / (1 - (detDeg d L + 1)² 2/e^κ)`,
which involves neither the scale `k`, nor the torus, nor `z`, nor the datum. -/
theorem exists_detExpansionLocC_of_chart_uniform
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ E : DetExpansionLocC S m₀ z eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
      ∀ D T, E.term D T =
        ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) D y T := by
  classical
  obtain ⟨E, hE⟩ := exists_detExpansionLocC_of_chart (m₀ := m₀) S hC hδc hMX hdm hα hsm hconn hN
    hz z
  have hmax := covBLog_compWeight_le_covBLogMax hC S.hk1
  have hden : 0 < 1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) := by linarith
  have h0 : 0 ≤ (L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) :=
    le_trans (by positivity) (half_le_detConst S hC hz)
  refine ⟨E.weaken h0 ?_ le_rfl, fun D T => hE D T⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine div_le_div_of_nonneg_right ?_ hden.le
  exact mul_le_mul_of_nonneg_left hmax (by positivity)

end ScaleStep

/-! ### The field dependence -/

section Oscillation

/-- **Schwarz lemma along a complex line.**  Let `A` be analytic at every point of a set `U` and
bounded by `M` on `U`.  If the disc `p + t (q - p)`, `|t| < R`, with `R > 1`, lies in `U`, then
`‖A q - A p‖ ≤ 2 M / R`. -/
theorem norm_sub_le_of_analyticAt_disc {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {A : V → ℂ} {U : Set V} {M R : ℝ} (hR : 1 < R) (hA : ∀ v ∈ U, AnalyticAt ℂ A v)
    (hM : ∀ v ∈ U, ‖A v‖ ≤ M) {p q : V} (hdisc : ∀ t : ℂ, ‖t‖ < R → p + t • (q - p) ∈ U) :
    ‖A q - A p‖ ≤ 2 * M / R := by
  have hline : ∀ t : ℂ, AnalyticAt ℂ (fun t : ℂ => p + t • (q - p)) t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hd : DifferentiableOn ℂ (fun t : ℂ => A (p + t • (q - p))) (Metric.ball 0 R) := by
    intro t ht
    have h1 := hA _ (hdisc t (by simpa using ht))
    exact (AnalyticAt.comp (g := A) (f := fun t : ℂ => p + t • (q - p)) h1
      (hline t)).differentiableAt.differentiableWithinAt
  have hb : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖A (p + t • (q - p))‖ ≤ M := fun t ht =>
    hM _ (hdisc t (by simpa using ht))
  have h := norm_oneDiff_le hR hd hb
  simpa using h

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ}

/-- A datum whose raw datum lies in the chart is a datum of the chart. -/
theorem xiCData_of_rawOf_mem {D : BgData G N} (h : rawOf D ∈ XiCRaw G a ν n σ ε) :
    XiCData G a ν n σ ε D := by
  obtain ⟨D', hD', he⟩ := h
  rw [BgData.eq_of_raw he]
  exact hD'

/-- **The chart contains a disc around each of its points, along every line of data.**  For a
datum `D` of the chart there is `r₀ > 0` such that for every datum `D₂` and every complex `t`
with `|t| ‖rawOf D₂ - rawOf D‖ < r₀` the point `rawOf D + t (rawOf D₂ - rawOf D)` is a raw datum
of the chart.  (The chart is open in the subspace `rawSub` of raw data of data,
`xiCRaw_eventually`; the norm is the supremum norm of the raw data `(Ψ, h̃)`.) -/
theorem exists_chart_disc (H : BgHyp d L K ϱ a ν) {D : BgData G N}
    (hD : XiCData G a ν n σ ε D) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (D₂ : BgData G N) (t : ℂ), ‖t‖ * ‖rawOf D₂ - rawOf D‖ < r₀ →
      rawOf D + t • (rawOf D₂ - rawOf D) ∈ XiCRaw G a ν n σ ε := by
  have hev := xiCRaw_eventually H hD
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨r₀, hr₀, hsub⟩ := hev
  refine ⟨r₀, hr₀, fun D₂ t ht => hsub ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  · exact (rawSub N G).add_mem (rawOf_mem_rawSub D)
      ((rawSub N G).smul_mem t ((rawSub N G).sub_mem (rawOf_mem_rawSub D₂) (rawOf_mem_rawSub D)))

/-- **Lipschitz bound from a disc of the chart.**  Let `F` be a function of the datum which is,
on the chart, the value at the raw datum of a function analytic at the raw data of the chart, and
is bounded by `M` on the chart.  If `r₀ > 0` is a radius of `exists_chart_disc` at `D`, then every
datum `D₂` with `‖rawOf D₂ - rawOf D‖ < r₀` is a datum of the chart and
`‖F D₂ - F D‖ ≤ 2 M ‖rawOf D₂ - rawOf D‖ / r₀`. -/
theorem norm_sub_le_of_chart_disc {F : BgData G N → ℂ}
    {A : RawData d L (N₁ * L ^ m₁) K N → ℂ} {M r₀ : ℝ}
    (hA : ∀ D : BgData G N, XiCData G a ν n σ ε D → AnalyticAt ℂ A (rawOf D))
    (hAv : ∀ D : BgData G N, XiCData G a ν n σ ε D → A (rawOf D) = F D)
    (hM : ∀ D : BgData G N, XiCData G a ν n σ ε D → ‖F D‖ ≤ M) {D : BgData G N}
    (hr₀ : ∀ (D₂ : BgData G N) (t : ℂ), ‖t‖ * ‖rawOf D₂ - rawOf D‖ < r₀ →
      rawOf D + t • (rawOf D₂ - rawOf D) ∈ XiCRaw G a ν n σ ε)
    {D₂ : BgData G N} (h : ‖rawOf D₂ - rawOf D‖ < r₀) :
    XiCData G a ν n σ ε D₂ ∧ ‖F D₂ - F D‖ ≤ 2 * M / r₀ * ‖rawOf D₂ - rawOf D‖ := by
  have hr₀pos : 0 < r₀ := lt_of_le_of_lt (norm_nonneg _) h
  have hX : XiCData G a ν n σ ε D := by
    have h0 := hr₀ D₂ 0 (by simpa using hr₀pos)
    rw [zero_smul, add_zero] at h0
    exact xiCData_of_rawOf_mem h0
  have hX₂ : XiCData G a ν n σ ε D₂ := by
    have h1 := hr₀ D₂ 1 (by simpa using h)
    rw [one_smul, add_sub_cancel] at h1
    exact xiCData_of_rawOf_mem h1
  refine ⟨hX₂, ?_⟩
  rcases eq_or_lt_of_le (norm_nonneg (rawOf D₂ - rawOf D)) with h0 | h0
  · have e : rawOf D₂ = rawOf D := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    rw [BgData.eq_of_raw e]
    simp
  · have hR : 1 < r₀ / ‖rawOf D₂ - rawOf D‖ := (one_lt_div h0).2 h
    have hAU : ∀ v ∈ XiCRaw G a ν n σ ε, AnalyticAt ℂ A v := by
      rintro v ⟨D', hD', rfl⟩
      exact hA D' hD'
    have hMU : ∀ v ∈ XiCRaw G a ν n σ ε, ‖A v‖ ≤ M := by
      rintro v ⟨D', hD', rfl⟩
      rw [hAv D' hD']
      exact hM D' hD'
    have hmain := norm_sub_le_of_analyticAt_disc hR hAU hMU (p := rawOf D) (q := rawOf D₂)
      (fun t ht => hr₀ D₂ t (by rwa [lt_div_iff₀ h0] at ht))
    rw [hAv D hX, hAv D₂ hX₂] at hmain
    calc ‖F D₂ - F D‖ ≤ 2 * M / (r₀ / ‖rawOf D₂ - rawOf D‖) := hmain
      _ = 2 * M / r₀ * ‖rawOf D₂ - rawOf D‖ := by
        field_simp

end Oscillation

/-! ### The field dependence of the activities -/

section ActivityOscillation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hconn : HatConn Gp)

include hC hk hδc hcap hsm hmar hα hconn

open Classical in
/-- **Oscillation of an activity along a complex line inside the chart.**  If the disc
`rawOf D + t (rawOf D₂ - rawOf D)`, `|t| < R`, `R > 1`, lies in the chart, then the activities of
the two data differ by at most `2 / R` times the bound of `norm_detActivityBg_le`. -/
theorem norm_detActivityBg_sub_le_of_disc (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) {D D₂ : BgData Gp N} {R : ℝ} (hR : 1 < R)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → rawOf D + t • (rawOf D₂ - rawOf D) ∈
      XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) :
    ‖detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D₂ y Y -
        detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y‖ ≤
      2 * ((1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
        Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
          (2 * d * L)) * dExt Y)) / R := by
  obtain ⟨A, hA, hAv⟩ := exists_analytic_detActivityBg_raw (m₀ := m₀) hC hk hδc hcap hsm hmar hα
    y Y
  have hAU : ∀ v ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps, AnalyticAt ℂ A v := by
    rintro v ⟨D', hD', rfl⟩
    exact hA D' hD'
  have hMU : ∀ v ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps, ‖A v‖ ≤
      (1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
        Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
          (2 * d * L)) * dExt Y) := by
    rintro v ⟨D', hD', rfl⟩
    rw [hAv D' hD']
    exact norm_detActivityBg_le hC hk hδc hcap hsm hmar hα hconn hD' hN y hz Y
  have hX : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D := by
    have h0 := hdisc 0 (by simpa using lt_trans zero_lt_one hR)
    rw [zero_smul, add_zero] at h0
    exact xiCData_of_rawOf_mem h0
  have hX₂ : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D₂ := by
    have h1 := hdisc 1 (by simpa using hR)
    rw [one_smul, add_sub_cancel] at h1
    exact xiCData_of_rawOf_mem h1
  have hmain := norm_sub_le_of_analyticAt_disc hR hAU hMU hdisc
  rwa [hAv D hX, hAv D₂ hX₂] at hmain

open Classical in
/-- **The field dependence of an activity is small near each datum of the chart.**  For a datum
`D` of the chart there is `r₀ > 0` (depending on `D`) such that every datum `D₂` with
`‖rawOf D₂ - rawOf D‖ < r₀` is a datum of the chart and, for every unit block `y` and polymer `Y`,
the activities differ by at most `2 ‖rawOf D₂ - rawOf D‖ / r₀` times the bound of
`norm_detActivityBg_le`. -/
theorem exists_norm_detActivityBg_sub_le (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ D₂ : BgData Gp N, ‖rawOf D₂ - rawOf D‖ < r₀ →
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D₂ ∧
      ∀ (y : unitPts Gp) (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ)),
        ‖detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D₂ y Y -
            detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y‖ ≤
          2 * ((1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
            Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt Y)) / r₀ * ‖rawOf D₂ - rawOf D‖ := by
  obtain ⟨r₀, hr₀, hdisc⟩ := exists_chart_disc hC.HBp hD
  refine ⟨r₀, hr₀, fun D₂ h => ⟨?_, fun y Y => ?_⟩⟩
  · have h1 := hdisc D₂ 1 (by simpa using h)
    rw [one_smul, add_sub_cancel] at h1
    exact xiCData_of_rawOf_mem h1
  · obtain ⟨A, hA, hAv⟩ := exists_analytic_detActivityBg_raw (m₀ := m₀) hC hk hδc hcap hsm hmar
      hα y Y
    exact (norm_sub_le_of_chart_disc hA hAv
      (fun D' hD' => norm_detActivityBg_le hC hk hδc hcap hsm hmar hα hconn hD' hN y hz Y)
      hdisc h).2

end ActivityOscillation

/-! ### The field dependence of the terms of the record -/

section RecordOscillation

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

/-- **Oscillation of a term along a complex line inside the chart.**  If the disc
`rawOf D + t (rawOf D₂ - rawOf D)`, `|t| < R`, `R > 1`, lies in the chart, then
`‖term D₂ T - term D T‖ ≤ 2 c_det e^{-κ'' d(T)} / R`. -/
theorem DetExpansionLocC.norm_term_sub_le_of_disc (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {D D₂ : BgData S.G' N} {R : ℝ} (hR : 1 < R)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → rawOf D + t • (rawOf D₂ - rawOf D) ∈
      XiCRaw S.G' S.a S.ν (k + 1) 1 eps)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ‖E.term D₂ T - E.term D T‖ ≤ 2 * (cdet * Real.exp (-κ'' * dExt T)) / R := by
  obtain ⟨A, hA, hAv⟩ := E.analyticAt_raw T
  have hAU : ∀ v ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps, AnalyticAt ℂ A v := by
    rintro v ⟨D', hD', rfl⟩
    exact hA D' hD'
  have hMU : ∀ v ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps, ‖A v‖ ≤
      cdet * Real.exp (-κ'' * dExt T) := by
    rintro v ⟨D', hD', rfl⟩
    rw [hAv D' hD']
    exact E.bound D' hD' T
  have hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D := by
    have h0 := hdisc 0 (by simpa using lt_trans zero_lt_one hR)
    rw [zero_smul, add_zero] at h0
    exact xiCData_of_rawOf_mem h0
  have hX₂ : XiCData S.G' S.a S.ν (k + 1) 1 eps D₂ := by
    have h1 := hdisc 1 (by simpa using hR)
    rw [one_smul, add_sub_cancel] at h1
    exact xiCData_of_rawOf_mem h1
  have hmain := norm_sub_le_of_analyticAt_disc hR hAU hMU hdisc
  rwa [hAv D hX, hAv D₂ hX₂] at hmain

/-- **The field dependence of the terms is small near each datum of the chart.**  For a datum `D`
of the chart there is `r₀ > 0` (depending on `D` only) such that every datum `D₂` with
`‖rawOf D₂ - rawOf D‖ < r₀` is a datum of the chart and, for every `T`,
`‖term D₂ T - term D T‖ ≤ 2 c_det e^{-κ'' d(T)} ‖rawOf D₂ - rawOf D‖ / r₀`. -/
theorem DetExpansionLocC.exists_norm_term_sub_le (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (H : BgHyp d L (k + 1) ϱ S.a S.ν) {D : BgData S.G' N}
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ D₂ : BgData S.G' N, ‖rawOf D₂ - rawOf D‖ < r₀ →
      XiCData S.G' S.a S.ν (k + 1) 1 eps D₂ ∧
      ∀ T, ‖E.term D₂ T - E.term D T‖ ≤
        2 * (cdet * Real.exp (-κ'' * dExt T)) / r₀ * ‖rawOf D₂ - rawOf D‖ := by
  obtain ⟨r₀, hr₀, hdisc⟩ := exists_chart_disc H hD
  refine ⟨r₀, hr₀, fun D₂ h => ⟨?_, fun T => ?_⟩⟩
  · have h1 := hdisc D₂ 1 (by simpa using h)
    rw [one_smul, add_sub_cancel] at h1
    exact xiCData_of_rawOf_mem h1
  · obtain ⟨A, hA, hAv⟩ := E.analyticAt_raw T
    exact (norm_sub_le_of_chart_disc hA hAv (fun D' hD' => E.bound D' hD' T) hdisc h).2

end RecordOscillation

end Balaban.Fluctuation
