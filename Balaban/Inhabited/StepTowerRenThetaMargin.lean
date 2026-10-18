/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormThetaChart
public import Balaban.Localization.DecoupledBackground
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The chart inclusion of the renormalized datum at the radius `(1 + c r₀) ε`

The renormalized datum `θ_ξ = (1 + ε ξ₀) Ψ` of a class-chart datum at radius `ε` lies in the step
chart at the radius `(1 + c r₀) ε`, `c = (3/2) ξ₂` (`xiK2`), for `‖ξ‖ < r₀ ≤ 1`, as soon as `ε`
satisfies six explicit inequalities (`ThetaSmall`, stated inline below).  The strict inequalities
of the chart are those of `xiCData_perturb`; only the clause `c₀` is strict in the hypotheses.

* `thetaChartMargin_of_small`: the margin `ThetaChartMargin` from the smallness of `ε`;
* `exists_theta_small`: the smallness holds for every `0 < ε ≤ ε*`, one `ε*` for all `r₀ ≤ 1`;
* `renThetaDatum_xiCData_scaled`: the chart inclusion at radius `(1 + c r₀) ε`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization

/-- **The margin from the smallness of the class radius.**  For `0 < r₀ ≤ 1` and `0 < ε` with
`(3/2) ε ≤ 1`, the smallness of the class radius and the four inequalities below, the margin
`ThetaChartMargin d L N ε ((1 + (3/2) ξ₂ r₀) ε) r₀` holds. -/
theorem thetaChartMargin_of_small {d L N : ℕ} [NeZero L] {ε r₀ : ℝ} (hε : 0 < ε) (hr : 0 < r₀)
    (hr1 : r₀ ≤ 1) (h1 : (3 / 2 : ℝ) * ε ≤ 1)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hdata : (xiC1 d + 15 / 2) * ε ≤ bgC1 d L N)
    (hstar : (3 / 2 : ℝ) * ε ≤ deltaStar d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N)
    (hc0 : bgK1 d L N * (xiC1 d * ε) + cK2 d L N * ((3 / 2 : ℝ) * ε) < bgC0 d L N) :
    ThetaChartMargin d L N ε ((1 + xiK2 d L N * ((3 / 2 : ℝ) * r₀)) * ε) r₀ := by
  have hδ : (3 / 2 : ℝ) * ε * r₀ ≤ (3 / 2 : ℝ) * ε := by nlinarith
  have hδ0 : 0 ≤ (3 / 2 : ℝ) * ε * r₀ := by positivity
  have hck : 0 < cK2 d L N := cK2_pos d L N
  refine ⟨hε, hr, hδ0, hδ.trans h1, hsm, ?_, hδ.trans hstar, hK, ?_, by ring⟩
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hδ hck.le]

/-- **The smallness is attained.**  For `0 < d` there is `ε* > 0` such that every `0 < ε ≤ ε*`
satisfies the six inequalities of `thetaChartMargin_of_small`. -/
theorem exists_theta_small (d L N : ℕ) [NeZero L] (hd : 0 < d) :
    ∃ εs : ℝ, 0 < εs ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εs →
      (3 / 2 : ℝ) * ε ≤ 1 ∧ (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1 ∧
      (xiC1 d + 15 / 2) * ε ≤ bgC1 d L N ∧ (3 / 2 : ℝ) * ε ≤ deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N ∧
      bgK1 d L N * (xiC1 d * ε) + cK2 d L N * ((3 / 2 : ℝ) * ε) < bgC0 d L N := by
  have hx : 1 ≤ xiC1 d := one_le_xiC1 d
  have hk : 0 < bgK1 d L N := bgK1_pos d L N
  have hck : 0 < cK2 d L N := cK2_pos d L N
  have hC1 : 0 < bgC1 d L N := bgC1_pos' hd
  have hC0 : 0 < bgC0 d L N := bgC0_pos d L N hd
  have hds : 0 < deltaStar d L N := deltaStar_pos d L N hd
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd
  set a : ℝ := bgK1 d L N * xiC1 d + cK2 d L N * (3 / 2) with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  set m : ℝ := (4 * d + 6) * (2 * d + 1) with hm
  have hm0 : 0 < m := by rw [hm]; positivity
  refine ⟨min (min (min (2 / 3) (1 / m)) (min (bgC1 d L N / (xiC1 d + 15 / 2))
    (deltaStar d L N / (3 / 2)))) (min (deltaStar d L N / (bgK1 d L N * xiC1 d))
      (bgC0 d L N / (2 * a))), ?_, fun ε hε hle => ?_⟩
  · refine lt_min (lt_min (lt_min (by norm_num) (by positivity)) (lt_min ?_ ?_)) (lt_min ?_ ?_)
    · exact div_pos hC1 (by positivity)
    · exact div_pos hds (by norm_num)
    · exact div_pos hds (by positivity)
    · exact div_pos hC0 (by positivity)
  · have e1 : ε ≤ 2 / 3 := hle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (((min_le_left _ _)))))
    have e2 : ε ≤ 1 / m := hle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_right _ _)))
    have e3 : ε ≤ bgC1 d L N / (xiC1 d + 15 / 2) := hle.trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have e4 : ε ≤ deltaStar d L N / (3 / 2) := hle.trans ((min_le_left _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
    have e5 : ε ≤ deltaStar d L N / (bgK1 d L N * xiC1 d) := hle.trans ((min_le_right _ _).trans
      (min_le_left _ _))
    have e6 : ε ≤ bgC0 d L N / (2 * a) := hle.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at e3 e5
    rw [le_div_iff₀ (by positivity)] at e4
    rw [le_div_iff₀ (by positivity)] at e6
    rw [le_div_iff₀ hm0] at e2
    refine ⟨by linarith, ?_, by linarith, by linarith, by nlinarith, ?_⟩
    · have : (4 * d + 6 : ℝ) * ((2 * d + 1) * ε) = m * ε := by rw [hm]; ring
      rw [this]; linarith
    · have : bgK1 d L N * (xiC1 d * ε) + cK2 d L N * ((3 / 2 : ℝ) * ε) = a * ε := by
        rw [ha]; ring
      rw [this]; nlinarith

/-- **The chart inclusion at the radius `(1 + c r₀) ε`.**  For `D` in the class chart
`XiCOneReal` at radius `ε` and `‖ξ‖ < r₀ ≤ 1`, `renThetaDatum S ε D ξ` lies in the step chart
`XiCData` at level `k + 1` and radius `(1 + (3/2) ξ₂ r₀) ε`, provided `ε` satisfies the
inequalities of `thetaChartMargin_of_small`. -/
theorem renThetaDatum_xiCData_scaled {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (H : BgHyp d L (k + 1) ϱ S.a S.ν) {ε r₀ : ℝ}
    (hε : 0 < ε) (hr : 0 < r₀) (hr1 : r₀ ≤ 1) (h1 : (3 / 2 : ℝ) * ε ≤ 1)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hdata : (xiC1 d + 15 / 2) * ε ≤ bgC1 d L N)
    (hstar : (3 / 2 : ℝ) * ε ≤ deltaStar d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N)
    (hc0 : bgK1 d L N * (xiC1 d * ε) + cK2 d L N * ((3 / 2 : ℝ) * ε) < bgC0 d L N)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν ε D) (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k + 1) 1 ((1 + xiK2 d L N * ((3 / 2 : ℝ) * r₀)) * ε)
      (renThetaDatum S ε D ξ) :=
  renE0_theta_domain S H ε _ r₀ (thetaChartMargin_of_small hε hr hr1 h1 hsm hdata hstar hK hc0)
    D hD ξ hξ

/-- The same inclusion at a step radius `t = λ ε` with `λ = 1 + (3/2) ξ₂ r₀`, the form of the
radius of the towers of `StepTowerRenThetaClass`. -/
theorem renThetaDatum_xiCData_tower {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (H : BgHyp d L (k + 1) ϱ S.a S.ν) {ε r₀ t lam : ℝ}
    (hε : 0 < ε) (hr : 0 < r₀) (hr1 : r₀ ≤ 1) (h1 : (3 / 2 : ℝ) * ε ≤ 1)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hdata : (xiC1 d + 15 / 2) * ε ≤ bgC1 d L N)
    (hstar : (3 / 2 : ℝ) * ε ≤ deltaStar d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) ≤ deltaStar d L N)
    (hc0 : bgK1 d L N * (xiC1 d * ε) + cK2 d L N * ((3 / 2 : ℝ) * ε) < bgC0 d L N)
    (hlam : lam = 1 + xiK2 d L N * ((3 / 2 : ℝ) * r₀)) (ht : t = lam * ε)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν ε D) (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k + 1) 1 t (renThetaDatum S ε D ξ) := by
  subst hlam ht
  exact renThetaDatum_xiCData_scaled S H hε hr hr1 h1 hsm hdata hstar hK hc0 D hD ξ hξ

end Balaban.Inhabited
