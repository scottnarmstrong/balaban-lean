/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepScaleDataG
public import Balaban.Inhabited.MarkBudgetAuditG
public import Balaban.Fluctuation.MarkedCubicJoint
public import Balaban.Fluctuation.MarkedTangent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# MARK-REAL, the marked disc uniformly on the constant-`h₀` slice, at the general tower

General versions of `StepScaleData.marked_radius_lt` and `markReal_disc_slice`: at a scale of the
tower `T : StepTowerG d L N κmin` (`StepScaleDataG`), with `R₁ = R_σ = 17/16`, `t₁ = 1/16` and
`r = lvRG/4`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.Inhabited.MarkBudgetAudit
  Balaban.SmallField Set

/-- The radius arithmetic: for `R > 0`, `(17/16 + R/4)(17/16 + 1/16) ≤ 4 + R`. -/
theorem marked_radius_arith {R : ℝ} (hR : 0 < R) :
    (17 / 16 + R / 4) * (17 / 16 + 1 / 16) ≤ 4 + R := by nlinarith

namespace StepScaleDataG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} {T : StepTowerG d L N κmin} {k : ℕ} {hk : 1 ≤ k}
  {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- **The radius inequality of `markedDisc_field_mem_flBall`** at the scale of the general tower,
with `R₁ = R_σ = 17/16`, `t₁ = 1/16`, `r = lvRG/4`, `Y₀ = markedRad(p₁)`, `δ₁ = T.t`. -/
theorem marked_radius_lt (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    (17 / 16 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) * (17 / 16 + 1 / 16) *
      markedRad d L N k 1 T.κ p₁
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hmem := compWeightG_mem T hk
  have hCs : 0 ≤ covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ :=
    covSupConstC_nonneg (by have := T.hd; omega) T.hL (by linarith [hmem.1]) T.κ
  have hr := D.r_pos
  have ha := marked_radius_arith hr
  have hm := D.ray_margin
  have hW : 0 ≤ Real.sqrt (N : ℝ) *
      (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) hCs)
  have hfl := D.fl_radius
  have e : ∀ c : ℝ, markedRad d L N k 1 T.κ c
      ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      (Real.sqrt (N : ℝ) *
      (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ)) * c := fun c => by
    simp only [markedRad]; ring
  rw [e]
  have hfl' : (Real.sqrt (N : ℝ) *
      (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
        covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ)) *
      lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) < T.t := by
    have e2 : ∀ a b c d : ℝ, a * (b * (c * d)) = a * (b * c) * d := fun a b c d => by ring
    rwa [e2] at hfl
  have h1 : (17 / 16 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4) *
      (17 / 16 + 1 / 16) * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
    nlinarith
  calc _ = _ * p₁ * _ := by ring
    _ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) * _ :=
        mul_le_mul_of_nonneg_right h1.le hW
    _ < _ := by rw [mul_comm]; exact hfl'

end StepScaleDataG

/-- **The marked disc on the constant-`h₀` slice, at the general tower** (`hdisc` of
`hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, for the step with datum `D`): for every datum
`D` of the slice with `XiCData`, every hat field `‖x‖ ≤ p₁`, every `‖u‖ < 17/16`, `|t| < 1/16`,
`|σ| < 17/16 + lvRG/4`, the field `σ (lift(u · shiftUC x) + t · lift(M_z shiftUC x))` lies in
`FlBall (stepG …) T.t`.  The step is stated over any `ϱ = rhoSepG d L T.m₁`. -/
theorem markReal_disc_sliceG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleDataG T k hk N₁ ν β p₁) (hp₁ : 0 < p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁)
    {S₀ : StepSetting d L N₁ T.m₁ k N ϱ}
    (hS₀ : S₀ = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
    (D : BgData S₀.G' N)
    (hDh : ∀ y i, D.h y i = (S₀.h₀ i : ℂ))
    (hD : XiCData S₀.G' (compWeight L 1) ν (k + 1) 1 T.t D)
    {x : (S₀.withDatum D hDh).E} (hx : ‖x‖ ≤ p₁)
    (z : Torus d (N₁ * L ^ T.m₁ * L ^ (k + 1 - (k + 1)))) {u : ℂ} (hu : ‖u‖ < 17 / 16) :
    ∀ t : ℂ, ‖t‖ < 1 / 16 →
      ∀ σ : ℂ, ‖σ‖ < 17 / 16 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ / 4 →
      σ • (liftC (S₀.withDatum D hDh).hG' (u • (S₀.withDatum D hDh).shiftUC x) +
        t • liftC (S₀.withDatum D hDh).hG'
          ((S₀.withDatum D hDh).maskUC z ((S₀.withDatum D hDh).shiftUC x))) ∈
        FlBall (stepG d L N₁ T.m₁ k ϱ) T.t := by
  intro t ht σ hσ
  subst hϱ
  subst hS₀
  obtain ⟨Q, -, hQ, hQb⟩ := (T.step k hk N₁ ν β p₁).exists_analytic_shiftUC_chart
    (δc := T.δc) hS.core T.large_block T.dom_margin T.coer_margin T.δc_small x
    (cψ := p₁) hp₁.le (fun p => (T.step k hk N₁ ν β p₁).yhat_le_of_norm_le hx p)
  have hY := hQb (rawOf D) ⟨D, hD, rfl⟩
  rw [hQ D hDh hD] at hY
  exact ((T.step k hk N₁ ν β p₁).withDatum D hDh).markedDisc_field_mem_flBall z
    (isLevel_lvLowG hk) hY (hS.marked_radius_lt hp₁) hu ht hσ

end Balaban.Inhabited
