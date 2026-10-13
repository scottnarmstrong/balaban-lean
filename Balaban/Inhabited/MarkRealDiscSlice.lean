/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScaleLemmas
public import Balaban.Inhabited.MarkRealDiscSliceG
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Fluctuation.MarkedCubicJoint
public import Balaban.Fluctuation.MarkedTangent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# MARK-REAL, the marked disc uniformly on the constant-`h₀` slice (leaf 2)

At a scale of the shared tower `T` (`StepScaleData`), with `R₁ = R_σ = 17/16`, `t₁ = 1/16` and
`r = lvR/4`:

* `marked_radius_arith`: `(R₁ + r)(R_σ + t₁) ≤ 4 + lvR` for `lvR > 0`.
* `markedRad_mono`: `markedRad` is monotone in its `c_ψ` argument.
* `StepScaleData.marked_radius_lt`: `(R₁ + r)(R_σ + t₁) · markedRad(p₁) < T.t`.
* `markReal_disc_slice`: the premise `hdisc` of
  `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, for every datum of the slice and every
  `‖x‖ ≤ p₁`, with the coordinate bound of `exists_analytic_shiftUC_chart` (uniform in the datum).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set

/-- `markedRad` is monotone in the hat radius `c_ψ`. -/
theorem markedRad_mono (d L N k : ℕ) (a₁ κ : ℝ) (cc : ℂ) (h : 0 ≤ covSupConstC d L N
    (compWeight L a₁ k) κ) {c c' : ℝ} (hc : c ≤ c') :
    markedRad d L N k a₁ κ c cc ≤ markedRad d L N k a₁ κ c' cc := by
  unfold markedRad
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hc h) (norm_nonneg _)) (Real.sqrt_nonneg _)

namespace StepScaleData

variable {κmin : ℝ} {T : StepTower κmin} {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
  {ν β p₁ : ℝ}

/-- **The radius inequality of `markedDisc_field_mem_flBall`** at the scale, with
`R₁ = R_σ = 17/16`, `t₁ = 1/16`, `r = lvR/4`, `Y₀ = markedRad(p₁)`, `δ₁ = T.t`. -/
theorem marked_radius_lt (D : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    (17 / 16 + lvR T.κ T.t (β * 3 ^ k) p₁ / 4) * (17 / 16 + 1 / 16) *
      markedRad 3 3 2 k 1 T.κ p₁
        ((((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < T.t := by
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := (T.scaleDataG_of_fixed D).marked_radius_lt hp
  rw [StepTower.toG_step_betaU] at h
  rw [hb, lvRG_three] at h
  exact h

end StepScaleData

/-- **The marked disc on the constant-`h₀` slice** (`hdisc` of
`hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, verbatim, for the step with datum `D`):
for every datum `D` of the slice with `XiCData`, every hat field `‖x‖ ≤ p₁`, every `‖u‖ < 17/16`,
`|t| < 1/16`, `|σ| < 17/16 + lvR/4`, the field `σ (lift(u · shiftUC x) + t · lift(M_z shiftUC x))`
lies in `FlBall (stepG …) T.t`.  The coordinate bound is the chart-wide bound of
`exists_analytic_shiftUC_chart` at the base step, transported to `rawOf D`; it is uniform in `D`. -/
theorem markReal_disc_slice {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hp₁ : 0 < p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (hx : ‖x‖ ≤ p₁)
    (z : Torus 3 (N₁ * 3 ^ T.m₁ * 3 ^ (k + 1 - (k + 1)))) {u : ℂ} (hu : ‖u‖ < 17 / 16) :
    ∀ t : ℂ, ‖t‖ < 1 / 16 → ∀ σ : ℂ, ‖σ‖ < 17 / 16 + lvR T.κ T.t (β * 3 ^ k) p₁ / 4 →
      σ • (liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG' (u • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) +
        t • liftC ((T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
          (((T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
            (((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))) ∈
        FlBall (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.t := by
  intro t ht σ hσ
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := markReal_disc_sliceG T.toG (T.scaleDataG_of_fixed hS) hp₁ (ϱ := rhoSep T.m₁)
    (rhoSepG_three _).symm (S₀ := T.step k hk N₁ ν β p₁) rfl D hDh hD hx z hu t ht σ
    (by rw [hb, lvRG_three]; exact hσ)
  exact h

/-- **Non-vacuity of `markReal_disc_slice`**: at `k = 1`, `N₁ = 6`, `ν = 0`, `p₁ = 1`, `β = βray`
the package is inhabited and the step's own datum satisfies the conclusion at `x = 0`, `u = 0`. -/
theorem markReal_disc_slice_nonempty {κmin : ℝ} (T : StepTower κmin) :
    ∃ βray : ℝ, 2 ≤ βray ∧ Nonempty (StepScaleData T 1 le_rfl 6 0 βray 1) ∧
      ∀ z : Torus 3 (6 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))), ∀ t : ℂ, ‖t‖ < 1 / 16 →
        ∀ σ : ℂ, ‖σ‖ < 17 / 16 + lvR T.κ T.t (βray * 3 ^ 1) 1 / 4 →
        σ • (liftC (T.step 1 le_rfl 6 0 βray 1).hG'
            ((0 : ℂ) • (T.step 1 le_rfl 6 0 βray 1).shiftUC 0) +
          t • liftC (T.step 1 le_rfl 6 0 βray 1).hG'
            ((T.step 1 le_rfl 6 0 βray 1).maskUC z ((T.step 1 le_rfl 6 0 βray 1).shiftUC 0))) ∈
          FlBall (stepG 3 3 6 T.m₁ 1 (rhoSep T.m₁)) T.t := by
  obtain ⟨βray, h2, ⟨hS⟩⟩ := T.scale_instance
  exact ⟨βray, h2, ⟨hS⟩, fun z t ht σ hσ =>
    markReal_disc_slice T hS one_pos (T.step 1 le_rfl 6 0 βray 1).D'
      (T.step 1 le_rfl 6 0 βray 1).hh₀ hS.xi (x := 0) (by simp) z (u := 0) (by norm_num) t ht σ hσ⟩

end Balaban.Inhabited
