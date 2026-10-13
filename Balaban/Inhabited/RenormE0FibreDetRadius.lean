/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormE0FibreDet
public import Balaban.Inhabited.StepTowerRadius
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant part of the new energy function at a renormalization radius `e <= t`

The statement `StepTowerTheta.detGrouped_ambient` with the renormalization radius `t` replaced by
any `e` with `0 < e <= t`.  (`renE0_fibre_det_at` and `expE0_det_scale_of_tower_at` are in
`RenormE0FibreDet`, as corollaries of the general tower.)  The step determinant records stay at chart radius `2 t`;
the renormalized datum lies in the chart at radius `e + xi_2 (3/2) e r_0 <= 2 e <= 2 t`
(`StepTowerTheta.thetaChartMargin_of_le`).

## What is not asserted

This is the determinant summand `renE0θ_det` only; it is NOT the physical `expE0` field of the
renormalization input record (the marked energy terms are missing).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep LocalCover

section TowerFamily

/-- **Ambient analytic determinant terms at renormalization radius `e <= t`.**  As
`StepTowerTheta.detGrouped_ambient` with `R.t` replaced by `e` in the datum and the domain; the
records stay at chart radius `2 t`.  Determinant part only, not the physical `expE0`. -/
theorem StepTowerTheta.detGrouped_ambient_at {κmin : ℝ} (R : StepTowerTheta κmin)
    {e : ℝ} (he : 0 < e) (het : e ≤ R.t)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁) (hN : 5 < N₁) {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z,
          detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 R.BG R.κ) D y T') ∧
      (∀ z, renE0θ_det e E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
          -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
            (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))))
        (X : Set (CTorus 3 3 N₁ R.m₁ (k + 1))),
        ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) → ℂ,
          AnalyticOnNhd ℂ F (expDom (R.toStepTower.step k hk N₁ ν β p₁).G'
            (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν e)
            R.r₀) ∧
          ∀ (D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2),
            XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν e D →
            (∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
              F ((D.Ψ, D.h), ξ) =
                (E z).detGrouped (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) e D ξ) X ∧
              ‖F ((D.Ψ, D.h), ξ)‖ ≤ hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
                Real.exp (-hullRate 3 3 (towerDetRate R.κ) * sizeJ 1 (k + 1) X)) ∧
            F ((D.Ψ, D.h), 0) = (E z).detGrouped D X := by
  have h := R.toG.detGrouped_ambient_at he het k hk N₁ h3N hN hν0 (by simpa using hν) β p₁
  unfold StepTowerG.step at h
  rw [rhoSepG_three] at h
  dsimp only [StepTowerTheta.toG_m₁, StepTowerTheta.toG_κ, StepTowerTheta.toG_t,
    StepTowerTheta.toG_BG, StepTowerTheta.toG_r₀] at h
  have e1 : (R.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 + 1 : ℕ) : ℝ)) /
      (2 * ((3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = towerDetRate R.κ := by
    unfold towerDetRate; norm_num
  have e2 : ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * (2 : ℕ) * covBLogMax 3 3 R.κ /
      (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) = towerDetConst R.κ :=
    StepTower.det_const_eq _ _
  rw [e1, e2] at h
  exact h

end TowerFamily

end Balaban.Inhabited
