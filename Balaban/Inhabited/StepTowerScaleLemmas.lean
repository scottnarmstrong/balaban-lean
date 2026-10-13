/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScale
public import Balaban.Inhabited.StepScaleDataGBridge
public import Balaban.Fluctuation.MarkRealRegular
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small lemmas on the per-scale package `StepScaleData`

* `StepScaleData.beta_pos`: `0 < β` (from `0 < c_ψ`).
* `StepScaleData.two_p_lt_cψ`, `StepScaleData.p_lt_cψ`: `2 p₁ < c_ψ` and `p₁ < c_ψ` for `0 < p₁`
  (from `0 < lvR` and the ray margin).
* `StepScaleData.betaU_pos`: the coupling of the step is positive.
* `markReal_differentiableAt_Phi1C_scale'`: `markReal_differentiableAt_Phi1C_scale` without the
  hypothesis `0 < β`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Localization.I5Inhabited Balaban.Inhabited.LevelStep Balaban.SmallField Set

namespace StepScaleDataG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} {T : StepTowerG d L N κmin} {k : ℕ} {hk : 1 ≤ k}
  {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}

/-- The coupling `β` is positive: `0 < c_ψ = lvCpsiG … (β L^{k(d-2)})` forces
`β L^{k(d-2)} > 0`. -/
theorem beta_pos (D : StepScaleDataG T k hk N₁ ν β p₁) : 0 < β := by
  by_contra hb
  replace hb := not_lt.mp hb
  have hb' : β * (L : ℝ) ^ (k * (d - 2)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hb (by positivity)
  have : lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) = 0 := by
    unfold lvCpsiG
    rw [Real.sqrt_eq_zero_of_nonpos hb']; simp
  linarith [D.cψ_pos]

/-- `2 p₁ < c_ψ` for `0 < p₁` (ray margin and `0 < lvRG`). -/
theorem two_p_lt_cψ (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    2 * p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
  have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos D.r_pos hp
  nlinarith [D.ray_margin]

/-- `p₁ < c_ψ` for `0 < p₁`. -/
theorem p_lt_cψ (D : StepScaleDataG T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    p₁ < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) := by
  linarith [D.two_p_lt_cψ hp]

/-- The coupling `betaU = β L^{k(d-2)}` of the step is positive. -/
theorem betaU_pos (D : StepScaleDataG T k hk N₁ ν β p₁) (hd : 2 ≤ d) :
    0 < (T.step k hk N₁ ν β p₁).betaU := by
  rw [show (T.step k hk N₁ ν β p₁).betaU = β * (L : ℝ) ^ (k * (d - 2)) from
    hatStepKG_betaU T.hN hd k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ]
  have := D.beta_pos
  have hL : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

end StepScaleDataG

namespace StepScaleData

variable {κmin : ℝ} {T : StepTower κmin} {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
  {ν β p₁ : ℝ}

/-- The coupling `β` is positive: `0 < c_ψ = lvCpsi … (β 3^k)` forces `β 3^k > 0`. -/
theorem beta_pos (D : StepScaleData T k hk N₁ ν β p₁) : 0 < β :=
  (T.scaleDataG_of_fixed D).beta_pos

/-- `2 p₁ < c_ψ` for `0 < p₁` (ray margin and `0 < lvR`). -/
theorem two_p_lt_cψ (D : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    2 * p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
  have h := (T.scaleDataG_of_fixed D).two_p_lt_cψ hp
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  simpa [hb, lvCpsiG_three] using h

/-- `p₁ < c_ψ` for `0 < p₁`. -/
theorem p_lt_cψ (D : StepScaleData T k hk N₁ ν β p₁) (hp : 0 < p₁) :
    p₁ < lvCpsi T.κ T.t (β * 3 ^ k) := by
  linarith [D.two_p_lt_cψ hp]

/-- The coupling `betaU = β 3^k` of the step is positive. -/
theorem betaU_pos (D : StepScaleData T k hk N₁ ν β p₁) :
    0 < (T.step k hk N₁ ν β p₁).betaU := by
  rw [← T.toG_step_betaU]
  exact (T.scaleDataG_of_fixed D).betaU_pos (by norm_num)

end StepScaleData

/-- **`markReal_differentiableAt_Phi1C_scaleG` without the hypothesis `0 < β`**, which the package
`StepScaleDataG` implies. -/
theorem markReal_differentiableAt_Phi1C_scaleG' {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleDataG T k hk N₁ ν β p₁) (hp₁ : 0 < p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' N)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (hx : ‖x‖ ≤ p₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass d L N₁ T.m₁ k N (rhoSepG d L T.m₁)))
      ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) :=
  markReal_differentiableAt_Phi1C_scaleG T hS hS.beta_pos hp₁ D hDh hD hx hs

/-- **`markReal_differentiableAt_Phi1C_scale` without the hypothesis `0 < β`**, which the package
`StepScaleData` implies. -/
theorem markReal_differentiableAt_Phi1C_scale' {κmin : ℝ} (T : StepTower κmin) {k : ℕ}
    {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (hS : StepScaleData T k hk N₁ ν β p₁) (hp₁ : 0 < p₁)
    (D : BgData (T.step k hk N₁ ν β p₁).G' 2)
    (hDh : ∀ y i, D.h y i = ((T.step k hk N₁ ν β p₁).h₀ i : ℂ))
    (hD : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 T.t D)
    {x : ((T.step k hk N₁ ν β p₁).withDatum D hDh).E} (hx : ‖x‖ ≤ p₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℂ (((T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
        (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)))
      ((s : ℂ) • ((T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) :=
  markReal_differentiableAt_Phi1C_scale T hS hS.beta_pos hp₁ D hDh hD hx hs

end Balaban.Inhabited
