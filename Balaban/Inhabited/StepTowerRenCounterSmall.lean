/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerRenThetaClass
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The renormalized datum in the step chart at the class radii

The six smallness inequalities of `renThetaDatum_xiCData_scaled` hold at every class radius
`ε_j`, `j ≥ 1`, once `ε_1` is below the threshold of `exists_theta_small` (the class radii
decrease).  Such class constants exist for any `γ ∈ (0, 1/2)` and any bound on `ε_1`.  Combined:
at a step radius `t = λ ε_{k+1}`, the renormalized datum of a class-chart datum at radius
`ε_{k+1}` lies in the step chart.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Fluctuation Balaban.Localization

/-- **The smallness at every class radius.**  There is `ε* > 0` such that for class constants
with `0 < α₀`, `0 ≤ α` and `ε_1 ≤ ε*`, the six inequalities of `thetaChartMargin_of_small` hold at
`ε_j` for every `j ≥ 1`. -/
theorem classEps_theta_small (L N : ℕ) [NeZero L] :
    ∃ εs : ℝ, 0 < εs ∧ ∀ P : Consts, 0 < P.α₀ → 0 ≤ P.alpha 3 → P.eps 3 3 1 ≤ εs →
      ∀ j : ℕ, 1 ≤ j → 0 < P.eps 3 3 j ∧ (3 / 2 : ℝ) * P.eps 3 3 j ≤ 1 ∧
      (4 * 3 + 6) * ((2 * 3 + 1) * P.eps 3 3 j) ≤ 1 ∧
      (xiC1 3 + 15 / 2) * P.eps 3 3 j ≤ bgC1 3 L N ∧
      (3 / 2 : ℝ) * P.eps 3 3 j ≤ deltaStar 3 L N ∧
      bgK1 3 L N * (xiC1 3 * P.eps 3 3 j) ≤ deltaStar 3 L N ∧
      bgK1 3 L N * (xiC1 3 * P.eps 3 3 j) + cK2 3 L N * ((3 / 2 : ℝ) * P.eps 3 3 j) <
        bgC0 3 L N := by
  obtain ⟨εs, hεs, H⟩ := exists_theta_small 3 L N (by norm_num)
  refine ⟨εs, hεs, fun P hα₀ hα h1 j hj => ?_⟩
  have hpos : 0 < P.eps 3 3 j := by
    have := epsTail_pos j
    unfold Consts.eps epsSeq
    positivity
  have hle : P.eps 3 3 j ≤ εs := (classEps_antitone hα₀.le hα hj).trans h1
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := H _ hpos hle
  push_cast at a2
  exact ⟨hpos, a1, a2, a3, a4, a5, a6⟩

/-- **Class constants with a prescribed small first radius.**  For `0 < γ < 1/2` and `θ > 0`
there are class constants with `P.γ = γ`, `0 < P.α₀` and `P.eps 3 3 1 = θ`; hence `ε_1` can be
below any threshold, with the other premises of
`e0CoeffFamily_class_exists_tower_struct_step_collar_classEps_ren_phi` unchanged. -/
theorem exists_classConsts_eps_one {γ θ : ℝ} (hθ : 0 < θ) :
    ∃ P : Consts, P.γ = γ ∧ 0 < P.α₀ ∧ P.eps 3 3 1 = θ := by
  have ht := epsTail_pos 1
  refine ⟨⟨γ, 0, 0, 0, 0, 0, θ / (epsTail 1 * ((3 : ℕ) : ℝ) ^ (-(((3 : ℝ) - 2) / 2 - γ))), 0, 0,
    fun _ => 0, 0⟩, rfl, ?_, ?_⟩
  · show 0 < θ / (epsTail 1 * ((3 : ℕ) : ℝ) ^ (-(((3 : ℝ) - 2) / 2 - γ)))
    have : 0 < ((3 : ℕ) : ℝ) ^ (-(((3 : ℝ) - 2) / 2 - γ)) := by positivity
    positivity
  · unfold Consts.eps epsSeq Consts.alpha
    have : 0 < ((3 : ℕ) : ℝ) ^ (-(((3 : ℝ) - 2) / 2 - γ)) := by positivity
    simp only [pow_one]
    push_cast
    field_simp

end Balaban.Inhabited
