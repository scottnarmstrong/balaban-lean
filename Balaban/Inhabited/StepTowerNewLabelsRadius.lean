/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctFacts
public import Balaban.SmallField.LocalSuccessorRadius
public import Balaban.Localization.DecoupledFieldClose
public import Balaban.Inhabited.StepTower
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The radius of the new level against the radius of the step (`StepTowerNewLabelsRadius`)

The terms born at step `k` are terms of level `k + 1` of the class: analytic on the class domain
`Ξ^c_{k+1}(·; 1, ε_{k+1})`, `ε_j = P.eps d L j` (P4 Prop. 4.1, (4.23), p. 706; the step variables
of P4 (4.9), p. 702, range over `Ξ_{k+1}(1, ε_{k+1})`).  The class chain produces them, and their
expansion identity, on the step chart of radius `t` (`physV … t`, `XiDom S.G' … ε`, `ε ≤ t`), so
the new level needs `ε_{k+1} ≤ t`.  The inherited terms are read at the composed step data, which
need the room `t + K₂ δ₃ + K₂ δ_fl ≤ ε_j`, `j ≤ k` (`d2raw_d1Triple_mem_xiDom`, W1040 (B)).

`not_newLevel_cover_and_room`: at `d = L = 3`, `N = 2`, `γ ≥ 0`, with the fluctuation numerics
`FlNum … t δ₃ t δfl` of the landed interface (fluctuation ball `δ₁` equal to the step radius `t`),
the two conditions `ε_{k+1} ≤ t` and `t + K₂ δ₃ + K₂ δ_fl ≤ ε_k` exclude each other: `FlNum.flb`
gives `δ_fl ≥ 2 t`, `K₂ = xiK2 3 3 2 ≥ 58`, so the room needs `ε_k ≥ 117 t`, while
`ε_k ≤ 2 · 3^α ε_{k+1} < 4 ε_{k+1}` (`epsSeq_le_two_rpow_mul_succ`, `α = 1/2 − γ ≤ 1/2`).
`flNum_room_ge` is the inequality `117 t ≤ t + K₂ δ₃ + K₂ δ_fl`; in particular the step radius of the
towers of `exists_stepTower_room` (room at every `j ≤ k + 1`) is at most `ε_{k+1} / 117`.
`StepTower.not_newLevel_cover_and_room` is the statement for the step of a tower.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6 Balaban.Background

/-- `3 ^ α < 2` for `α ≤ 1 / 2`. -/
theorem three_rpow_lt_two {α : ℝ} (hα : α ≤ 1 / 2) : (3 : ℝ) ^ α < 2 := by
  have h1 : (3 : ℝ) ^ α ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hα
  have h2 : (3 : ℝ) ^ (1 / 2 : ℝ) < 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_lt' (by norm_num)]
    norm_num
  linarith

/-- **The room of the composed step data is at least `117` step radii** when the fluctuation ball
is the step radius (`FlNum … t δ₃ t δfl`, `d = L = 3`, `N = 2`): `δ_fl ≥ 2 t` and
`K₂ = xiK2 3 3 2 ≥ 58`. -/
theorem flNum_room_ge {BG BG₂ κ t δ₃ δfl : ℝ} (hF : FlNum 3 3 2 BG BG₂ κ t δ₃ t δfl)
    (hδ₃ : 0 ≤ δ₃) (hfam : 0 ≤ famConst 3 3 BG₂ κ) :
    117 * t ≤ t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl := by
  have ht : 0 < t := hF.δ₁_pos
  have hc' : 0 ≤ cK2' 3 3 2 (famConst 3 3 BG₂ κ) := cK2'_nonneg hfam
  have hfl : 2 * t ≤ δfl := by
    have := hF.flb
    push_cast at this
    nlinarith
  have hK : 58 ≤ xiK2 3 3 2 := by
    have := cK2_pos (d := 3) (L := 3) (N := 2)
    unfold xiK2
    push_cast
    nlinarith
  have h1 : 0 ≤ xiK2 3 3 2 * δ₃ := mul_nonneg (by linarith) hδ₃
  have h2 : 58 * (2 * t) ≤ xiK2 3 3 2 * δfl :=
    mul_le_mul hK hfl (by linarith) (by linarith)
  linarith

/-- **The new level is not covered by the step chart when the inherited room holds** (`d = L = 3`,
`N = 2`, fluctuation ball equal to the step radius): there is no step radius `t` with
`ε_{k+1} ≤ t` (the class domain of the new level inside the step chart) and
`t + K₂ δ₃ + K₂ δ_fl ≤ ε_k` (the composed step data in the class domain of level `k`). -/
theorem not_newLevel_cover_and_room {P : Consts} (hα₀ : 0 < P.α₀) (hγ : 0 ≤ P.γ)
    {BG BG₂ κ t δ₃ δfl : ℝ} (hF : FlNum 3 3 2 BG BG₂ κ t δ₃ t δfl) (hδ₃ : 0 ≤ δ₃)
    (hfam : 0 ≤ famConst 3 3 BG₂ κ) (k : ℕ) :
    ¬ (P.eps 3 3 (k + 1) ≤ t ∧ t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl ≤ P.eps 3 3 k) := by
  rintro ⟨hcov, hroom⟩
  have hroom' := (flNum_room_ge hF hδ₃ hfam).trans hroom
  have hgap := GsSpec.epsSeq_le_two_rpow_mul_succ 3 (P.alpha 3) P.α₀ hα₀.le k
  have hpos : 0 < P.eps 3 3 (k + 1) := by
    have := epsTail_pos (k + 1)
    unfold Consts.eps epsSeq
    positivity
  have hα : P.alpha 3 ≤ 1 / 2 := by
    unfold Consts.alpha; push_cast; linarith
  have h3 : ((3 : ℕ) : ℝ) ^ P.alpha 3 < 2 := by
    push_cast; exact three_rpow_lt_two hα
  have hgap' : P.eps 3 3 k ≤ 4 * P.eps 3 3 (k + 1) := by
    have : 2 * ((3 : ℕ) : ℝ) ^ P.alpha 3 * P.eps 3 3 (k + 1) ≤ 4 * P.eps 3 3 (k + 1) := by
      nlinarith
    exact (show P.eps 3 3 k ≤ 2 * ((3 : ℕ) : ℝ) ^ P.alpha 3 * P.eps 3 3 (k + 1) from hgap).trans
      this
  linarith

/-- **`not_newLevel_cover_and_room` for the step of a tower**: with the numerics
`FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl` of the tower's step (as in `exists_stepTower_room`),
no class radius sequence `ε_j = P.eps 3 3 j` (`α₀ > 0`, `γ ≥ 0`) has both `ε_{k+1} ≤ T.t` and
`T.t + K₂ δ₃ + K₂ δ_fl ≤ ε_k`. -/
theorem StepTower.not_newLevel_cover_and_room {κmin : ℝ} (T : StepTower κmin) {P : Consts}
    (hα₀ : 0 < P.α₀) (hγ : 0 ≤ P.γ) {δ₃ δfl : ℝ}
    (hF : FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl) (hδ₃ : 0 ≤ δ₃) (k : ℕ) :
    ¬ (P.eps 3 3 (k + 1) ≤ T.t ∧ T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl ≤ P.eps 3 3 k) :=
  Balaban.Inhabited.not_newLevel_cover_and_room hα₀ hγ hF hδ₃ T.fam_nonneg k

end Balaban.Inhabited
