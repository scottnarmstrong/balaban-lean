/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerScaleTNum
public import Balaban.Fluctuation.LocalClassDensityIrrelStepRoom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The towers at the scale-dependent step radius `t_k ≤ ε_{k+1}` and the room condition

For an antitone sequence `ε` (the radii `ε_j` of the class domains) and every scale `k`
`exists_stepTower_room` gives a tower `T_k` with the parameters of a fixed tower `T` (the same
`m₁, c, B_G, κ, c₂, B_G₂, δ_c, δ, δ'`, the same `κ_dec`) and the radius
`t_k = l_k T.t`, `l_k = min 1 (ε_{k+1} / R)`, `R = t + K₂(δ₃ + δ_fl)`, with `δ₃^{(k)} = l_k δ₃`,
`δ_fl^{(k)} = l_k δ_fl`, for which the room condition
`t_k + K₂ δ₃^{(k)} + K₂ δ_fl^{(k)} ≤ ε_j` of `d2raw_d1Triple_mem_xiDom` holds for all `j ≤ k + 1`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited

/-- **The room condition of the class chain at the scale `k`.**  For every antitone `ε` and scale
`k` with `ε_{k+1} > 0` the tower `T_k` of `exists_stepTower_scale_num` at the proportion
`l_k = min 1 (ε_{k+1} / R)` has `t_k ≤ ε_{k+1}`, `t_k = l_k t` and
`t_k + K₂ (l_k δ₃) + K₂ (l_k δ_fl) ≤ ε_j` for all `j ≤ k + 1`. -/
theorem exists_stepTower_room (m₀ : ℕ) (κlo : ℝ) :
    ∃ (κmin : ℝ) (_ : κlo ≤ κmin) (T : StepTower κmin) (δ₃ δfl κdec : ℝ),
      4 * 3 * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) * κdec ≤ T.κ ∧
      (2 * T.κdec - 1) * (((3 : ℕ) : ℝ) ^ (m₀ - 1) + 2 * ((3 : ℕ) : ℝ) *
        ((3 : ℕ) : ℝ) ^ m₀ * ((((3 ^ (m₀ - 1)) ^ 3 : ℕ)) : ℝ) * c1 3 3) + 1 ≤ 2 * κdec ∧
      ChainNum 3 3 2 T.m₁ T.BG T.κ 324 T.t δ₃ ∧ FlNum 3 3 2 T.BG T.BG₂ T.κ T.t δ₃ T.t δfl ∧
      ∀ ε : ℕ → ℝ, Antitone ε → ∀ k : ℕ, 0 < ε (k + 1) →
        ∃ T' : StepTower κmin, ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧
          l = min 1 (ε (k + 1) / (T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl)) ∧
          T'.t = l * T.t ∧ T'.t ≤ ε (k + 1) ∧ T'.m₁ = T.m₁ ∧
          T'.c = T.c ∧ T'.BG = T.BG ∧ T'.κ = T.κ ∧ T'.c₂ = T.c₂ ∧ T'.BG₂ = T.BG₂ ∧
          T'.δc = T.δc ∧ T'.δ = T.δ ∧ T'.δ' = T.δ' ∧
          ChainNum 3 3 2 T'.m₁ T'.BG T'.κ 324 T'.t (l * δ₃) ∧
          FlNum 3 3 2 T'.BG T'.BG₂ T'.κ T'.t (l * δ₃) T'.t (l * δfl) ∧
          ∀ j ≤ k + 1, T'.t + xiK2 3 3 2 * (l * δ₃) + xiK2 3 3 2 * (l * δfl) ≤ ε j := by
  obtain ⟨κmin, hlo, T, δ₃, δfl, κdec, h3, h4, h1, h2, H⟩ := exists_stepTower_scale_num m₀ κlo
  refine ⟨κmin, hlo, T, δ₃, δfl, κdec, h3, h4, h1, h2, fun ε hε k hk => ?_⟩
  have hx : 0 ≤ xiK2 3 3 2 := by
    have := cK2_pos 3 3 2
    unfold xiK2; positivity
  have ht := T.t_pos
  have hd := h1.δ₃_nn
  have hf := h2.δfl_nn
  set R : ℝ := T.t + xiK2 3 3 2 * δ₃ + xiK2 3 3 2 * δfl with hR
  have hR0 : 0 < R := by
    have := mul_nonneg hx hd
    have := mul_nonneg hx hf
    linarith
  have hl0 : 0 < min 1 (ε (k + 1) / R) := lt_min one_pos (div_pos hk hR0)
  obtain ⟨T', hT, hm, hc, hB, hκ, hc₂, hB₂, hδc, hδ, hδ', hC, hF⟩ :=
    H (min 1 (ε (k + 1) / R)) hl0 (min_le_left _ _)
  have hlR : min 1 (ε (k + 1) / R) * R ≤ ε (k + 1) := by
    calc min 1 (ε (k + 1) / R) * R ≤ (ε (k + 1) / R) * R :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hR0.le
      _ = ε (k + 1) := div_mul_cancel₀ _ hR0.ne'
  have hroom : T'.t + xiK2 3 3 2 * (min 1 (ε (k + 1) / R) * δ₃) +
      xiK2 3 3 2 * (min 1 (ε (k + 1) / R) * δfl) = min 1 (ε (k + 1) / R) * R := by
    rw [hT, hR]; ring
  refine ⟨T', min 1 (ε (k + 1) / R), hl0, min_le_left _ _, rfl, hT, ?_, hm, hc, hB, hκ, hc₂, hB₂,
    hδc, hδ, hδ', hC, hF, fun j hj => ?_⟩
  · rw [hT]
    have : min 1 (ε (k + 1) / R) * T.t ≤ min 1 (ε (k + 1) / R) * R := by
      apply mul_le_mul_of_nonneg_left _ hl0.le
      have := mul_nonneg hx hd
      have := mul_nonneg hx hf
      linarith
    linarith
  · rw [hroom]
    exact hlR.trans (hε hj)

end Balaban.Inhabited
