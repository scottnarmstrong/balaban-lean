/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RootFInputs
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The prefix input is satisfiable

`prefixInput_exists`: for every `L ≥ 3` and every `0 < δ < 1/2` there are constants of the prefix
(as functions of `κ, c₉`) satisfying `PrefixInput`. The witness takes `m₀ = 1`, `m₁ = 3`,
`M = c = L⁴`, `M₁ = 1`, the kernel constant `a = 5/4`, the Def-6 exponents `γ = (1+2δ)/4`,
`α₁ = (1-2δ)/4` (so `γ - α₁ = δ`), `κ_flow = 3^{d+1} L^{2d+1} (κ+1)` and
`c₉^{flow} = (c₉/2) e^{-κ_flow}`. The clauses of `PrefixInput` are jointly satisfiable at every
`L ≥ 3`; no clause forces `L = 7`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.SmallField

/-- **`PrefixInput` is satisfiable** at every `L ≥ 3` and every `0 < δ < 1/2`. -/
theorem prefixInput_exists (d L : ℕ) (hL : 3 ≤ L) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ (Ty : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7)
      (cs₀ : ℝ → ℝ → OpConsts) (M1 c : ℝ → ℝ → ℕ), PrefixInput d δ Ty P6 C7 cs₀ M1 c := by
  have hLr : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hLpos : (0 : ℝ) < (L : ℝ) ^ 2 := by linarith
  have hinv : ((L : ℝ) ^ 2)⁻¹ ≤ 1 / 9 := by
    rw [inv_le_comm₀ hLpos (by norm_num)]; norm_num; exact hL2
  have hinv0 : 0 < ((L : ℝ) ^ 2)⁻¹ := inv_pos.2 hLpos
  have h14 : 14 ≤ L ^ (1 + 3) := by
    calc 14 ≤ 3 ^ (1 + 3) := by norm_num
      _ ≤ L ^ (1 + 3) := Nat.pow_le_pow_left hL _
  refine ⟨fun _ _ => ⟨d, L, L ^ (1 + 3), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    fun κ c₉ => ⟨(1 + 2 * δ) / 4, (1 - 2 * δ) / 4,
      (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1), 0, 1,
      c₉ / 2 * Real.exp (-((3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1))), 1, 1,
      7 / 8 * ((L : ℝ) ^ 2)⁻¹, fun _ => 1, 1⟩,
    fun _ _ => ⟨3, 0, 0, 1, 0⟩,
    fun _ _ => ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, 0,
      fun _ => 0, fun _ => 0, 5 / 4, 0, 1⟩,
    fun _ _ => 1, fun _ _ => L ^ (1 + 3), ?_⟩
  intro κ hκ c₉ hc₉
  have hκf : 0 < (3 : ℝ) ^ (d + 1) * (L : ℝ) ^ (2 * d + 1) * (κ + 1) := by positivity
  refine ⟨hL, by norm_num, by norm_num, ?_, by simp, h14, le_rfl, by simp, ?_, ?_, by norm_num,
    le_rfl, ?_, ?_, ?_⟩
  · have h1 : (8 : ℝ) / 9 ≤ 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
    have h2 : (64 : ℝ) / 81 ≤ (1 - ((L : ℝ) ^ 2)⁻¹) ^ 2 := by nlinarith
    show (9 : ℝ) / 10 ≤ 5 / 4 * _
    nlinarith
  · refine ⟨?_, ?_, ?_, ?_, by norm_num, hκf, mul_pos (by norm_num) hinv0, ?_, by norm_num, le_rfl⟩ <;>
      simp only [] <;> linarith
  · show 0 < c₉ / 2 * Real.exp _
    positivity
  · show δ ≤ (1 + 2 * δ) / 4 - (1 - 2 * δ) / 4
    linarith
  · exact le_rfl
  · exact le_rfl
