/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Transfer
public import Balaban.LargeField.Def7WitLF

/-!
# `TransferTyping` is inhabited

The typing of `Def7WitLF` (`d = 3`, `L = 3`, `M = 27`, `θ± = log 3`, `c_v = 100000`,
`c_H = 3 log 3`) with the budget constants `H₀ = 2`, `c₁ = 0`, `c₂ = 0` satisfies
`TransferTyping`, for every `κ, c₉`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7.Wit

/-- `TransferTyping` is satisfiable. -/
theorem transferTyping_exists : ∃ (d : ℕ) (Ty : ℝ → ℝ → Typing) (PB : ℝ → ℝ → BudgetConsts),
    TransferTyping d Ty PB := by
  refine ⟨3, fun _ _ => typing, fun _ _ => ⟨0, 0, 2, fun _ => 1⟩, ?_⟩
  intro κ _ c₉ _
  have hl := log_three_pos
  have hθ : thetaOf 3 ((3 : ℕ)) = Real.log 3 := by
    unfold thetaOf; norm_num
  refine ⟨typing_ok, ⟨?_, ?_⟩, ?_, by norm_num, le_rfl, ?_, ?_⟩
  · show Real.log 3 ≤ thetaOf 3 3
    rw [hθ]
  · show thetaOf 3 3 ≤ Real.log 3
    rw [hθ]
  · show (3 : ℝ) * ((3 : ℝ) - 2) / 2 * Real.log ((3 : ℕ) : ℝ) ≤ 3 * Real.log 3
    push_cast; linarith
  · show 3 ≤ 27; norm_num
  · show ((27 : ℕ) : ℝ) ^ 3 * (2 + 0 + 3) ≤ 100000
    norm_num

end Balaban.RootFSpine
