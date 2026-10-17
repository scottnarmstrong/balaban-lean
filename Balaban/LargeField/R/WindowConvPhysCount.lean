/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvWindow

/-!
# The count in a window decomposition needs a physical lower bound

The typing structure for cube and wall decompositions permits zero cube weights
on an arbitrary region. A regional source estimate measured by its total therefore
requires a separate positive-weight theorem for the decomposition used by the history.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ K ϱ}

/-- Every region admits a cube and wall decomposition with zero mixed count,
because the structure imposes only nonnegativity on cube weights. -/
theorem exists_stepDecomp_total_zero (X : Region G) :
    ∃ Dc : StepDecomp X, Dc.total = 0 := by
  classical
  let Dc : StepDecomp X :=
    { ι := Unit
      κ := Unit
      cube := fun _ => X
      wt := fun _ => 0
      wt_nonneg := by intro _; norm_num
      cube_disj := by
        intro i j hij
        exact False.elim (hij (Subsingleton.elim i j))
      cube_union := by simp
      wall := fun _ => X.crossing
      wall_disj := by
        intro i j hij
        exact False.elim (hij (Subsingleton.elim i j))
      wall_union := by simp
      wallCube := fun _ => ()
      inc := 1
      inc_le := by intro i; simp }
  refine ⟨Dc, ?_⟩
  simp [Dc, StepDecomp.total]

end Balaban.LargeField.ActionConv
