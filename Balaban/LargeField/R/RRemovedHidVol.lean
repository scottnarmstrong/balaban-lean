/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedShell

/-!
# The volume of the shells of a family of variables (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  `pi_shell_le_one`: for any finite family
of non-spin variables, the product measure of the set of configurations with every variable in its shell
`{|u·u - 1| < t_i}` is at most `1` when the radii satisfy `0 < t_i ≤ 1/2`, `c_N t_i ≤ 1`.  The shell
indicators of the new′ variables of the Jv-coordinates and of the window coordinates in `T` are integrated
with it.
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory

section Vol

variable {N : ℕ}

/-- **The shells of a finite family of non-spin variables have measure at most `1`.** -/
theorem pi_shell_le_one (hN : 2 ≤ N) {ι : Type} [Fintype ι] (b : ι → Bool) (hb : ∀ i, b i = false)
    (t : ι → ℝ) (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1 / 2) (hct : ∀ i, cShell N * t i ≤ 1) :
    (Measure.pi fun i => varMeasure N (b i))
      {x | ∀ i, |‖VarVal.toEuc (x i)‖ ^ 2 - 1| < t i} ≤ 1 := by
  have hset : {x : ∀ i, VarVal N (b i) | ∀ i, |‖VarVal.toEuc (x i)‖ ^ 2 - 1| < t i} =
      Set.pi Set.univ (fun i => (VarVal.toEuc : VarVal N (b i) → EuclideanSpace ℝ (Fin N)) ⁻¹'
        shellSet N (t i)) := by
    ext x; simp [shellSet]
  rw [hset]
  refine pi_pi_le_one (fun i => varMeasure N (b i)) _ fun i => ?_
  rw [(measurePreserving_toEuc_false (N := N) _ (hb i)).measure_preimage
    (measurableSet_shellSet N (t i)).nullMeasurableSet]
  exact (volume_shellSet_le N hN (ht i) (ht1 i)).trans (ENNReal.ofReal_le_one.mpr (hct i))

end Vol

end Balaban.LargeField
