/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.FootprintMargin
public import Balaban.Fluctuation.InteractionLevelPair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The footprint inclusion has instances

On the concrete whole-lattice level-`2` generating set `LevelPair.Gp` (`d = L = 3`, `N₁ = 9`,
`K = 2`) there is a centre `z` of the cover and a site `x` of its interaction box, so that the
hypotheses of `resDep_subset_hatBox` are met and its conclusion is a statement about a nonempty
set (`footprint_witness`).  The failure of the inclusion `resDep ⊆ intBox` (the reason the margin
`3 L ^ 2 ℓ` of the thickened box is needed) is not proved here: it needs a positive lower bound
for the spline at the face of the box.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation

/-- **Non-vacuity of the footprint inclusion** on `LevelPair.Gp`: for every `m₁ ≥ 2` there is a
centre `z` of the cover and a site `x` of `□_z` whose residual footprint is a nonempty subset of
`□̂_z`. -/
theorem footprint_witness (m₁ : ℕ) (ϱ : ℝ) (h : 2 ≤ m₁) :
    ∃ z ∈ cubeIdx (LevelPair.Gp m₁ ϱ), ∃ x ∈ intBox z,
      (resDep (LevelPair.Gp m₁ ϱ) x).Nonempty ∧
        resDep (LevelPair.Gp m₁ ϱ) x ⊆ hatBox z := by
  have hG : IsLevel (LevelPair.Gp m₁ ϱ) 2 := LevelPair.isLevel_Gp
  have hlay : (0 : CTorus 3 3 9 m₁ 2) ∈ (LevelPair.Gp m₁ ϱ).layer 2 := hG.mem_layer 0
  have hz := own_mem_cubeIdx (LevelPair.Gp_cubeAligned (ϱ := ϱ) h) (n := 2) (by norm_num)
    le_rfl hlay
  set z : ℕ × CTorus 3 3 9 m₁ 2 := (2, ownBase (2 + m₁) (0 : CTorus 3 3 9 m₁ 2)) with hzdef
  have hx : z.2 ∈ intBox z := by
    rw [mem_intBox]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (3 : ℝ) ^ (z.1 + m₁) := one_le_pow₀ (by norm_num)
    have hL : ((3 : ℕ) : ℝ) = 3 := by norm_num
    simp only [Int.cast_zero, zero_mul, add_zero, sub_add_cancel_left, abs_neg]
    rw [abs_of_nonneg (by simp only [Nat.cast_ofNat]; linarith)]
    simp only [Nat.cast_ofNat]
    linarith
  refine ⟨z, hz, z.2, hx, ⟨z.2, ?_⟩, resDep_subset_hatBox hG hz hx⟩
  unfold resDep
  exact Finset.mem_biUnion.2 ⟨z.2, mem_resSites_self _, mem_approxDep_self _⟩

end Balaban.Inhabited
