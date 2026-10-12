/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolventMain
public import Balaban.Multiscale.AgmonCore
public import Balaban.Green.LimitCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Volume-independent row sums and range of `A_e(s)` (BASE-KERNEL-3 Theorem 1.1)

There are `J, R < ∞`, depending only on `d, L, ν` and not on the number `N₀` of blocks, the
domain `D`, the potential `α`, the parameters `s` or the background `e`, such that the block row
and column sums of `A_e(s)` are at most `J` and its blocks vanish beyond distance `R`
(`baseOp_rowSum_range`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Green Matrix Finset

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Torus

theorem matrix_eq_of_forms {n : Type*} [Fintype n] [DecidableEq n] (M M' : Matrix n n ℝ)
    (h : ∀ g φ : n → ℝ, g ⬝ᵥ M *ᵥ φ = g ⬝ᵥ M' *ᵥ φ) : M = M' := by
  ext x y
  have := h (Pi.single x 1) (Pi.single y 1)
  simpa [Matrix.mulVec_single_one, dotProduct_single_one] using this

/-- `-Δ + ν = ν + ∑_b T_b` on the torus (sum over all bonds). -/
theorem latticeLaplacian_eq_bonds (ν : ℝ) :
    latticeLaplacian d (N₀ * L ^ 1) ν = ν • (1 : Matrix (Torus d (N₀ * L ^ 1)) (Torus d (N₀ * L ^ 1)) ℝ) +
      ∑ b : FineBond d L N₀, bondMatrix b := by
  refine matrix_eq_of_forms _ _ fun g φ => ?_
  rw [latticeLaplacian_bilinear, Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec,
    dotProduct_sum]
  simp only [bondMatrix_bilinear, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul, Fintype.sum_prod_type]
  simp only [dotProduct]
  ring

theorem sum_abs_bondMatrix_row (b : FineBond d L N₀) (z : Torus d (N₀ * L ^ 1)) :
    ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y| ≤
      if (b.1 = z ∨ bondTip b = z) then 2 else 0 := by
  have hnorm : ∀ y, |bondMatrix b z y| = |bondVec b z| * |bondVec b y| := by
    intro y
    rw [bondMatrix, Matrix.vecMulVec_apply, abs_mul]
  simp only [hnorm]
  rw [← Finset.mul_sum]
  split_ifs with h
  · calc |bondVec b z| * ∑ y, |bondVec b y| ≤ 1 * 2 :=
          mul_le_mul (abs_bondVec_le_one b z) (sum_abs_bondVec_le b)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_le_one
      _ = 2 := one_mul _
  · have : bondVec b z = 0 := by
      by_contra hne; exact h (bondVec_ne_zero_mem b z hne)
    simp [this]

theorem sum_bonds_abs_row_le (S : Finset (FineBond d L N₀)) (z : Torus d (N₀ * L ^ 1)) :
    ∑ b ∈ S, ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y| ≤ 4 * d := by
  classical
  calc ∑ b ∈ S, ∑ y : Torus d (N₀ * L ^ 1), |bondMatrix b z y|
      ≤ ∑ b ∈ S, (if (b.1 = z ∨ bondTip b = z) then (2 : ℝ) else 0) :=
        Finset.sum_le_sum fun b _ => sum_abs_bondMatrix_row b z
    _ ≤ ∑ b : FineBond d L N₀, (if (b.1 = z ∨ bondTip b = z) then (2 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun b _ _ => by split_ifs <;> norm_num)
    _ = 2 * ((Finset.univ.filter fun b : FineBond d L N₀ =>
          b.1 = z ∨ bondTip b = z).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 2 * (2 * d : ℕ) := by
        gcongr
        exact_mod_cast card_bonds_at z
    _ = 4 * d := by push_cast; ring

end Torus

end Balaban.LargeField.Base
