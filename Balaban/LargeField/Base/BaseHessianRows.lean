/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActAlg
public import Balaban.LargeField.Base.BaseBackgroundIdent
public import Balaban.Multiscale.AgmonCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Row sums of the Hessian `H` of the first step

The Hessian of the chart (`baseHamiltonian G a ν α 1 = dirichletOperator G a ν α`) is
`-Δ + ν + a_1 L^{-2} P + diag α` restricted to `Ω₁`, `P` the block projection.  Its rows have
`ℓ¹` norm at most `4d + |ν| + |a_1| L^{-2} + |α_x|` (`dirichletOperator_rowSum_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Matrix

section Lap

variable {d ℓ : ℕ} [NeZero ℓ]

theorem latticeLaplacian_entry (ν : ℝ) (x y : Torus d ℓ) :
    latticeLaplacian d ℓ ν x y = (if x = y then 2 * d + ν else 0) -
      ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then 1 else 0) +
        (if x = y + Pi.single μ 1 then 1 else 0)) := by
  unfold latticeLaplacian
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Matrix.sum_apply, Matrix.add_apply, Matrix.transpose_apply, shiftMatrix]

/-- The rows of `-Δ + ν` have `ℓ¹` norm `≤ 4d + |ν|`. -/
theorem latticeLaplacian_rowSum (ν : ℝ) (x : Torus d ℓ) :
    ∑ y, |latticeLaplacian d ℓ ν x y| ≤ 4 * d + |ν| := by
  have h1 : ∀ y, |latticeLaplacian d ℓ ν x y| ≤ (if x = y then |2 * (d : ℝ) + ν| else 0) +
      ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then 1 else 0) +
        (if x = y + Pi.single μ 1 then 1 else 0)) := by
    intro y
    rw [latticeLaplacian_entry]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [abs_of_nonneg (Finset.sum_nonneg fun μ _ => by split_ifs <;> norm_num)]
  refine (Finset.sum_le_sum fun y _ => h1 y).trans ?_
  rw [Finset.sum_add_distrib]
  have hA : ∑ y : Torus d ℓ, (if x = y then |2 * (d : ℝ) + ν| else 0) = |2 * (d : ℝ) + ν| := by
    simp
  have hB : ∑ y : Torus d ℓ, ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
      (if x = y + Pi.single μ 1 then 1 else 0)) = 2 * d := by
    rw [Finset.sum_comm]
    have : ∀ μ : Fin d, ∑ y : Torus d ℓ, ((if y = x + Pi.single μ 1 then (1 : ℝ) else 0) +
        (if x = y + Pi.single μ 1 then 1 else 0)) = 2 := by
      intro μ
      rw [Finset.sum_add_distrib]
      have e1 : ∑ y : Torus d ℓ, (if y = x + Pi.single μ 1 then (1 : ℝ) else 0) = 1 := by simp
      have e2 : ∑ y : Torus d ℓ, (if x = y + Pi.single μ 1 then (1 : ℝ) else 0) = 1 := by
        have : ∀ y : Torus d ℓ, (x = y + Pi.single μ 1) ↔ (y = x - Pi.single μ 1) := fun y => by
          rw [eq_sub_iff_add_eq, eq_comm]
        simp only [this]
        simp
      rw [e1, e2]; norm_num
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hA, hB]
  have : |2 * (d : ℝ) + ν| ≤ 2 * d + |ν| := (abs_add_le _ _).trans (by simp)
  linarith

end Lap

section Dir

variable {d L N₀ : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The rows of the Dirichlet operator at one layer have `ℓ¹` norm
`≤ 4d + |ν| + |a_1| L^{-2} + |α_x|`. -/
theorem dirichletOperator_rowSum_le (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (x : G.Ω 1) :
    ∑ y : G.Ω 1, ‖dirichletOperator G a ν α x y‖ ≤
      4 * d + |ν| + |a 1| / (L : ℝ) ^ 2 + ‖α x‖ := by
  classical
  have hent : ∀ y : G.Ω 1, ‖dirichletOperator G a ν α x y‖ ≤
      (|latticeLaplacian d (N₀ * L ^ 1) ν x y| + |a 1| / (L : ℝ) ^ 2 *
        blockProjMatrix d (N₀ * L ^ 1) (L ^ 1) (N₀ * L ^ (1 - 1)) x y) +
        (if x = y then ‖α x‖ else 0) := by
    intro y
    have hfull : dirichletOperator G a ν α x y =
        ((fullMatrix G a ν x y : ℝ) : ℂ) + (if x = y then α x else 0) := by
      unfold dirichletOperator
      simp [Green.restrictOp, Matrix.diagonal_apply]
    rw [hfull]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs]
      unfold fullMatrix avgMatrix
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.Icc_self, Finset.sum_singleton]
      refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
      · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((L : ℝ) ^ 1) ^ 2)]
        simp
      · unfold layerProjMatrix
        split_ifs
        · rw [abs_of_nonneg (blockProjMatrix_nonneg _ _ _)]
        · simp only [abs_zero]
          exact blockProjMatrix_nonneg _ _ _
    · split_ifs <;> simp
  have hsub : ∑ y : G.Ω 1, ((|latticeLaplacian d (N₀ * L ^ 1) ν x y| + |a 1| / (L : ℝ) ^ 2 *
        blockProjMatrix d (N₀ * L ^ 1) (L ^ 1) (N₀ * L ^ (1 - 1)) x y)) ≤
      4 * d + |ν| + |a 1| / (L : ℝ) ^ 2 := by
    rw [Finset.sum_coe_sort (G.Ω 1) (fun y => |latticeLaplacian d (N₀ * L ^ 1) ν x y| +
      |a 1| / (L : ℝ) ^ 2 * blockProjMatrix d (N₀ * L ^ 1) (L ^ 1) (N₀ * L ^ (1 - 1)) x y)]
    refine (Finset.sum_le_univ_sum_of_nonneg fun y => ?_).trans ?_
    · have := blockProjMatrix_nonneg (d := d) (N₀ := N₀) (L := L) (k := 1) 1 x y
      positivity
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, blockProjMatrix_row le_rfl]
      have := latticeLaplacian_rowSum (d := d) (ℓ := N₀ * L ^ 1) ν x
      linarith
  calc ∑ y : G.Ω 1, ‖dirichletOperator G a ν α x y‖
      ≤ ∑ y : G.Ω 1, ((|latticeLaplacian d (N₀ * L ^ 1) ν x y| + |a 1| / (L : ℝ) ^ 2 *
        blockProjMatrix d (N₀ * L ^ 1) (L ^ 1) (N₀ * L ^ (1 - 1)) x y) +
        (if x = y then ‖α x‖ else 0)) := Finset.sum_le_sum fun y _ => hent y
    _ = _ := by rw [Finset.sum_add_distrib]
    _ ≤ (4 * d + |ν| + |a 1| / (L : ℝ) ^ 2) + ‖α x‖ := by
        refine add_le_add hsub ?_
        simp

/-- The rows of the Hessian `H = baseHamiltonian G a ν α 1`. -/
theorem baseHamiltonian_rowSum_le (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (α : G.Ω 1 → ℂ) (x : G.Ω 1) :
    ∑ y : G.Ω 1, ‖baseHamiltonian G a ν α (fun _ => 1) x y‖ ≤
      4 * d + |ν| + |a 1| / (L : ℝ) ^ 2 + ‖α x‖ := by
  rw [baseHamiltonian_one]
  exact dirichletOperator_rowSum_le G a ν α x

end Dir

section Field

variable {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **`|e_x| ≤ 3/2`**: the components of a constraint field are bounded on `Ω₁`. -/
theorem restrictField_entry_le (G : GeneratingSet d L N₀ 1 ϱ) {δ : ℝ}
    {φ : Torus d (N₀ * L ^ 1) → Fin N → ℂ} (hφ : IsConstraintField G δ φ) (y : G.Ω 1)
    (i : Fin N) : ‖restrictField G φ y i‖ ≤ 3 / 2 :=
  (norm_le_vn _ i).trans (hφ.bound y y.2)

end Field

end Balaban.LargeField.Base
