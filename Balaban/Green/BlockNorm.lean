/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.OneScaleDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The block `L²` norm and the unit-lattice single-scale Green's function

For a function `h` on the fine torus `Torus d ℓ` (`ℓ = N * m`) and a coarse site `y` let
`blockL2 N m y h = ((N^d)⁻¹ ∑_{x ∈ block y} h(x)²)^{1/2}`: the `L²` norm over the block of `y`
in unit-lattice measure (fine sites have mass `N⁻ᵈ`, as the fine spacing is `η = N⁻¹` in
units of the block side).  It is a seminorm with the triangle inequality
(`blockL2_sum_le`), and dominates block averages (`abs_blockAvg_le_blockL2`).

The matrix `Balaban.fineHamiltonian = N² (-Δ_unit) + ν + a P` is the unit-lattice operator of
GREEN.md; `Balaban.Green.oneScale_blockDecay` is the single-scale form of G-2(i) for it:
for `F` supported in the block `y'`,
`‖H⁻¹ F‖_{y} ≤ C₀ e^{-δ₀ dist(y, y')} ‖F‖_{y'}` with `C₀ = blockDecayConst d L`,
`δ₀ = blockDecayRate d`, uniformly in `k ≥ 1`, `N₀`, `ν ≥ 0`, `a ∈ [1/2, 2]`.
-/

@[expose] public section

namespace Balaban.Green

open Matrix Finset Balaban

variable {d ℓ N m : ℕ} [NeZero ℓ]

/-- The block `L²` norm (unit-lattice measure) of `h` over the block of the coarse site `y`. -/
noncomputable def blockL2 (N m : ℕ) (y : Torus d m) (h : Torus d ℓ → ℝ) : ℝ :=
  Real.sqrt (((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m y, h x ^ 2)

theorem blockL2_nonneg (y : Torus d m) (h : Torus d ℓ → ℝ) : 0 ≤ blockL2 N m y h :=
  Real.sqrt_nonneg _

/-- The block `L²` norm as a Euclidean norm. -/
noncomputable def blockL2Vec (N m : ℕ) (y : Torus d m) (h : Torus d ℓ → ℝ) :
    EuclideanSpace ℝ (blockFibre N m y : Finset (Torus d ℓ)) :=
  WithLp.toLp 2 fun x => Real.sqrt (((N : ℝ) ^ d)⁻¹) * h x

theorem blockL2_eq_norm (y : Torus d m) (h : Torus d ℓ → ℝ) :
    blockL2 N m y h = ‖blockL2Vec N m y h‖ := by
  rw [blockL2Vec, EuclideanSpace.norm_eq, blockL2]
  congr 1
  rw [← Finset.sum_coe_sort (blockFibre N m y) (fun x => h x ^ 2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by positivity)]

theorem blockL2Vec_sum (y : Torus d m) {κ : Type*} (s : Finset κ) (f : κ → Torus d ℓ → ℝ) :
    blockL2Vec N m y (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, blockL2Vec N m y (f i) := by
  ext x
  simp [blockL2Vec, Finset.mul_sum]

/-- The triangle inequality for sums. -/
theorem blockL2_sum_le (y : Torus d m) {κ : Type*} (s : Finset κ) (f : κ → Torus d ℓ → ℝ) :
    blockL2 N m y (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, blockL2 N m y (f i) := by
  simp only [blockL2_eq_norm, blockL2Vec_sum]
  exact norm_sum_le _ _

theorem blockL2_smul (y : Torus d m) (c : ℝ) (h : Torus d ℓ → ℝ) :
    blockL2 N m y (fun x => c * h x) = |c| * blockL2 N m y h := by
  unfold blockL2
  have : ∑ x ∈ blockFibre N m y, (c * h x) ^ 2 = c ^ 2 * ∑ x ∈ blockFibre N m y, h x ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [this, show ((N : ℝ) ^ d)⁻¹ * (c ^ 2 * ∑ x ∈ blockFibre N m y, h x ^ 2) =
      c ^ 2 * (((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m y, h x ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem blockL2_mono_of_abs_le (y : Torus d m) {h h' : Torus d ℓ → ℝ}
    (hh : ∀ x, |h x| ≤ |h' x|) : blockL2 N m y h ≤ blockL2 N m y h' := by
  unfold blockL2
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.sum_le_sum fun x _ => ?_
  exact sq_le_sq.2 (hh x)

/-- The block average is dominated by the block `L²` norm. -/
theorem abs_blockAvg_le_blockL2 [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N) (y : Torus d m)
    (v : Torus d ℓ → ℝ) :
    |((N : ℝ) ^ d)⁻¹ * ∑ x ∈ blockFibre N m y, v x| ≤ blockL2 N m y v := by
  unfold blockL2
  apply Real.abs_le_sqrt
  have hc := sq_sum_le_card_mul_sum_sq (s := blockFibre N m y) (f := v)
  rw [card_blockFibre hℓ] at hc
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  rw [mul_pow, inv_pow]
  push_cast at hc
  have : ((N : ℝ) ^ d)⁻¹ ^ 2 * (∑ x ∈ blockFibre N m y, v x) ^ 2 ≤
      ((N : ℝ) ^ d)⁻¹ ^ 2 * (((N : ℝ) ^ d) * ∑ x ∈ blockFibre N m y, v x ^ 2) :=
    mul_le_mul_of_nonneg_left hc (by positivity)
  calc _ = ((N : ℝ) ^ d)⁻¹ ^ 2 * (∑ x ∈ blockFibre N m y, v x) ^ 2 := by
        rw [inv_pow]
    _ ≤ _ := this
    _ = _ := by field_simp

end Balaban.Green
