/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepMeasure
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Positivity

/-!
# The Gaussian kernel `t_k` is a probability density (FLUCTUATION.md Definition 2.1)

* `tBlock c N ϑ w = (c/2π)^{N/2} exp (-(c/2) |ϑ - w|²)` (the kernel `t_k` of one block, with
  `c = β_k a L^{d-2}` in the units of the Background action);
* `integral_tBlock`: `∫_{ℝ^N} t(ϑ, w) dϑ = 1`;
* `integral_prod_tBlock`: `∫_{(ℝ^N)^Z} ∏_{z ∈ Z} t(θ(z), w(z)) dθ = 1` for a finite set of blocks `Z`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory
open scoped Real

/-- **The kernel `t_k(ϑ, w)` of one block**, for real `ϑ, w ∈ ℝ^N`. -/
noncomputable def tBlock (c : ℝ) (N : ℕ) (ϑ w : Rn N) : ℝ :=
  (c / (2 * π)) ^ ((N : ℝ) / 2) * Real.exp (-(c / 2) * ‖ϑ - w‖ ^ 2)

theorem tBlock_nonneg (c : ℝ) (N : ℕ) (ϑ w : Rn N) (hc : 0 ≤ c) : 0 ≤ tBlock c N ϑ w := by
  unfold tBlock
  positivity

/-- **`∫_{ℝ^N} t_k(ϑ, w) dϑ = 1`.** -/
theorem integral_tBlock {c : ℝ} (hc : 0 < c) (N : ℕ) (w : Rn N) :
    ∫ ϑ : Rn N, tBlock c N ϑ w = 1 := by
  unfold tBlock
  rw [integral_const_mul]
  have h1 : ∫ ϑ : Rn N, Real.exp (-(c / 2) * ‖ϑ - w‖ ^ 2) =
      ∫ v : Rn N, Real.exp (-(c / 2) * ‖v‖ ^ 2) :=
    integral_sub_right_eq_self (fun v : Rn N => Real.exp (-(c / 2) * ‖v‖ ^ 2)) w
  rw [h1, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < c / 2)]
  have hfr : (Module.finrank ℝ (Rn N) : ℝ) = N := by
    simp [Rn]
  rw [hfr, ← Real.mul_rpow (by positivity) (by positivity)]
  have : c / (2 * π) * (π / (c / 2)) = 1 := by
    field_simp
  rw [this, Real.one_rpow]

/-- **`∫ ∏_z t_k(θ(z), w(z)) dθ = 1`**: the block-product form of the normalisation. -/
theorem integral_prod_tBlock {c : ℝ} (hc : 0 < c) (N : ℕ) {Z : Type*} [Fintype Z]
    (w : Z → Rn N) :
    ∫ θ : Z → Rn N, ∏ z, tBlock c N (θ z) (w z) = 1 := by
  have := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (ι := Z) (E := fun _ : Z => Rn N)
    (fun z ϑ => tBlock c N ϑ (w z))
  rw [this]
  exact Finset.prod_eq_one fun z _ => integral_tBlock hc N (w z)

end Balaban.Fluctuation
