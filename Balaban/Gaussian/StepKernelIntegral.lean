/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.Quiet
public import Balaban.LargeField.R.WindowGaussTree
import Mathlib.Tactic.Positivity

/-!
# Integrals of the product Gaussian kernel

For `c > 0` the kernel `t(·, w) = gaussT N c · w` has integral one, and so does the product kernel
over a finite set of blocks, also after the field renormalization `θ ↦ z θ` (with the factor
`z^{N|ι|}`). These identities are used by the renormalization step densities and by the first
step from the frozen partition function.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField

namespace Balaban.LargeField

/-- `gaussT` is the Gaussian density of the difference. -/
theorem gaussT_eq_gaussDens (N : ℕ) (c : ℝ) (ϑ w : EuclideanSpace ℝ (Fin N)) :
    gaussT N c ϑ w = gaussDens c (ϑ - w) := by
  unfold gaussT gaussDens
  rw [finrank_euclideanSpace_fin]

end Balaban.LargeField

namespace Balaban.RootFSpine

section Kernel

variable {N : ℕ}

/-- `∫ t_k(u, w) du = 1`. -/
theorem integral_gaussT_left {c : ℝ} (hc : 0 < c) (w : EuclideanSpace ℝ (Fin N)) :
    ∫ u, gaussT N c u w = 1 := by
  simp_rw [gaussT_eq_gaussDens N c _ w]
  rw [integral_sub_right_eq_self (fun u : EuclideanSpace ℝ (Fin N) => gaussDens c u) w,
    integral_gaussDens hc]

/-- `t_k(·, w)` is integrable. -/
theorem integrable_gaussT_left {c : ℝ} (hc : 0 < c) (w : EuclideanSpace ℝ (Fin N)) :
    Integrable (fun u : EuclideanSpace ℝ (Fin N) => gaussT N c u w) := by
  by_contra hni
  have := integral_gaussT_left (N := N) hc w
  rw [integral_undef hni] at this
  exact zero_ne_one this

variable {ι : Type*} [Fintype ι]

/-- The product kernel over a finite set of blocks is normalized. -/
theorem integral_prod_gaussT {c : ℝ} (hc : 0 < c) (w : ι → EuclideanSpace ℝ (Fin N)) :
    ∫ θ : ι → EuclideanSpace ℝ (Fin N), ∏ y, gaussT N c (θ y) (w y)
      ∂(Measure.pi fun _ => volume) = 1 := by
  rw [integral_fintype_prod_eq_prod (f := fun y u => gaussT N c u (w y))]
  exact Finset.prod_eq_one fun y _ => integral_gaussT_left hc _

theorem integrable_prod_gaussT {c : ℝ} (hc : 0 < c) (w : ι → EuclideanSpace ℝ (Fin N)) :
    Integrable (fun θ : ι → EuclideanSpace ℝ (Fin N) => ∏ y, gaussT N c (θ y) (w y))
      (Measure.pi fun _ => volume) :=
  Integrable.fintype_prod (f := fun y u => gaussT N c u (w y))
    fun _ => integrable_gaussT_left hc _

theorem finrank_blockField :
    Module.finrank ℝ (ι → EuclideanSpace ℝ (Fin N)) = N * Fintype.card ι := by
  simp [Module.finrank_pi_fintype, mul_comm]

/-- With the field renormalization `z`: `z^{N|ι|} ∫ ∏_y t(z θ_y, w_y) dθ = 1`. -/
theorem integral_prod_gaussT_smul {c z : ℝ} (hc : 0 < c) (hz : 0 < z)
    (w : ι → EuclideanSpace ℝ (Fin N)) :
    z ^ (N * Fintype.card ι) * ∫ θ : ι → EuclideanSpace ℝ (Fin N),
      ∏ y, gaussT N c (z • θ y) (w y) ∂(Measure.pi fun _ => volume) = 1 := by
  have h := Measure.integral_comp_smul (μ := (Measure.pi fun _ : ι =>
    (volume : Measure (EuclideanSpace ℝ (Fin N)))))
    (fun θ : ι → EuclideanSpace ℝ (Fin N) => ∏ y, gaussT N c (θ y) (w y)) z
  simp only [Pi.smul_apply] at h
  rw [h, integral_prod_gaussT hc w, finrank_blockField, smul_eq_mul, mul_one,
    abs_of_pos (by positivity)]
  exact mul_inv_cancel₀ (by positivity)

theorem integrable_prod_gaussT_smul {c z : ℝ} (hc : 0 < c) (hz : 0 < z)
    (w : ι → EuclideanSpace ℝ (Fin N)) :
    Integrable (fun θ : ι → EuclideanSpace ℝ (Fin N) => ∏ y, gaussT N c (z • θ y) (w y))
      (Measure.pi fun _ => volume) := by
  have := (integrable_prod_gaussT (N := N) hc w).comp_smul hz.ne'
  simpa only [Pi.smul_apply] using this

end Kernel

end Balaban.RootFSpine
