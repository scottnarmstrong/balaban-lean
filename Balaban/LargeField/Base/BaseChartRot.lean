/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActAlg
import Mathlib.Tactic.Linarith

/-!
# `O(N)` covariance of the chart exponent

For a matrix `R` with `Rᵀ R = 1` acting componentwise (`rotVec`, `rotE`): the tangent vector, the factor
`t_x`, the shift `z` and the site exponent `V_x` of the chart are covariant
(`chartTangent_rot`, `chartT_rot`, `chartZ_rot`, `chartSite_rot`): `V_x` does not change when the
background, the source and the field are rotated together.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix

section Rot

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The action of a matrix on the components of a field `w : ι × Fin N → ℂ`, site by site. -/
def rotVec (R : Matrix (Fin N) (Fin N) ℂ) (w : ι × Fin N → ℂ) : ι × Fin N → ℂ :=
  fun p => R.mulVec (fun i => w (p.1, i)) p.2

/-- The action of a matrix on a background `e : ι → Fin N → ℂ`, site by site. -/
def rotE (R : Matrix (Fin N) (Fin N) ℂ) (e : ι → Fin N → ℂ) : ι → Fin N → ℂ :=
  fun y => R.mulVec (e y)

theorem sum_mulVec_mul_mulVec {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1)
    (a b : Fin N → ℂ) : ∑ j, R.mulVec a j * R.mulVec b j = ∑ j, a j * b j := by
  simp only [Matrix.mulVec, dotProduct]
  have hent : ∀ j k, ∑ i, R i j * R i k = if j = k then 1 else 0 := by
    intro j k
    have := congrFun (congrFun hR j) k
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this
  calc ∑ i, (∑ j, R i j * a j) * (∑ k, R i k * b k)
      = ∑ i, ∑ j, ∑ k, R i j * R i k * (a j * b k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ j, ∑ k, (∑ i, R i j * R i k) * (a j * b k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ j, a j * b j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hent, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem chartTangent_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1)
    (e : ι → Fin N → ℂ) (w : ι × Fin N → ℂ) :
    chartTangent (rotE R e) (rotVec R w) = rotVec R (chartTangent e w) := by
  funext ⟨x, i⟩
  rw [chartTangent_apply]
  have hs : ∑ j, rotE R e x j * rotVec R w (x, j) = ∑ j, e x j * w (x, j) :=
    sum_mulVec_mul_mulVec hR (e x) (fun j => w (x, j))
  rw [hs]
  simp only [rotVec, rotE, chartTangent_apply]
  have : (fun j => w (x, j) - e x j * ∑ k, e x k * w (x, k)) =
      (fun j => w (x, j)) - (∑ k, e x k * w (x, k)) • e x := by
    funext j; simp [mul_comm]
  rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp [mul_comm]

omit [Fintype ι] [DecidableEq ι] in
theorem chartT_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (β : ℝ)
    (v : ι × Fin N → ℂ) (x : ι) : chartT β (rotVec R v) x = chartT β v x := by
  unfold chartT
  rw [show (∑ i, rotVec R v (x, i) * rotVec R v (x, i)) = ∑ i, v (x, i) * v (x, i) from
    sum_mulVec_mul_mulVec hR (fun j => v (x, j)) (fun j => v (x, j))]

omit [Fintype ι] [DecidableEq ι] in
theorem chartZ_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (β : ℝ)
    (e : ι → Fin N → ℂ) (v : ι × Fin N → ℂ) :
    chartZ β (rotE R e) (rotVec R v) = rotVec R (chartZ β e v) := by
  funext ⟨y, i⟩
  simp only [chartZ, chartT_rot hR, rotVec, rotE]
  have : (fun j => (Real.sqrt β : ℂ) * (chartSqrt (chartT β v y) - 1) * e y j) =
      ((Real.sqrt β : ℂ) * (chartSqrt (chartT β v y) - 1)) • e y := by
    funext j; simp
  rw [this, Matrix.mulVec_smul]
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem dot_rotVec {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (a b : ι × Fin N → ℂ)
    (x y : ι) : ∑ i, rotVec R a (x, i) * rotVec R b (y, i) = ∑ i, a (x, i) * b (y, i) :=
  sum_mulVec_mul_mulVec hR (fun j => a (x, j)) (fun j => b (y, j))

/-- **`O(N)` covariance of the site exponent `V_x`** of the chart: rotating the background, the source
and the field by `R` (`Rᵀ R = 1`) does not change `V_x`. -/
theorem chartSite_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : R.transpose * R = 1) (β : ℝ)
    (e : ι → Fin N → ℂ) (H : Matrix ι ι ℂ) (g w : ι × Fin N → ℂ) (x : ι) :
    chartSite β (rotE R e) H (rotVec R g) (rotVec R w) x = chartSite β e H g w x := by
  unfold chartSite
  simp only [chartTangent_rot hR, chartZ_rot hR, chartT_rot hR, dot_rotVec hR]
  have hvz : ∀ i, (rotVec R (chartTangent e w)) (x, i) + (rotVec R (chartZ β e (chartTangent e w))) (x, i)
      = rotVec R (chartTangent e w + chartZ β e (chartTangent e w)) (x, i) := fun i => by
    simp only [rotVec]
    rw [← Pi.add_apply, ← Matrix.mulVec_add]
    rfl
  simp only [hvz, dot_rotVec hR]
  rfl

end Rot

end Balaban.LargeField.Base
