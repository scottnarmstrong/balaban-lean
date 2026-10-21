/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseResolvent
public import Balaban.LargeField.Base.ChartIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The site exponent of the first-step chart integral, over `ℂ` (LF-BASE-KF0 (A.2)-(A.3))

For a tangent vector `v = Q_e C^{1/2} ψ'` the chart integrand of the first fluctuation integral is
`e^{-V}`, `V = ∑_x V_x`,
```
V_x = ∑_y H_{xy} (v_x · z_y + ½ z_x · z_y) + ½ log(1 - v_x·v_x/β) - β^{-1/2} g_x · (v_x + z_x),
z_x = √β (√(1 - v_x·v_x/β) - 1) e_x,
```
(`-log J_x(v_x) = ½ log(1 - v_x·v_x/β)`).  This file defines `V_x` as a function of complex inputs
(the covariance square root `Sq`, the background `e`, the Hessian entries `H`, the fluctuation `ψ'`
and the source `g`), with the square root and the logarithm taken through `exp` and `log` of
`1 - v_x·v_x/β`, so that `V_x` is analytic in all the inputs wherever `1 - v_x·v_x/β` is in the slit
plane (`chartSite_analyticAt`), and identifies it with the landed real chart objects
(`chartShift`, `cinner`) when everything is real (`chartSite_real`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Matrix

section Alg

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- The complex tangent vector `v = Q_e w`, `Q_e = 1 - P_e` (the projection onto the directions
orthogonal to `e`, with the bilinear product). -/
noncomputable def chartTangent (e : ι → Fin N → ℂ) (w : ι × Fin N → ℂ) : ι × Fin N → ℂ :=
  (1 - basePart e) *ᵥ w

/-- `t_x = v_x · v_x / β`. -/
noncomputable def chartT (β : ℝ) (v : ι × Fin N → ℂ) (x : ι) : ℂ :=
  (∑ i, v (x, i) * v (x, i)) / (β : ℂ)

/-- `√(1 - t)` as `exp (½ log (1 - t))`. -/
noncomputable def chartSqrt (t : ℂ) : ℂ := Complex.exp (Complex.log (1 - t) / 2)

/-- The chart shift `z_x = √β (√(1 - t_x) - 1) e_x`. -/
noncomputable def chartZ (β : ℝ) (e : ι → Fin N → ℂ) (v : ι × Fin N → ℂ) : ι × Fin N → ℂ :=
  fun p => (Real.sqrt β : ℂ) * (chartSqrt (chartT β v p.1) - 1) * e p.1 p.2

/-- **The site exponent `V_x`** of the chart integrand. -/
noncomputable def chartSite (β : ℝ) (e : ι → Fin N → ℂ) (H : Matrix ι ι ℂ) (g w : ι × Fin N → ℂ)
    (x : ι) : ℂ :=
  let v := chartTangent e w
  let z := chartZ β e v
  (∑ y, H x y * (∑ i, v (x, i) * z (y, i))) + (1 / 2) * (∑ y, H x y * (∑ i, z (x, i) * z (y, i))) +
    (1 / 2) * Complex.log (1 - chartT β v x) -
    ((Real.sqrt β)⁻¹ : ℂ) * ∑ i, g (x, i) * (v (x, i) + z (x, i))

theorem basePart_apply' (e : ι → Fin N → ℂ) (p q : ι × Fin N) :
    basePart e p q = if p.1 = q.1 then e p.1 p.2 * e q.1 q.2 else 0 := by
  unfold basePart
  rw [Matrix.mul_apply, Finset.sum_eq_single p.1]
  · by_cases h : p.1 = q.1
    · simp [fieldMul, h]
    · simp [fieldMul, h]
      exact fun hq => absurd hq.symm h
  · intro z _ hz
    simp [fieldMul, Ne.symm hz]
  · simp

/-- The tangent vector in coordinates: `v_{x,i} = w_{x,i} - e_{x,i} ∑_j e_{x,j} w_{x,j}`. -/
theorem chartTangent_apply (e : ι → Fin N → ℂ) (w : ι × Fin N → ℂ) (x : ι) (i : Fin N) :
    chartTangent e w (x, i) = w (x, i) - e x i * ∑ j, e x j * w (x, j) := by
  unfold chartTangent
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, basePart_apply']
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
  · simp only [ite_true, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticAt_chartTangent {q₀ : E} {e : E → ι → Fin N → ℂ} {w : E → ι × Fin N → ℂ}
    (he : ∀ y i, AnalyticAt ℂ (fun q => e q y i) q₀)
    (hw : ∀ y i, AnalyticAt ℂ (fun q => w q (y, i)) q₀) (x : ι) (i : Fin N) :
    AnalyticAt ℂ (fun q => chartTangent (e q) (w q) (x, i)) q₀ := by
  simp only [chartTangent_apply]
  refine (hw x i).sub ((he x i).mul ?_)
  exact Finset.analyticAt_fun_sum _ fun j _ => (he x j).mul (hw x j)

theorem analyticAt_chartT {q₀ : E} {β : ℝ} {v : E → ι × Fin N → ℂ}
    (hv : ∀ y i, AnalyticAt ℂ (fun q => v q (y, i)) q₀) (x : ι) :
    AnalyticAt ℂ (fun q => chartT β (v q) x) q₀ := by
  unfold chartT
  simp only [div_eq_mul_inv]
  exact (Finset.analyticAt_fun_sum _ fun i _ => (hv x i).mul (hv x i)).mul analyticAt_const

theorem analyticAt_chartSqrt {q₀ : E} {t : E → ℂ} (ht : AnalyticAt ℂ t q₀)
    (hs : 1 - t q₀ ∈ Complex.slitPlane) : AnalyticAt ℂ (fun q => chartSqrt (t q)) q₀ := by
  unfold chartSqrt
  have h1 : AnalyticAt ℂ (fun q => Complex.log (1 - t q)) q₀ :=
    ((analyticAt_const.sub ht).clog hs)
  exact (analyticAt_cexp.comp (h1.div analyticAt_const (by norm_num)))

theorem analyticAt_chartSite {q₀ : E} {β : ℝ} {e : E → ι → Fin N → ℂ} {H : E → Matrix ι ι ℂ}
    {g w : E → ι × Fin N → ℂ} (he : ∀ y i, AnalyticAt ℂ (fun q => e q y i) q₀)
    (hH : ∀ x y, AnalyticAt ℂ (fun q => H q x y) q₀)
    (hg : ∀ y i, AnalyticAt ℂ (fun q => g q (y, i)) q₀)
    (hw : ∀ y i, AnalyticAt ℂ (fun q => w q (y, i)) q₀)
    (hs : ∀ x, 1 - chartT β (chartTangent (e q₀) (w q₀)) x ∈ Complex.slitPlane) (x : ι) :
    AnalyticAt ℂ (fun q => chartSite β (e q) (H q) (g q) (w q) x) q₀ := by
  have hv : ∀ y i, AnalyticAt ℂ (fun q => chartTangent (e q) (w q) (y, i)) q₀ :=
    analyticAt_chartTangent he hw
  have hT : ∀ y, AnalyticAt ℂ (fun q => chartT β (chartTangent (e q) (w q)) y) q₀ :=
    fun y => analyticAt_chartT hv y
  have hsq : ∀ y, AnalyticAt ℂ (fun q => chartSqrt (chartT β (chartTangent (e q) (w q)) y)) q₀ :=
    fun y => analyticAt_chartSqrt (hT y) (hs y)
  have hz : ∀ y i, AnalyticAt ℂ (fun q => chartZ β (e q) (chartTangent (e q) (w q)) (y, i)) q₀ :=
    fun y i => (analyticAt_const.mul ((hsq y).sub analyticAt_const)).mul (he y i)
  unfold chartSite
  simp only []
  refine ((((Finset.analyticAt_fun_sum _ fun y _ => (hH x y).mul
      (Finset.analyticAt_fun_sum _ fun i _ => (hv x i).mul (hz y i)))).add
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun y _ => (hH x y).mul
      (Finset.analyticAt_fun_sum _ fun i _ => (hz x i).mul (hz y i)))) ).add
    (analyticAt_const.mul ((analyticAt_const.sub (hT x)).clog (hs x)))).sub
    (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun i _ => (hg x i).mul
      ((hv x i).add (hz x i))))

end Analytic

section Real

/-- Real inputs: `1 - t` real in `(0, 1]` gives the real square root. -/
theorem chartSqrt_ofReal {t : ℝ} (h0 : t < 1) :
    chartSqrt (t : ℂ) = ((Real.sqrt (1 - t) : ℝ) : ℂ) := by
  unfold chartSqrt
  have hp : 0 < 1 - t := by linarith
  have e1 : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; ring
  rw [e1, ← Complex.ofReal_log hp.le, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem chartT_ofReal {β : ℝ} {v : ι × Fin N → ℂ} {vr : EuclideanSpace ℝ (Fin N)} {x : ι}
    (hv : ∀ i, v (x, i) = ((vr i : ℝ) : ℂ)) : chartT β v x = ((‖vr‖ ^ 2 / β : ℝ) : ℂ) := by
  unfold chartT
  simp only [hv, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum, EuclideanSpace.real_norm_sq_eq]
  simp [sq]

/-- **The complex site exponent is the real one for real data**: if `v` is the tangent vector of a
real configuration with `‖v_x‖² < β` for all `x`, `e` and the Hessian entries `a` are real, then
`V_x` is the cast of the real expression built from `chartShift` and the real inner product, plus
the source term. -/
theorem chartSite_real {β : ℝ} (hβ : 0 < β) (er : ι → EuclideanSpace ℝ (Fin N)) (a : ι → ι → ℝ)
    (g w : ι × Fin N → ℂ) (vr : ι → EuclideanSpace ℝ (Fin N))
    (hv : ∀ x i, chartTangent (fun x i => ((er x i : ℝ) : ℂ)) w (x, i) = ((vr x i : ℝ) : ℂ))
    (hlt : ∀ x, ‖vr x‖ ^ 2 < β) (x : ι) :
    chartSite β (fun x i => ((er x i : ℝ) : ℂ)) (fun x y => ((a x y : ℝ) : ℂ)) g w x =
      ((∑ y, a x y * (inner ℝ (vr x) (chartShift β er vr y) +
          (1 / 2) * inner ℝ (chartShift β er vr x) (chartShift β er vr y)) : ℝ) : ℂ) +
        (1 / 2) * ((Real.log (1 - ‖vr x‖ ^ 2 / β) : ℝ) : ℂ) -
        ((Real.sqrt β)⁻¹ : ℂ) * ∑ i, g (x, i) * (((vr x i + chartShift β er vr x i : ℝ)) : ℂ) := by
  have hT : ∀ y, chartT β (chartTangent (fun x i => ((er x i : ℝ) : ℂ)) w) y =
      ((‖vr y‖ ^ 2 / β : ℝ) : ℂ) := fun y => chartT_ofReal (fun i => hv y i)
  have ht1 : ∀ y, ‖vr y‖ ^ 2 / β < 1 := fun y => by
    rw [div_lt_one hβ]; exact hlt y
  have hZ : ∀ y i, chartZ β (fun x i => ((er x i : ℝ) : ℂ))
      (chartTangent (fun x i => ((er x i : ℝ) : ℂ)) w) (y, i) =
      ((chartShift β er vr y i : ℝ) : ℂ) := by
    intro y i
    unfold chartZ
    rw [hT y, chartSqrt_ofReal (ht1 y)]
    simp [chartShift]
  have hlog : ∀ y, Complex.log (1 - ((‖vr y‖ ^ 2 / β : ℝ) : ℂ)) =
      ((Real.log (1 - ‖vr y‖ ^ 2 / β) : ℝ) : ℂ) := fun y => by
    have hp : 0 < 1 - ‖vr y‖ ^ 2 / β := by linarith [ht1 y]
    have e1 : (1 : ℂ) - ((‖vr y‖ ^ 2 / β : ℝ) : ℂ) = ((1 - ‖vr y‖ ^ 2 / β : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, ← Complex.ofReal_log hp.le]
  unfold chartSite
  simp only [hv, hZ, hT, hlog]
  have hin : ∀ u w : EuclideanSpace ℝ (Fin N), inner ℝ u w = ∑ i, u i * w i := fun u w => by
    simp [PiLp.inner_apply, mul_comm]
  simp only [hin]
  push_cast
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 2
  · congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring_nf


end Real

end Alg

end Balaban.LargeField.Base
