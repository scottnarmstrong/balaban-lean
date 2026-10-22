/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRemainderLocal
public import Balaban.LargeField.Base.BaseFirstFIntegrable
public import Balaban.LargeField.Base.BaseChartActionPhysical

/-!
# The first-sector chart integrand as the exponential of a site sum

On the tangent balls `|v_x| < √β` the chart integrand `F = baseSectorF` is the cutoff `χ`, the
kernel normalization `κ`, the constant `exp(-β B(e) + ⟨g, e⟩)` and `exp(-∑_x V_x(v))`, where the
site exponent is
`V_x = ∑_y a_{xy} (⟨v_x, z_y⟩ + ½⟨z_x, z_y⟩) + c |φ_x - h|² + ½ log(1 - |v_x|²/β)
        - β^{-1/2} g_x · (v_x + z_x)`
with `z = chartShift β e v`, `φ = chartPoint β e v` (LF-BASE-KF0 (A.2)-(A.3); the Jacobian
`J_x = (1 - |v_x|²/β)^{-1/2}`, the cross and quadratic terms of the normal shift, the source and the
mass term, each as a sum over sites). The pair term reads `v_x` and `v_y` only.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical
open Balaban.LargeField.Base MeasureTheory SphereChart

variable {ι : Type*} [Fintype ι] {N : ℕ}

/-- **The site exponent `V_x` of the chart integrand** for real data: the pair sum with the real
Hessian entries `a`, the mass term `c|φ_x - h|²` (`c = β(ν - μ)/2`), `½ log(1 - |v_x|²/β)`
(`-log J_x`) and the source term (compare `chartSite_real` of the complex site exponent). -/
noncomputable def chartSiteReal (β : ℝ) (e : Config ι N) (a : ι → ι → ℝ) (c : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (g : ι → Fin N → ℂ) (w : Config ι N) (x : ι) : ℂ :=
  ((∑ y, a x y * (inner ℝ (w x) (chartShift β e w y) +
      (1 / 2) * inner ℝ (chartShift β e w x) (chartShift β e w y)) +
    c * ‖chartPoint β e w x - h‖ ^ 2 + (1 / 2) * Real.log (1 - ‖w x‖ ^ 2 / β) : ℝ) : ℂ) -
  ((Real.sqrt β)⁻¹ : ℂ) * ∑ i, g x i * (((w x + chartShift β e w x) i : ℝ) : ℂ)

/-- The chart Jacobian is `exp(-½ ∑_x log(1 - |w_x|²/β))` inside the tangent balls. -/
theorem chartJac_eq_exp {β : ℝ} (hβ : 0 < β) (w : Config ι N) (hw : ∀ x, ‖w x‖ < Real.sqrt β) :
    chartJac β w = Real.exp (-(∑ x, (1 / 2) * Real.log (1 - ‖w x‖ ^ 2 / β))) := by
  have hpos : ∀ x, 0 < 1 - ‖w x‖ ^ 2 / β := fun x => by
    have h1 : ‖w x‖ ^ 2 < β := by
      have := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 (hw x)
      rwa [Real.sq_sqrt hβ.le] at this
    rw [sub_pos, div_lt_one hβ]; exact h1
  have hx : ∀ x, (if ‖w x‖ < Real.sqrt β then (Real.sqrt (1 - ‖w x‖ ^ 2 / β))⁻¹ else 0) =
      Real.exp (-((1 / 2) * Real.log (1 - ‖w x‖ ^ 2 / β))) := by
    intro x
    simp only [hw x, ↓reduceIte]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (hpos x), ← Real.exp_neg]
    congr 1
    ring
  unfold chartJac
  rw [Finset.prod_congr rfl (fun x _ => hx x), ← Real.exp_sum, Finset.sum_neg_distrib]

section Sector

variable {d L n : ℕ} [NeZero L] [NeZero n]

/-- **The first-sector chart integrand as the exponential of a site sum.** Inside the tangent
balls, `F(v) = χ(φ) κ e^{-β B(e) + ⟨g, e⟩} exp(-∑_x V_x(v))` with `φ` the chart point and `V_x` the
site exponent `chartSiteReal` (`a` the entries of the Hessian `Hα`, `c = β(ν - μ)/2`). -/
theorem baseSectorF_eq_exp_neg_sum {β : ℝ} (hβ : 0 < β) (a₀ ν : ℝ) (regimeB : Prop)
    (h : EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (e : Config (Torus d (L * n)) N)
    (he : ∀ x, ‖e x‖ = 1)
    (Hα : Config (Torus d (L * n)) N →ₗ[ℝ] Config (Torus d (L * n)) N)
    (a : Torus d (L * n) → Torus d (L * n) → ℝ)
    (hH : ∀ u x i, (Hα u x i : ℝ) = ∑ y, a x y * (u y i : ℝ))
    (χ : CfgT d N L n → ℝ) (κ : ℂ)
    (v : (x : Torus d (L * n)) → perp (e x)) (hv : ∀ x, ‖v x‖ < Real.sqrt β) :
    let ec : CfgT d N L n := fun x => ⟨e x, mem_sphere_zero_iff_norm.mpr (he x)⟩
    let w : Config (Torus d (L * n)) N := fun x => (v x : EuclideanSpace ℝ (Fin N))
    baseSectorF β a₀ ν regimeB h g θ e he Hα χ κ v =
      ((χ (chartMapPi e he ((Real.sqrt β)⁻¹ • v)) : ℝ) : ℂ) * κ *
        Complex.exp (-((β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2) : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N, g x i * (((e x) i : ℝ) : ℂ)) *
        Complex.exp (-(∑ x, chartSiteReal β e a (β * (ν - (if regimeB then ν else 0)) / 2) h g w x)) := by
  intro ec w
  have hpt := chartMapPi_inv_sqrt_eq_chartPoint e he hβ v hv
  have hφ : ∀ x, (chartMapPi e he ((Real.sqrt β)⁻¹ • v) x : EuclideanSpace ℝ (Fin N)) =
      chartPoint β e w x := fun x => congrFun hpt x
  have hwv : ∀ x, ‖w x‖ < Real.sqrt β := fun x => by simpa [w] using hv x
  have hJ := chartJac_eq_exp hβ w hwv
  have key := exp_eq_const_mul_prod_site (β := β) e a Hα hH g w (β * (ν - (if regimeB then ν else 0)) / 2) h
    (β * (energy d N (L * n) (if regimeB then ν else 0) h ec +
            (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
              ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2)) 0
  unfold baseSectorF
  simp only [hφ]
  simp only [add_zero] at key
  simp only [w, ec] at key hJ ⊢
  have hSig : Complex.exp (-(∑ x, chartSiteReal β e a (β * (ν - (if regimeB then ν else 0)) / 2) h g
        (fun x => (v x : EuclideanSpace ℝ (Fin N))) x)) =
      Complex.exp (((-(∑ x, (1 / 2) * Real.log (1 - ‖(v x : EuclideanSpace ℝ (Fin N))‖ ^ 2 / β)) : ℝ) : ℂ)) *
        (∏ x, Complex.exp
          ((((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
              ∑ i, g x i * ((((v x : EuclideanSpace ℝ (Fin N)) +
                chartShift β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) x) i : ℝ) : ℂ) -
            ((β * (ν - (if regimeB then ν else 0)) / 2 *
              ‖chartPoint β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) x - h‖ ^ 2 : ℝ) : ℂ))) *
        ∏ x, ∏ y, Complex.exp (-((a x y * (inner ℝ (v x : EuclideanSpace ℝ (Fin N))
            (chartShift β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) y) +
          (1 / 2) * inner ℝ (chartShift β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) x)
            (chartShift β e (fun x => (v x : EuclideanSpace ℝ (Fin N))) y)) : ℝ) : ℂ)) := by
    simp only [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    unfold chartSiteReal
    push_cast
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      neg_sub]
    ring
  rw [key, hJ, Complex.ofReal_exp, hSig]
  simp only [neg_zero, Complex.exp_zero, mul_one]
  ring

end Sector

end Balaban.LargeField
