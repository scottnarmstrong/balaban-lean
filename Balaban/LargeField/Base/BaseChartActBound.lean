/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActAlg
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# (AE1), the bound of the site exponent of the chart integrand

If the tangent vector `v` has components of modulus `≤ m` with `N m² ≤ β/4`, the background has
components of modulus `≤ E_e`, the rows of the Hessian have `ℓ¹` norm `≤ B_H` and the rows of the
source have `ℓ¹` norm `≤ G_g`, then `|V_x|` is bounded by an explicit expression of order
`B_H (m³ β^{-1/2} + m⁴ β^{-1}) + m² β^{-1} + G_g (m β^{-1/2} + m² β^{-1})` (`norm_chartSite_le`).
The tangent components are bounded by the whitened fluctuation (`norm_chartTangent_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Matrix

section Bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem norm_log_one_sub_le {t : ℂ} (h : ‖t‖ ≤ 1 / 2) : ‖Complex.log (1 - t)‖ ≤ 3 / 2 * ‖t‖ := by
  have := Complex.norm_log_one_add_half_le_self (z := -t) (by simpa using h)
  simpa [sub_eq_add_neg] using this

theorem norm_chartSqrt_sub_one_le {t : ℂ} (h : ‖t‖ ≤ 1 / 2) : ‖chartSqrt t - 1‖ ≤ 3 / 2 * ‖t‖ := by
  unfold chartSqrt
  have h1 := norm_log_one_sub_le h
  have h2 : ‖Complex.log (1 - t) / 2‖ ≤ 3 / 4 * ‖t‖ := by
    rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have h3 : ‖Complex.log (1 - t) / 2‖ ≤ 1 := by
    have := norm_nonneg t; linarith
  have := Complex.norm_exp_sub_one_le h3
  linarith

theorem norm_chartT_le {β : ℝ} (hβ : 0 < β) {v : ι × Fin N → ℂ} {m : ℝ} (x : ι)
    (hv : ∀ i, ‖v (x, i)‖ ≤ m) : ‖chartT β v x‖ ≤ N * m ^ 2 / β := by
  unfold chartT
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hβ.le]
  refine div_le_div_of_nonneg_right ?_ hβ.le
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖v (x, i) * v (x, i)‖ ≤ ∑ _i : Fin N, m ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, ← sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
    _ = N * m ^ 2 := by simp

theorem norm_chartZ_le {β : ℝ} (hβ : 0 < β) {e : ι → Fin N → ℂ} {v : ι × Fin N → ℂ} {τ Ee : ℝ}
    (y : ι) (i : Fin N) (hτ : ‖chartT β v y‖ ≤ τ) (hτ2 : τ ≤ 1 / 2) (he : ‖e y i‖ ≤ Ee) :
    ‖chartZ β e v (y, i)‖ ≤ Real.sqrt β * (3 / 2 * τ) * Ee := by
  unfold chartZ
  simp only []
  have ht2 : ‖chartT β v y‖ ≤ 1 / 2 := hτ.trans hτ2
  have h1 := norm_chartSqrt_sub_one_le ht2
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs := Real.sqrt_nonneg β
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hτ
  calc Real.sqrt β * ‖chartSqrt (chartT β v y) - 1‖ * ‖e y i‖
      ≤ Real.sqrt β * (3 / 2 * τ) * Ee := by
        gcongr
        linarith

theorem norm_chartTangent_le {e : ι → Fin N → ℂ} {w : ι × Fin N → ℂ} {Ee M : ℝ} (hE : 0 ≤ Ee)
    (he : ∀ y i, ‖e y i‖ ≤ Ee) (hw : ∀ y i, ‖w (y, i)‖ ≤ M) (x : ι) (i : Fin N) :
    ‖chartTangent e w (x, i)‖ ≤ (1 + N * Ee ^ 2) * M := by
  rw [chartTangent_apply]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hw x i)
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖e x i * ∑ j, e x j * w (x, j)‖ ≤ Ee * (N * (Ee * M)) := by
    rw [norm_mul]
    refine mul_le_mul (he x i) ?_ (norm_nonneg _) hE
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖e x j * w (x, j)‖ ≤ ∑ _j : Fin N, Ee * M := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          exact mul_le_mul (he x j) (hw x j) (norm_nonneg _) hE
      _ = N * (Ee * M) := by simp
  have := hw x i
  nlinarith

theorem norm_chartSite_le {β : ℝ} (hβ : 0 < β) {e : ι → Fin N → ℂ} {H : Matrix ι ι ℂ}
    {g w : ι × Fin N → ℂ} {Ee m τ BH Gg : ℝ} (hE : 0 ≤ Ee) (hm : 0 ≤ m)
    (he : ∀ y i, ‖e y i‖ ≤ Ee) (hv : ∀ y i, ‖chartTangent e w (y, i)‖ ≤ m)
    (hτ : (N : ℝ) * m ^ 2 / β ≤ τ) (hτ2 : τ ≤ 1 / 2) (x : ι)
    (hH : ∑ y, ‖H x y‖ ≤ BH) (hg : ∑ i, ‖g (x, i)‖ ≤ Gg) :
    ‖chartSite β e H g w x‖ ≤
      BH * (N * (m * (Real.sqrt β * (3 / 2 * τ) * Ee))) +
        1 / 2 * (BH * (N * ((Real.sqrt β * (3 / 2 * τ) * Ee) * (Real.sqrt β * (3 / 2 * τ) * Ee)))) +
        1 / 2 * (3 / 2 * τ) + (Real.sqrt β)⁻¹ * (Gg * (m + Real.sqrt β * (3 / 2 * τ) * Ee)) := by
  set ζ : ℝ := Real.sqrt β * (3 / 2 * τ) * Ee with hζ
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ
  have hζ0 : 0 ≤ ζ := by rw [hζ]; positivity
  set v := chartTangent e w with hvdef
  have hT : ∀ y, ‖chartT β v y‖ ≤ τ := fun y =>
    (norm_chartT_le hβ y fun i => hv y i).trans hτ
  have hz : ∀ y i, ‖chartZ β e v (y, i)‖ ≤ ζ := fun y i =>
    norm_chartZ_le hβ y i (hT y) hτ2 (he y i)
  unfold chartSite
  simp only []
  rw [← hvdef]
  refine (norm_sub_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ?_ ?_)) ?_)) ?_
  · -- first term
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y, ‖H x y * ∑ i, v (x, i) * chartZ β e v (y, i)‖
        ≤ ∑ y, ‖H x y‖ * (N * (m * ζ)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine (norm_sum_le _ _).trans ?_
          calc ∑ i, ‖v (x, i) * chartZ β e v (y, i)‖ ≤ ∑ _i : Fin N, m * ζ := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [norm_mul]
                exact mul_le_mul (hv x i) (hz y i) (norm_nonneg _) hm
            _ = N * (m * ζ) := by simp
      _ = (∑ y, ‖H x y‖) * (N * (m * ζ)) := by rw [Finset.sum_mul]
      _ ≤ BH * (N * (m * ζ)) := mul_le_mul_of_nonneg_right hH (by positivity)
  · -- second term
    rw [norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ y, ‖H x y * ∑ i, chartZ β e v (x, i) * chartZ β e v (y, i)‖
        ≤ ∑ y, ‖H x y‖ * (N * (ζ * ζ)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine (norm_sum_le _ _).trans ?_
          calc ∑ i, ‖chartZ β e v (x, i) * chartZ β e v (y, i)‖ ≤ ∑ _i : Fin N, ζ * ζ := by
                refine Finset.sum_le_sum fun i _ => ?_
                rw [norm_mul]
                exact mul_le_mul (hz x i) (hz y i) (norm_nonneg _) hζ0
            _ = N * (ζ * ζ) := by simp
      _ = (∑ y, ‖H x y‖) * (N * (ζ * ζ)) := by rw [Finset.sum_mul]
      _ ≤ BH * (N * (ζ * ζ)) := mul_le_mul_of_nonneg_right hH (by positivity)
  · -- the logarithm
    rw [norm_mul]
    have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h12]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact (norm_log_one_sub_le ((hT x).trans hτ2)).trans (by linarith [hT x])
  · -- the source
    rw [norm_mul]
    have hs : ‖((Real.sqrt β)⁻¹ : ℂ)‖ = (Real.sqrt β)⁻¹ := by
      rw [show ((Real.sqrt β)⁻¹ : ℂ) = (((Real.sqrt β)⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hs]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖g (x, i) * (v (x, i) + chartZ β e v (x, i))‖ ≤ ∑ i, ‖g (x, i)‖ * (m + ζ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hv x i) (hz x i)))
            (norm_nonneg _)
      _ = (∑ i, ‖g (x, i)‖) * (m + ζ) := by rw [Finset.sum_mul]
      _ ≤ Gg * (m + ζ) := mul_le_mul_of_nonneg_right hg (by positivity)

/-- The whitened fluctuation has components `≤ B_W p₁` if the rows of `W` have `ℓ¹` norm `≤ B_W` and
the components of `ψ'` are `≤ p₁`. -/
theorem norm_mulVec_le {W : Matrix (ι × Fin N) (ι × Fin N) ℂ} {ψ : ι × Fin N → ℂ} {BW p₁ : ℝ}
    (hW : ∀ p, ∑ r, ‖W p r‖ ≤ BW) (hψ : ∀ r, ‖ψ r‖ ≤ p₁) (p : ι × Fin N) :
    ‖(W *ᵥ ψ) p‖ ≤ BW * p₁ := by
  have h0 : 0 ≤ p₁ := (norm_nonneg _).trans (hψ p)
  simp only [Matrix.mulVec, dotProduct]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r, ‖W p r * ψ r‖ ≤ ∑ r, ‖W p r‖ * p₁ := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hψ r) (norm_nonneg _)
    _ = (∑ r, ‖W p r‖) * p₁ := by rw [Finset.sum_mul]
    _ ≤ BW * p₁ := mul_le_mul_of_nonneg_right (hW p) h0

/-- **(AE1), the bound for an abstract whitening family.**  If the rows of `W` have `ℓ¹` norm
`≤ B_W`, `|ψ'_r| ≤ p₁`, then with `m = (1 + N E_e²) B_W p₁` and `τ = N m²/β ≤ 1/2` the site exponent
obeys the bound of `norm_chartSite_le`. -/
theorem norm_chartSite_whitened_le {β : ℝ} (hβ : 0 < β) {e : ι → Fin N → ℂ} {H : Matrix ι ι ℂ}
    {g : ι × Fin N → ℂ} {W : Matrix (ι × Fin N) (ι × Fin N) ℂ} {ψ : ι × Fin N → ℂ}
    {Ee BW p₁ BH Gg : ℝ} (hE : 0 ≤ Ee) (hBW : 0 ≤ BW) (hp : 0 ≤ p₁)
    (he : ∀ y i, ‖e y i‖ ≤ Ee) (hW : ∀ p, ∑ r, ‖W p r‖ ≤ BW) (hψ : ∀ r, ‖ψ r‖ ≤ p₁)
    (hτ2 : (N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β ≤ 1 / 2) (x : ι)
    (hH : ∑ y, ‖H x y‖ ≤ BH) (hg : ∑ i, ‖g (x, i)‖ ≤ Gg) :
    ‖chartSite β e H g (W *ᵥ ψ) x‖ ≤
      BH * (N * (((1 + N * Ee ^ 2) * BW * p₁) * (Real.sqrt β *
        (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee))) +
      1 / 2 * (BH * (N * ((Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee) *
        (Real.sqrt β * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee)))) +
      1 / 2 * (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) +
      (Real.sqrt β)⁻¹ * (Gg * (((1 + N * Ee ^ 2) * BW * p₁) + Real.sqrt β *
        (3 / 2 * ((N : ℝ) * ((1 + N * Ee ^ 2) * BW * p₁) ^ 2 / β)) * Ee)) := by
  have hw : ∀ y i, ‖(W *ᵥ ψ) (y, i)‖ ≤ BW * p₁ := fun y i => norm_mulVec_le hW hψ (y, i)
  have hv := norm_chartTangent_le (e := e) hE he hw
  exact norm_chartSite_le hβ hE (by positivity) he
    (fun y i => by simpa [mul_assoc] using hv y i) le_rfl hτ2 x hH hg

end Bound

end Balaban.LargeField.Base
