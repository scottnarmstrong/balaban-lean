/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The Schwarz-type bound for a second-order function (S2 of RENORM-RELEVANT)

If `c` is analytic on the closed ball of radius `r` of a complex normed space, bounded by `M`, and
vanishes together with its derivative at `0`, then `‖c(ξ)‖ ≤ (M/r²) ‖ξ‖²` on the ball
(`norm_le_of_second_order`): restrict to the complex line through `ξ`, divide twice by the variable
(`dslope`) and apply the maximum modulus principle on the unit disc.
-/

@[expose] public section

namespace Balaban.SmallField

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [CompleteSpace F]

/-- **Schwarz-type bound.** -/
theorem norm_le_of_second_order {c : E → F} {r M : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ c (closedBall 0 r)) (hM : ∀ ξ ∈ closedBall (0 : E) r, ‖c ξ‖ ≤ M)
    (h0 : c 0 = 0) (hD : fderiv ℂ c 0 = 0) :
    ∀ ξ ∈ closedBall (0 : E) r, ‖c ξ‖ ≤ M / r ^ 2 * ‖ξ‖ ^ 2 := by
  intro ξ hξ
  by_cases hξ0 : ξ = 0
  · subst hξ0; simp [h0]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ0
  have hξr : ‖ξ‖ ≤ r := by simpa using hξ
  set u : E := (r / ‖ξ‖ : ℝ) • ξ with hu
  have hun : ‖u‖ = r := by
    rw [hu, norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp
  -- the function on the complex line
  set g : ℂ → F := fun t => c (t • u) with hg
  have hmem : ∀ t : ℂ, ‖t‖ ≤ 1 → t • u ∈ closedBall (0 : E) r := fun t ht => by
    rw [mem_closedBall, dist_zero_right, norm_smul, hun]
    nlinarith
  have hlinD : Differentiable ℂ (fun t : ℂ => t • u) := by fun_prop
  have hgd : DifferentiableOn ℂ g (closedBall 0 1) :=
    hd.comp hlinD.differentiableOn (fun t ht => hmem t (by simpa using ht))
  have hg0 : g 0 = 0 := by simp [hg, h0]
  have hcAt : DifferentiableAt ℂ c 0 := hd.differentiableAt (closedBall_mem_nhds 0 hr)
  have hline : HasDerivAt (fun t : ℂ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).smul_const u
  have hg' : deriv g 0 = 0 := by
    have h1 : HasFDerivAt c (fderiv ℂ c 0) ((fun t : ℂ => t • u) 0) := by
      simpa using hcAt.hasFDerivAt
    have := (h1.comp_hasDerivAt (0 : ℂ) hline).deriv
    simpa [hg, hD, Function.comp_def] using this
  have hball : closedBall (0 : ℂ) 1 ∈ nhds (0 : ℂ) := closedBall_mem_nhds 0 one_pos
  set k1 : ℂ → F := dslope g 0 with hk1
  set k : ℂ → F := dslope k1 0 with hk
  have hk1d : DifferentiableOn ℂ k1 (closedBall 0 1) := (Complex.differentiableOn_dslope hball).2 hgd
  have hkd : DifferentiableOn ℂ k (closedBall 0 1) := (Complex.differentiableOn_dslope hball).2 hk1d
  have hk10 : k1 0 = 0 := by rw [hk1, dslope_same]; exact hg'
  have hgk : ∀ t : ℂ, t ≠ 0 → g t = (t ^ 2) • k t := by
    intro t ht
    have e1 : k1 t = t⁻¹ • g t := by
      rw [hk1, dslope_of_ne _ ht, slope_def_module]; simp [hg0]
    have e2 : k t = t⁻¹ • k1 t := by
      rw [hk, dslope_of_ne _ ht, slope_def_module]; simp [hk10]
    rw [e2, e1, smul_smul, smul_smul]
    have : t ^ 2 * t⁻¹ * t⁻¹ = 1 := by field_simp
    rw [this, one_smul]
  have hkb : ∀ z ∈ closedBall (0 : ℂ) 1, ‖k z‖ ≤ M := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) 1)
      Metric.isBounded_ball (DifferentiableOn.diffContOnCl (by rw [closure_ball _ one_ne_zero]; exact hkd)) (fun w hw => ?_) (by rw [closure_ball _ one_ne_zero]; exact hz)
    rw [frontier_ball _ one_ne_zero] at hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw1; simp at hw1
    have := hgk w hw0
    have hnk : ‖k w‖ = ‖g w‖ := by
      rw [this, norm_smul, norm_pow, hw1]; simp
    rw [hnk]
    exact hM _ (hmem w hw1.le)
  set l0 : ℝ := ‖ξ‖ / r with hl0
  have hl0n : ‖(l0 : ℂ)‖ = l0 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hl01 : ‖(l0 : ℂ)‖ ≤ 1 := by rw [hl0n, hl0, div_le_one hr]; exact hξr
  have hl0ne : (l0 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  have hlu : (l0 : ℂ) • u = ξ := by
    rw [Complex.coe_smul, hu, smul_smul]
    have : l0 * (r / ‖ξ‖) = 1 := by rw [hl0]; field_simp
    rw [this, one_smul]
  have hkl := hkb (l0 : ℂ) (by simpa using hl01)
  have hgl : c ξ = g (l0 : ℂ) := by simp [hg, hlu]
  rw [hgl, hgk _ hl0ne, norm_smul, norm_pow, hl0n]
  calc l0 ^ 2 * ‖k (l0 : ℂ)‖ ≤ l0 ^ 2 * M := mul_le_mul_of_nonneg_left hkl (by positivity)
    _ = M / r ^ 2 * ‖ξ‖ ^ 2 := by rw [hl0]; field_simp

