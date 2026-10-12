/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Analysis.Cauchy
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Taylor remainders and Cauchy estimates for analytic functions on a ball

For `f : E → ℂ` analytic on the open ball `ball c ρ` of a complex Banach space and bounded there
by `M`, with the second derivative `D2 f c v w = (f'') (c) v w`:

* `norm_sub_taylor_le`: the one-variable Taylor tail on the unit disc inside a disc of radius `r > 1`;
* `taylor_first`, `taylor_second`: `‖f (c + z) - f c - f' z‖ ≤ 2 M (‖z‖/ρ)²` and the same with the
  second-order term and exponent `3`, for `‖z‖ ≤ ρ / 2`;
* `norm_fderiv_apply_le`, `norm_D2_le`: `‖f' v‖ ≤ M ‖v‖/ρ` and `‖f'' (v, w)‖ ≤ 4 M ‖v‖ ‖w‖/ρ²`;
* `D2_symm`: symmetry of the second derivative.
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.SmallField

section OneVariable

/-- Tail of the Taylor series of `g` on the unit disc, for `g` bounded by `M` on a disc of radius
`r > 1`. -/
theorem norm_sub_taylor_le (g : ℂ → ℂ) {r M : ℝ} (hr : 1 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hM : ∀ z ∈ ball (0 : ℂ) r, ‖g z‖ ≤ M) (k : ℕ) :
    ‖g 1 - ∑ n ∈ Finset.range k, ((n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0)‖ ≤
      M * (1 / r) ^ k / (1 - 1 / r) := by
  have hr0 : 0 < r := by linarith
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) r := by simpa using hr
  have hS := Complex.hasSum_taylorSeries_on_ball hg h1
  simp only [sub_zero, one_pow, smul_eq_mul, one_mul] at hS
  have hS' := (hasSum_nat_add_iff' k).mpr hS
  have hcoef : ∀ n : ℕ, ‖iteratedDeriv n g 0‖ ≤ n.factorial * M / r ^ n := by
    intro n
    have key : ∀ ρ, 0 < ρ → ρ < r → ‖iteratedDeriv n g 0‖ * ρ ^ n ≤ n.factorial * M := by
      intro ρ hρ hρr
      have hcl : DiffContOnCl ℂ g (ball (0 : ℂ) ρ) := by
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball _ hρ.ne']
        exact hg.mono (closedBall_subset_ball hρr)
      have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hcl
        (C := M) (fun z hz => hM z (by
          rw [mem_sphere_zero_iff_norm] at hz
          rw [mem_ball_zero_iff]; linarith))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have := Balaban.Analysis.mul_pow_le_of_forall_lt (a := ‖iteratedDeriv n g 0‖)
      (b := n.factorial * M) n hr0 key
    rwa [le_div_iff₀ (by positivity)]
  have hgeo : HasSum (fun n : ℕ => M * (1 / r) ^ (n + k))
      (M * (1 / r) ^ k / (1 - 1 / r)) := by
    have h0 : 0 ≤ 1 / r := by positivity
    have h1' : 1 / r < 1 := by rw [div_lt_one hr0]; exact hr
    have := (hasSum_geometric_of_lt_one h0 h1').mul_left (M * (1 / r) ^ k)
    convert this using 1
    · ext n; ring
    · field_simp
  refine HasSum.norm_le_of_bounded hS' hgeo (fun n => ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have := hcoef (n + k)
  have hf : (0 : ℝ) < ((n + k).factorial : ℝ) := by positivity
  calc (((n + k).factorial : ℝ))⁻¹ * ‖iteratedDeriv (n + k) g 0‖
      ≤ (((n + k).factorial : ℝ))⁻¹ * (((n + k).factorial : ℝ) * M / r ^ (n + k)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = M * (1 / r) ^ (n + k) := by
        rw [one_div, inv_pow]
        field_simp

end OneVariable

section Ball

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The second derivative `f''(c)(v, w)`: the derivative of `x ↦ f'(x)` in the direction `v`,
applied to `w`. -/
noncomputable def D2 (f : E → ℂ) (c v w : E) : ℂ := fderiv ℂ (fderiv ℂ f) c v w

theorem D2_add_left (f : E → ℂ) (c v v' w : E) : D2 f c (v + v') w = D2 f c v w + D2 f c v' w := by
  simp [D2]

theorem D2_sub_left (f : E → ℂ) (c v v' w : E) : D2 f c (v - v') w = D2 f c v w - D2 f c v' w := by
  simp [D2]

theorem D2_smul_left (f : E → ℂ) (c : E) (t : ℂ) (v w : E) : D2 f c (t • v) w = t * D2 f c v w := by
  simp [D2]

theorem D2_add_right (f : E → ℂ) (c v w w' : E) : D2 f c v (w + w') = D2 f c v w + D2 f c v w' := by
  simp [D2]

theorem D2_sub_right (f : E → ℂ) (c v w w' : E) : D2 f c v (w - w') = D2 f c v w - D2 f c v w' := by
  simp [D2]

theorem D2_smul_right (f : E → ℂ) (c : E) (t : ℂ) (v w : E) : D2 f c v (t • w) = t * D2 f c v w := by
  simp [D2]

theorem D2_zero_left (f : E → ℂ) (c w : E) : D2 f c 0 w = 0 := by simp [D2]

theorem D2_zero_right (f : E → ℂ) (c v : E) : D2 f c v 0 = 0 := by simp [D2]

theorem D2_symm {f : E → ℂ} {c : E} (hf : AnalyticAt ℂ f c) (v w : E) :
    D2 f c v w = D2 f c w v :=
  (hf.contDiffAt.isSymmSndFDerivAt_of_omega) v w

/-- The line derivative of `f` at a point where `f` is differentiable. -/
theorem hasDerivAt_line {f : E → ℂ} {c z : E} {τ : ℂ} (hf : DifferentiableAt ℂ f (c + τ • z)) :
    HasDerivAt (fun t : ℂ => f (c + t • z)) (fderiv ℂ f (c + τ • z) z) τ := by
  have h1 : HasDerivAt (fun t : ℂ => c + t • z) z τ := by
    simpa using ((hasDerivAt_id τ).smul_const z).const_add c
  exact hf.hasFDerivAt.comp_hasDerivAt τ h1

theorem iteratedDeriv_one_line {f : E → ℂ} {c z : E} (hf : DifferentiableAt ℂ f c) :
    iteratedDeriv 1 (fun t : ℂ => f (c + t • z)) 0 = fderiv ℂ f c z := by
  rw [iteratedDeriv_one]
  have := hasDerivAt_line (f := f) (c := c) (z := z) (τ := 0) (by simpa using hf)
  simpa using this.deriv

theorem iteratedDeriv_two_line {f : E → ℂ} {c z : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) :
    iteratedDeriv 2 (fun t : ℂ => f (c + t • z)) 0 = D2 f c z z := by
  have hc : c ∈ ball c ρ := mem_ball_self hρ
  have hopen : IsOpen (ball c ρ) := isOpen_ball
  -- the derivative of the line function near 0
  have hev : (deriv fun t : ℂ => f (c + t • z)) =ᶠ[𝓝 0] fun t : ℂ => fderiv ℂ f (c + t • z) z := by
    have hcont : ContinuousAt (fun t : ℂ => c + t • z) 0 := by fun_prop
    have hmem : (fun t : ℂ => c + t • z) ⁻¹' ball c ρ ∈ 𝓝 (0 : ℂ) :=
      hcont.preimage_mem_nhds (by simpa using hopen.mem_nhds hc)
    filter_upwards [hmem] with t ht
    exact (hasDerivAt_line (hf _ ht).differentiableAt).deriv
  have hfd : DifferentiableAt ℂ (fderiv ℂ f) c := (hf.fderiv_of_isOpen hopen c hc).differentiableAt
  have h1 : HasDerivAt (fun t : ℂ => c + t • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const z).const_add c
  have h2 : HasDerivAt (fun t : ℂ => fderiv ℂ f (c + t • z)) (fderiv ℂ (fderiv ℂ f) c z) 0 := by
    have hfd' : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) c)
        ((fun t : ℂ => c + t • z) 0) := by simpa using hfd.hasFDerivAt
    exact hfd'.comp_hasDerivAt (0 : ℂ) h1
  have h3 : HasDerivAt (fun t : ℂ => fderiv ℂ f (c + t • z) z) (fderiv ℂ (fderiv ℂ f) c z z) 0 :=
    h2.clm_apply (hasDerivAt_const (0 : ℂ) z) |>.congr_deriv (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [Filter.EventuallyEq.deriv_eq hev]
  exact h3.deriv

/-- The line function of an analytic function on a ball, as a function on a disc. -/
theorem line_diffOn {f : E → ℂ} {c : E} {ρ : ℝ} (hf : AnalyticOnNhd ℂ f (ball c ρ)) {z : E}
    {r : ℝ} (hz : z ≠ 0) (hr : r = ρ / ‖z‖) :
    DifferentiableOn ℂ (fun t : ℂ => f (c + t • z)) (ball 0 r) := by
  intro t ht
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hmem : c + t • z ∈ ball c ρ := by
    rw [mem_ball, dist_eq_norm]
    have : ‖t‖ < r := by simpa using ht
    rw [hr, lt_div_iff₀ hzn] at this
    simpa [norm_smul] using this
  have h1 : DifferentiableAt ℂ (fun t : ℂ => c + t • z) t := by fun_prop
  exact ((hf _ hmem).differentiableAt.comp t h1).differentiableWithinAt

theorem line_bdd {f : E → ℂ} {c : E} {ρ M : ℝ} (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M) {z : E}
    {r : ℝ} (hz : z ≠ 0) (hr : r = ρ / ‖z‖) :
    ∀ t ∈ ball (0 : ℂ) r, ‖f (c + t • z)‖ ≤ M := by
  intro t ht
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  apply hM
  rw [mem_ball, dist_eq_norm]
  have : ‖t‖ < r := by simpa using ht
  rw [hr, lt_div_iff₀ hzn] at this
  simpa [norm_smul] using this

/-- First-order Taylor remainder: `‖f (c + z) - f c - f'(c) z‖ ≤ 2 M (‖z‖/ρ)²` for `‖z‖ ≤ ρ/2`. -/
theorem taylor_first {f : E → ℂ} {c : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M) {z : E}
    (hz : ‖z‖ ≤ ρ / 2) :
    ‖f (c + z) - f c - fderiv ℂ f c z‖ ≤ 2 * M * (‖z‖ / ρ) ^ 2 := by
  by_cases hz0 : z = 0
  · subst hz0
    have : f c = f c := rfl
    simp
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set r := ρ / ‖z‖ with hr
  have hr2 : 2 ≤ r := by rw [hr, le_div_iff₀ hzn]; linarith
  have hc : c ∈ ball c ρ := mem_ball_self hρ
  have key := norm_sub_taylor_le (fun t : ℂ => f (c + t • z)) (r := r) (M := M) (by linarith)
    (line_diffOn hf hz0 hr) (line_bdd hM hz0 hr) 2
  have hsum : ∑ n ∈ Finset.range 2, (((n.factorial : ℕ) : ℂ)⁻¹ *
      iteratedDeriv n (fun t : ℂ => f (c + t • z)) 0) = f c + fderiv ℂ f c z := by
    simp [Finset.sum_range_succ, iteratedDeriv_one_line (hf c hc).differentiableAt]
  rw [hsum] at key
  have hq : 1 / r = ‖z‖ / ρ := by rw [hr]; field_simp
  rw [hq] at key
  have hq2 : ‖z‖ / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ]; linarith
  have hq0 : 0 ≤ ‖z‖ / ρ := by positivity
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c hc)
  simp only [one_smul] at key
  calc ‖f (c + z) - f c - fderiv ℂ f c z‖ = ‖f (c + (1:ℂ) • z) - (f c + fderiv ℂ f c z)‖ := by
        simp only [one_smul]; ring_nf
    _ ≤ M * (‖z‖ / ρ) ^ 2 / (1 - ‖z‖ / ρ) := by simpa using key
    _ ≤ 2 * M * (‖z‖ / ρ) ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hM0 (sq_nonneg (‖z‖ / ρ)), mul_nonneg (mul_nonneg hM0 (sq_nonneg (‖z‖ / ρ))) hq0]

/-- Second-order Taylor remainder:
`‖f (c + z) - f c - f'(c) z - ½ f''(c)(z,z)‖ ≤ 2 M (‖z‖/ρ)³` for `‖z‖ ≤ ρ/2`. -/
theorem taylor_second {f : E → ℂ} {c : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M) {z : E}
    (hz : ‖z‖ ≤ ρ / 2) :
    ‖f (c + z) - f c - fderiv ℂ f c z - (1 / 2 : ℂ) * D2 f c z z‖ ≤ 2 * M * (‖z‖ / ρ) ^ 3 := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [D2_zero_left]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  set r := ρ / ‖z‖ with hr
  have hr2 : 2 ≤ r := by rw [hr, le_div_iff₀ hzn]; linarith
  have hc : c ∈ ball c ρ := mem_ball_self hρ
  have key := norm_sub_taylor_le (fun t : ℂ => f (c + t • z)) (r := r) (M := M) (by linarith)
    (line_diffOn hf hz0 hr) (line_bdd hM hz0 hr) 3
  have hsum : ∑ n ∈ Finset.range 3, (((n.factorial : ℕ) : ℂ)⁻¹ *
      iteratedDeriv n (fun t : ℂ => f (c + t • z)) 0) =
      f c + fderiv ℂ f c z + (1 / 2 : ℂ) * D2 f c z z := by
    simp [Finset.sum_range_succ, iteratedDeriv_one_line (hf c hc).differentiableAt,
      iteratedDeriv_two_line hρ hf, Nat.factorial]
  rw [hsum] at key
  have hq : 1 / r = ‖z‖ / ρ := by rw [hr]; field_simp
  rw [hq] at key
  have hq2 : ‖z‖ / ρ ≤ 1 / 2 := by rw [div_le_iff₀ hρ]; linarith
  have hq0 : 0 ≤ ‖z‖ / ρ := by positivity
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c hc)
  simp only [one_smul] at key
  calc ‖f (c + z) - f c - fderiv ℂ f c z - (1 / 2 : ℂ) * D2 f c z z‖
      = ‖f (c + (1:ℂ) • z) - (f c + fderiv ℂ f c z + (1 / 2 : ℂ) * D2 f c z z)‖ := by
        simp only [one_smul]; ring_nf
    _ ≤ M * (‖z‖ / ρ) ^ 3 / (1 - ‖z‖ / ρ) := by simpa using key
    _ ≤ 2 * M * (‖z‖ / ρ) ^ 3 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg hM0 (pow_nonneg hq0 3), mul_nonneg (mul_nonneg hM0 (pow_nonneg hq0 3)) hq0]

/-- Cauchy estimate for the first derivative at the centre. -/
theorem norm_fderiv_apply_le {f : E → ℂ} {c : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M) (v : E) :
    ‖fderiv ℂ f c v‖ ≤ M * ‖v‖ / ρ := by
  have h := Balaban.Analysis.norm_fderiv_le_of_ball hf.differentiableOn hM (mem_ball_self hρ)
  simp only [dist_self, sub_zero] at h
  calc ‖fderiv ℂ f c v‖ ≤ ‖fderiv ℂ f c‖ * ‖v‖ := (fderiv ℂ f c).le_opNorm v
    _ ≤ M / ρ * ‖v‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = M * ‖v‖ / ρ := by ring

/-- Cauchy estimate for the diagonal second derivative at the centre. -/
theorem norm_D2_diag_le {f : E → ℂ} {c : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M) (v : E) :
    ‖D2 f c v v‖ ≤ 2 * M * ‖v‖ ^ 2 / ρ ^ 2 := by
  have h := Balaban.Analysis.norm_iteratedDeriv_line_le (f := f) (z₀ := c) hρ hf.differentiableOn hM v 2
  rw [iteratedDeriv_two_line hρ hf] at h
  simpa [Nat.factorial, mul_comm, mul_assoc, mul_left_comm] using h

/-- Cauchy estimate for the second derivative at the centre. -/
theorem norm_D2_le {f : E → ℂ} {c : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (hM : ∀ x ∈ ball c ρ, ‖f x‖ ≤ M) (v w : E) :
    ‖D2 f c v w‖ ≤ 4 * M * ‖v‖ * ‖w‖ / ρ ^ 2 := by
  have hc : AnalyticAt ℂ f c := hf c (mem_ball_self hρ)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM c (mem_ball_self hρ))
  by_cases hv : v = 0
  · subst hv; simp [D2_zero_left]
  by_cases hw : w = 0
  · subst hw; simp [D2_zero_right]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  -- normalised vectors
  set v' : E := ((‖v‖ : ℂ))⁻¹ • v with hv'
  set w' : E := ((‖w‖ : ℂ))⁻¹ • w with hw'
  have hv'n : ‖v'‖ = 1 := by
    rw [hv', norm_smul]; simp [hvn.ne']
  have hw'n : ‖w'‖ = 1 := by
    rw [hw', norm_smul]; simp [hwn.ne']
  have hpol : D2 f c (v' + w') (v' + w') - D2 f c (v' - w') (v' - w') = 4 * D2 f c v' w' := by
    simp only [D2_add_left, D2_add_right, D2_sub_left, D2_sub_right, D2_symm hc w' v']
    ring
  have h1 := norm_D2_diag_le hρ hf hM (v' + w')
  have h2 := norm_D2_diag_le hρ hf hM (v' - w')
  have h3 : ‖v' + w'‖ ≤ 2 := by
    calc ‖v' + w'‖ ≤ ‖v'‖ + ‖w'‖ := norm_add_le _ _
      _ = 2 := by rw [hv'n, hw'n]; norm_num
  have h4 : ‖v' - w'‖ ≤ 2 := by
    calc ‖v' - w'‖ ≤ ‖v'‖ + ‖w'‖ := norm_sub_le _ _
      _ = 2 := by rw [hv'n, hw'n]; norm_num
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hsq1 : ‖v' + w'‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (v' + w')]
  have hsq2 : ‖v' - w'‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (v' - w')]
  have hb1 : ‖D2 f c (v' + w') (v' + w')‖ ≤ 8 * M / ρ ^ 2 := by
    refine h1.trans ?_
    rw [div_le_div_iff_of_pos_right hρ2]; nlinarith
  have hb2 : ‖D2 f c (v' - w') (v' - w')‖ ≤ 8 * M / ρ ^ 2 := by
    refine h2.trans ?_
    rw [div_le_div_iff_of_pos_right hρ2]; nlinarith
  have hD : ‖D2 f c v' w'‖ ≤ 4 * M / ρ ^ 2 := by
    have : ‖(4 : ℂ) * D2 f c v' w'‖ ≤ 16 * M / ρ ^ 2 := by
      rw [← hpol]
      calc _ ≤ ‖D2 f c (v' + w') (v' + w')‖ + ‖D2 f c (v' - w') (v' - w')‖ := norm_sub_le _ _
        _ ≤ 8 * M / ρ ^ 2 + 8 * M / ρ ^ 2 := add_le_add hb1 hb2
        _ = 16 * M / ρ ^ 2 := by ring
    rw [norm_mul] at this
    have h4' : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h4'] at this
    have h16 : 16 * M / ρ ^ 2 = 4 * (4 * M / ρ ^ 2) := by ring
    rw [h16] at this
    linarith
  have hscale : D2 f c v w = ((‖v‖ : ℂ) * ‖w‖) * D2 f c v' w' := by
    rw [hv', hw', D2_smul_left, D2_smul_right]
    have hv0 : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hvn.ne'
    have hw0 : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwn.ne'
    field_simp
  rw [hscale, norm_mul, norm_mul]
  simp only [Complex.norm_real, norm_norm]
  calc ‖v‖ * ‖w‖ * ‖D2 f c v' w'‖ ≤ ‖v‖ * ‖w‖ * (4 * M / ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 4 * M * ‖v‖ * ‖w‖ / ρ ^ 2 := by ring

end Ball

end Balaban.SmallField
