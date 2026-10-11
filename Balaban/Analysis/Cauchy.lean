/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic


/-!
# Cauchy estimates in finite dimension

For `f : E → F` (`E` a complex normed space, `F` a complex normed space) differentiable on the
ball `ball z₀ R` and bounded there by `M`, reduced to one variable along complex lines
`l ↦ f (w + l • v)` and Mathlib's `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`:

* `norm_fderiv_le_of_ball`: `‖Df w‖ ≤ M / (R - ‖w - z₀‖)`;
* `norm_sub_le_of_ball`: `‖f z - f z₀‖ ≤ M ‖z - z₀‖ / (R - ‖z - z₀‖)`;
* `norm_le_of_eq_zero_of_ball`: if `f z₀ = 0` then `‖f z‖ ≤ 2 M ‖z - z₀‖ / R` for
  `‖z - z₀‖ ≤ R / 2`;
* `norm_iteratedDeriv_line_le`: Taylor coefficients along a direction `v`;
* on polydiscs `polydisc c r` (polyradius `r : ι → ℝ`): `norm_fderiv_single_le` and the mixed
  derivative bound `norm_mixed_fderiv_le`, `‖∂_j ∂_i f (c)‖ ≤ M / (r_i r_j)` for `i ≠ j`.

The sup norm on `ι → ℂ` is the case `E = ι → ℂ`.  No finite-dimensionality is needed for the
ball estimates.
-/

@[expose] public section

open Metric Set Filter Topology

namespace Balaban.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- One-variable Cauchy estimate along a complex line: if `f` is differentiable at `w + λ v`
and bounded by `M` for `‖λ‖ < ρ`, then `‖Df(w) v‖ ≤ M / ρ`. -/
theorem norm_fderiv_line_le {f : E → F} {w v : E} {ρ M : ℝ} (hρ : 0 < ρ)
    (hd : ∀ l : ℂ, ‖l‖ < ρ → DifferentiableAt ℂ f (w + l • v))
    (hb : ∀ l : ℂ, ‖l‖ < ρ → ‖f (w + l • v)‖ ≤ M) :
    ‖fderiv ℂ f w v‖ ≤ M / ρ := by
  set D := ‖fderiv ℂ f w v‖ with hD
  have key : ∀ r, 0 < r → r < ρ → D * r ≤ M := by
    intro r hr hrρ
    set g : ℂ → F := fun l => f (w + l • v) with hg
    have hgd : ∀ l : ℂ, ‖l‖ < ρ → DifferentiableAt ℂ g l := by
      intro l hl
      have h1 : HasDerivAt (fun l : ℂ => w + l • v) v l := by
        simpa using ((hasDerivAt_id l).smul_const v).const_add w
      exact (hd l hl).comp l h1.differentiableAt
    have hcl : DiffContOnCl ℂ g (ball (0 : ℂ) r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hr.ne']
      intro l hl
      exact (hgd l (lt_of_le_of_lt (by simpa using hl) hrρ)).differentiableWithinAt
    have hsph : ∀ l ∈ sphere (0 : ℂ) r, ‖g l‖ ≤ M := by
      intro l hl
      exact hb l (by rw [mem_sphere_zero_iff_norm.mp hl]; exact hrρ)
    have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hcl hsph
    have h2 : deriv g 0 = fderiv ℂ f w v := by
      have h1 : HasDerivAt (fun l : ℂ => w + l • v) v 0 := by
        simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add w
      have h3 : HasFDerivAt f (fderiv ℂ f w) (w + (0:ℂ) • v) := by
        simpa using (hd 0 (by simpa using hρ)).hasFDerivAt
      have := h3.comp_hasDerivAt (0:ℂ) h1
      exact this.deriv
    rw [h2] at h1
    rw [le_div_iff₀ hr] at h1
    exact h1
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hb 0 (by simpa using hρ))
  rw [le_div_iff₀ hρ]
  have ht : Tendsto (fun r : ℝ => D * r) (𝓝[<] ρ) (𝓝 (D * ρ)) :=
    ((continuous_const.mul continuous_id).tendsto ρ).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hρ] with r hr
  by_cases h0 : 0 < r
  · exact key r h0 hr.2
  · have : D * r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (not_lt.mp h0)
    linarith

/-- Derivative bound on a ball: `‖Df(w)‖ ≤ M / (R - ‖w - z₀‖)`. -/
theorem norm_fderiv_le_of_ball {f : E → F} {z₀ : E} {R M : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M)
    {w : E} (hw : w ∈ ball z₀ R) :
    ‖fderiv ℂ f w‖ ≤ M / (R - dist w z₀) := by
  have hρ : 0 < R - dist w z₀ := by rw [mem_ball] at hw; linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM w hw)
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hM0 hρ.le) fun v => ?_
  by_cases hv : v = 0
  · simp [hv]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmem : ∀ l : ℂ, ‖l‖ < (R - dist w z₀) / ‖v‖ → w + l • v ∈ ball z₀ R := by
    intro l hl
    rw [mem_ball]
    have h1 : ‖l‖ * ‖v‖ < R - dist w z₀ := by rwa [lt_div_iff₀ hvn] at hl
    calc dist (w + l • v) z₀ ≤ dist (w + l • v) w + dist w z₀ := dist_triangle _ _ _
      _ = ‖l‖ * ‖v‖ + dist w z₀ := by rw [dist_eq_norm]; simp [norm_smul]
      _ < R := by linarith
  have := norm_fderiv_line_le (f := f) (w := w) (v := v) (ρ := (R - dist w z₀) / ‖v‖) (M := M)
    (div_pos hρ hvn)
    (fun l hl => (hf.differentiableAt (isOpen_ball.mem_nhds (hmem l hl))))
    (fun l hl => hM _ (hmem l hl))
  calc ‖fderiv ℂ f w v‖ ≤ M / ((R - dist w z₀) / ‖v‖) := this
    _ = M / (R - dist w z₀) * ‖v‖ := by field_simp

/-- Cauchy estimate for increments on a ball. -/
theorem norm_sub_le_of_ball {f : E → F} {z₀ : E} {R M : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M)
    {z : E} (hz : z ∈ ball z₀ R) :
    ‖f z - f z₀‖ ≤ M * dist z z₀ / (R - dist z z₀) := by
  set t := dist z z₀ with ht
  have hR : 0 < R - t := by rw [mem_ball] at hz; linarith
  have hz0 : z₀ ∈ ball z₀ R := mem_ball_self (by linarith [dist_nonneg (x := z) (y := z₀)])
  have hsub : closedBall z₀ t ⊆ ball z₀ R := closedBall_subset_ball (by rw [mem_ball] at hz; exact hz)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (s := closedBall z₀ t)
    (C := M / (R - t))
    (fun x hx => hf.differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
    (fun x hx => by
      refine (norm_fderiv_le_of_ball hf hM (hsub hx)).trans ?_
      have hxt : dist x z₀ ≤ t := mem_closedBall.mp hx
      have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ hz0)
      exact div_le_div_of_nonneg_left hM0 hR (by linarith))
    (convex_closedBall _ _) (x := z₀) (y := z) (mem_closedBall_self dist_nonneg) (mem_closedBall.mpr le_rfl)
  calc ‖f z - f z₀‖ ≤ M / (R - t) * ‖z - z₀‖ := this
    _ = M * t / (R - t) := by rw [← dist_eq_norm, ← ht]; ring

/-- First-order vanishing: if `f z₀ = 0` then `‖f z‖ ≤ 2 M ‖z - z₀‖ / R` for `‖z - z₀‖ ≤ R/2`. -/
theorem norm_le_of_eq_zero_of_ball {f : E → F} {z₀ : E} {R M : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M)
    (h0 : f z₀ = 0) {z : E} (hz : dist z z₀ ≤ R / 2) (hR : 0 < R) :
    ‖f z‖ ≤ 2 * M * dist z z₀ / R := by
  have hzb : z ∈ ball z₀ R := by rw [mem_ball]; linarith
  have h := norm_sub_le_of_ball hf hM hzb
  rw [h0, sub_zero] at h
  refine h.trans ?_
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM z₀ (mem_ball_self hR))
  have ht0 : 0 ≤ dist z z₀ := dist_nonneg
  rw [div_le_div_iff₀ (by linarith) hR]
  nlinarith [mul_nonneg hM0 ht0]


/-- Limit in the radius: if `a * r ^ n ≤ b` for all `0 < r < ρ` then `a * ρ ^ n ≤ b`. -/
theorem mul_pow_le_of_forall_lt {a b ρ : ℝ} (n : ℕ) (hρ : 0 < ρ)
    (h : ∀ r, 0 < r → r < ρ → a * r ^ n ≤ b) : a * ρ ^ n ≤ b := by
  have ht : Tendsto (fun r : ℝ => a * r ^ n) (𝓝[<] ρ) (𝓝 (a * ρ ^ n)) :=
    ((continuous_const.mul (continuous_id.pow n)).tendsto ρ).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hρ] with r hr
  exact h r hr.1 hr.2

/-- Taylor coefficient along a direction: `‖(d/dλ)^n f(z₀ + λ v)|₀‖ ≤ n! M ‖v‖^n / R^n`. -/
theorem norm_iteratedDeriv_line_le [CompleteSpace F] {f : E → F} {z₀ : E} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hM : ∀ z ∈ ball z₀ R, ‖f z‖ ≤ M) (v : E) (n : ℕ) :
    ‖iteratedDeriv n (fun l : ℂ => f (z₀ + l • v)) 0‖ ≤ n.factorial * M * ‖v‖ ^ n / R ^ n := by
  by_cases hv : v = 0
  · subst hv
    by_cases hn : n = 0
    · subst hn
      have := hM z₀ (mem_ball_self hR)
      simpa using this
    · have : iteratedDeriv n (fun l : ℂ => f (z₀ + l • (0 : E))) 0 = 0 := by
        simp only [smul_zero, add_zero]
        rw [iteratedDeriv_const]; simp [hn]
      rw [this]; simp [hn]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hmem : ∀ l : ℂ, ‖l‖ * ‖v‖ < R → z₀ + l • v ∈ ball z₀ R := by
    intro l hl
    rw [mem_ball, dist_eq_norm]; simpa [norm_smul] using hl
  have key : ∀ r, 0 < r → r < R / ‖v‖ →
      ‖iteratedDeriv n (fun l : ℂ => f (z₀ + l • v)) 0‖ * r ^ n ≤ n.factorial * M := by
    intro r hr hrR
    have hrv : r * ‖v‖ < R := by rwa [lt_div_iff₀ hvn] at hrR
    set g : ℂ → F := fun l => f (z₀ + l • v)
    have hgd : DifferentiableOn ℂ g (closedBall 0 r) := by
      intro l hl
      have hl' : ‖l‖ * ‖v‖ < R :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by simpa using hl) hvn.le) hrv
      have h1 : DifferentiableAt ℂ (fun l : ℂ => z₀ + l • v) l := by fun_prop
      exact ((hf.differentiableAt (isOpen_ball.mem_nhds (hmem l hl'))).comp l h1).differentiableWithinAt
    have hcl : DiffContOnCl ℂ g (ball (0:ℂ) r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rwa [closure_ball _ hr.ne']
    have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hcl
      (C := M) (fun l hl => hM _ (hmem l (by
        rw [mem_sphere_zero_iff_norm.mp hl]; exact hrv)))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have := mul_pow_le_of_forall_lt n (div_pos hR hvn) key
  rw [div_pow] at this
  rw [le_div_iff₀ (by positivity)]
  have h2 : 0 < ‖v‖ ^ n := by positivity
  have h3 := mul_le_mul_of_nonneg_right this h2.le
  calc ‖iteratedDeriv n (fun l : ℂ => f (z₀ + l • v)) 0‖ * R ^ n
      = ‖iteratedDeriv n (fun l : ℂ => f (z₀ + l • v)) 0‖ * (R ^ n / ‖v‖ ^ n) * ‖v‖ ^ n := by
        field_simp
    _ ≤ _ := h3
    _ = _ := by ring


section Polydisc

variable {ι : Type*}

/-- The open polydisc with centre `c` and polyradius `r`. -/
def polydisc (c : ι → ℂ) (r : ι → ℝ) : Set (ι → ℂ) := {z | ∀ i, ‖z i - c i‖ < r i}

theorem isOpen_polydisc [Finite ι] (c : ι → ℂ) (r : ι → ℝ) : IsOpen (polydisc c r) := by
  have : polydisc c r = Set.pi Set.univ (fun j => ball (c j) (r j)) := by
    ext z; simp [polydisc, Set.mem_pi, mem_ball, dist_eq_norm]
  rw [this]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_ball)

theorem mem_polydisc_add_single [DecidableEq ι] {c : ι → ℂ} {r : ι → ℝ} {w : ι → ℂ} (hw : w ∈ polydisc c r)
    (i : ι) {l : ℂ} (hl : ‖l‖ < r i - ‖w i - c i‖) :
    w + l • (Pi.single i 1 : ι → ℂ) ∈ polydisc c r := by
  intro j
  by_cases hji : j = i
  · subst hji
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    calc ‖w j + l - c j‖ = ‖(w j - c j) + l‖ := by ring_nf
      _ ≤ ‖w j - c j‖ + ‖l‖ := norm_add_le _ _
      _ < r j := by linarith
  · simpa [Pi.single_eq_of_ne hji] using hw j

/-- Coordinate derivative bound on a polydisc. -/
theorem norm_fderiv_single_le [Fintype ι] [DecidableEq ι] {f : (ι → ℂ) → F} {c : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (hf : DifferentiableOn ℂ f (polydisc c r)) (hM : ∀ z ∈ polydisc c r, ‖f z‖ ≤ M)
    {w : ι → ℂ} (hw : w ∈ polydisc c r) (i : ι) :
    ‖fderiv ℂ f w (Pi.single i 1)‖ ≤ M / (r i - ‖w i - c i‖) := by
  have hρ : 0 < r i - ‖w i - c i‖ := by have := hw i; linarith
  exact norm_fderiv_line_le hρ
    (fun l hl => hf.differentiableAt ((isOpen_polydisc c r).mem_nhds (mem_polydisc_add_single hw i hl)))
    (fun l hl => hM _ (mem_polydisc_add_single hw i hl))

/-- Mixed second derivative bound on a polydisc, for distinct coordinates:
`|∂_j ∂_i f (c)| ≤ M / (r_i r_j)`.  (For `i = j` the sharp bound is `2 M / r_i ^ 2`.) -/
theorem norm_mixed_fderiv_le [Fintype ι] [DecidableEq ι] [CompleteSpace F] {f : (ι → ℂ) → F} {c : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (hr : ∀ i, 0 < r i) (hf : AnalyticOnNhd ℂ f (polydisc c r))
    (hM : ∀ z ∈ polydisc c r, ‖f z‖ ≤ M) {i j : ι} (hij : i ≠ j) :
    ‖fderiv ℂ (fun w => fderiv ℂ f w (Pi.single i 1)) c (Pi.single j 1)‖ ≤ M / r i / r j := by
  have hc : c ∈ polydisc c r := fun k => by simpa using hr k
  have hdiff : DifferentiableOn ℂ f (polydisc c r) := hf.differentiableOn
  have hg : ∀ w ∈ polydisc c r,
      DifferentiableAt ℂ (fun w => fderiv ℂ f w (Pi.single i 1)) w := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fderiv ℂ f) w :=
      (hf.fderiv w hw).differentiableAt
    exact h1.clm_apply (differentiableAt_const _)
  have hline : ∀ l : ℂ, ‖l‖ < r j → c + l • (Pi.single j 1 : ι → ℂ) ∈ polydisc c r := by
    intro l hl
    exact mem_polydisc_add_single hc j (by simpa using hl)
  have := norm_fderiv_line_le (hr j)
    (fun l hl => hg _ (hline l hl))
    (fun l hl => by
      have hu := hline l hl
      have h1 := norm_fderiv_single_le hdiff hM hu i
      have h2 : (c + l • (Pi.single j 1 : ι → ℂ)) i = c i := by simp [Pi.single_eq_of_ne hij]
      rw [h2] at h1
      simpa using h1)
  exact this

end Polydisc

end Balaban.Analysis
