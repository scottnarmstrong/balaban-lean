/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Cauchy estimates for the first two orders along a ray (OBSMARKS 8.2)

This is a routine leaf.  The observable marks family (`ObsMarks` for the physical zero-class step)
is NOT constructed here.

Let `e : ℂ → E` be complex differentiable on the disc `|u| < ρ` and bounded by `K` there.  Then

* `norm_deriv_zero_le`: `‖e'(0)‖ ≤ K/ρ`;
* `norm_deriv_sub_deriv_zero_le`: the remainder `R(u) = e'(u) - e'(0)` satisfies
  `‖R(u)‖ ≤ 2K|u| / (ρ (ρ - |u|))`, which implies the bound
  `‖R(u)‖ ≤ (K/ρ) [(1 - |u|/ρ)⁻² - 1]` (`norm_deriv_sub_deriv_zero_le_note`);
* with `q = 1/ρ`: `‖R(u)‖ ≤ 6 K q²` for `|u| ≤ 1`, `q ≤ 1/2`, and `‖R(u)‖ ≤ 8 K q²` for
  `|u| < 3/2`, `q ≤ 1/4` (the sharper constants 4 and 5 hold);
* the zero extension `remExt` of `R` outside `|u| < 3/2` is bounded by `8 K q²` everywhere and
  holomorphic on the disc `|u| < 3/2`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Limit step: a bound for every smaller radius passes to the radius itself. -/
theorem le_of_forall_lt_radius {X R K : ℝ} {n : ℕ} (hR : 0 < R)
    (h : ∀ r, 0 < r → r < R → X ≤ n.factorial * K / r ^ n) :
    X ≤ n.factorial * K / R ^ n := by
  have hc : Tendsto (fun r : ℝ => (n.factorial : ℝ) * K / r ^ n) (𝓝[<] R)
      (𝓝 (n.factorial * K / R ^ n)) :=
    (((continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne'))).tendsto).mono_left
      nhdsWithin_le_nhds
  refine ge_of_tendsto hc ?_
  filter_upwards [Ioo_mem_nhdsLT hR] with r hr using h r hr.1 hr.2

/-- **Cauchy estimate for the `n`-th derivative at a point of the disc**. -/
theorem norm_iteratedDeriv_le_disc {e : ℂ → E} {ρ K : ℝ}
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {c : ℂ}
    (hc : ‖c‖ < ρ) (n : ℕ) :
    ‖iteratedDeriv n e c‖ ≤ n.factorial * K / (ρ - ‖c‖) ^ n := by
  refine le_of_forall_lt_radius (by linarith) fun r hr0 hr => ?_
  have hsub : closedBall c r ⊆ ball 0 ρ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ < ρ := by linarith
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr0 ?_ fun z hz =>
    hK z (hsub (sphere_subset_closedBall hz))
  exact hd.diffContOnCl_ball hsub

theorem le_of_inv_le_one_div {ρ a : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hq : ρ⁻¹ ≤ 1 / a) :
    a ≤ ρ := by
  have h := mul_inv_cancel₀ hρ.ne'
  have h2 : ρ * ρ⁻¹ ≤ ρ * (1 / a) := mul_le_mul_of_nonneg_left hq hρ.le
  rw [h] at h2
  rw [mul_one_div, le_div_iff₀ ha] at h2
  linarith

/-- **A1.** `‖e'(0)‖ ≤ K/ρ`. -/
theorem norm_deriv_zero_le {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) :
    ‖deriv e 0‖ ≤ K / ρ := by
  have := norm_iteratedDeriv_le_disc hd hK (c := 0) (by simpa using hρ) 1
  simpa using this

/-- First derivative at a point of the disc: `‖e'(c)‖ ≤ K/(ρ - |c|)`. -/
theorem norm_deriv_le_disc {e : ℂ → E} {ρ K : ℝ}
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {c : ℂ}
    (hc : ‖c‖ < ρ) : ‖deriv e c‖ ≤ K / (ρ - ‖c‖) := by
  have := norm_iteratedDeriv_le_disc hd hK hc 1
  simpa using this

theorem norm_deriv_deriv_le_disc {e : ℂ → E} {ρ K : ℝ}
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {c : ℂ}
    (hc : ‖c‖ < ρ) : ‖deriv (deriv e) c‖ ≤ 2 * K / (ρ - ‖c‖) ^ 2 := by
  have := norm_iteratedDeriv_le_disc hd hK hc 2
  rw [iteratedDeriv_succ, iteratedDeriv_one] at this
  simpa [Nat.factorial] using this

theorem differentiableOn_deriv_disc {e : ℂ → E} {ρ : ℝ}
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) : DifferentiableOn ℂ (deriv e) (ball 0 ρ) :=
  (hd.analyticOnNhd isOpen_ball).deriv.differentiableOn

/-- **A2.** The remainder `R(u) = e'(u) - e'(0)` satisfies `‖R(u)‖ ≤ 2K|u| / (ρ(ρ - |u|))`. -/
theorem norm_deriv_sub_deriv_zero_le {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {u : ℂ}
    (hu : ‖u‖ < ρ) :
    ‖deriv e u - deriv e 0‖ ≤ 2 * K * ‖u‖ / (ρ * (ρ - ‖u‖)) := by
  have hd' := differentiableOn_deriv_disc hd
  have hmem : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ((t : ℂ) * u) ∈ ball (0 : ℂ) ρ := by
    intro t ht
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc t * ‖u‖ ≤ 1 * ‖u‖ := by gcongr; exact ht.2
      _ < ρ := by simpa using hu
  have hden : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → 0 < ρ - t * ‖u‖ := by
    intro t ht
    have : t * ‖u‖ ≤ ‖u‖ := by
      calc t * ‖u‖ ≤ 1 * ‖u‖ := by gcongr; exact ht.2
        _ = ‖u‖ := one_mul _
    linarith
  set f : ℝ → E := fun t => deriv e ((t : ℂ) * u) - deriv e 0 with hf
  have hfd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt f (u • deriv (deriv e) ((t : ℂ) * u)) t := by
    intro t ht
    have hda : HasDerivAt (deriv e) (deriv (deriv e) ((t : ℂ) * u)) ((t : ℂ) * u) :=
      ((hd'.differentiableAt (isOpen_ball.mem_nhds (hmem t ht)))).hasDerivAt
    have hin : HasDerivAt (fun r : ℝ => (r : ℂ) * u) (1 * u) t :=
      ((hasDerivAt_id t).ofReal_comp).mul_const u
    have h1 : HasDerivAt (fun r : ℝ => deriv e ((r : ℂ) * u))
        ((1 * u) • deriv (deriv e) ((t : ℂ) * u)) t := HasDerivAt.scomp (h := fun r : ℝ => (r : ℂ) * u) t hda hin
    simpa [hf] using h1.sub_const (deriv e 0)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  let B : ℝ → ℝ := fun t => 2 * K * (ρ - t * ‖u‖)⁻¹ - 2 * K * ρ⁻¹
  let B' : ℝ → ℝ := fun t => 2 * K * ‖u‖ / (ρ - t * ‖u‖) ^ 2
  have hBd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt B (B' t) t := by
    intro t ht
    have hne := (hden t ht).ne'
    have h1 : HasDerivAt (fun t : ℝ => ρ - t * ‖u‖) (-‖u‖) t := by
      simpa using ((hasDerivAt_id t).mul_const ‖u‖).const_sub ρ
    have h3 := ((h1.inv hne).const_mul (2 * K)).sub_const (2 * K * ρ⁻¹)
    refine h3.congr_deriv ?_
    simp only [B']
    field_simp
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := fun t ht => (hfd t ht).continuousAt.continuousWithinAt
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := f)
    (f' := fun t => u • deriv (deriv e) ((t : ℂ) * u)) (a := 0) (b := 1) hfc
    (fun t ht => (hfd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := B) (B' := B') (by simp [hf, B]) (fun t ht => (hBd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hBd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (by
      intro t ht
      have ht' := Ico_subset_Icc_self ht
      have hn : ‖(t : ℂ) * u‖ = t * ‖u‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      have h2 := norm_deriv_deriv_le_disc hd hK (c := (t : ℂ) * u) (by simpa using hmem t ht')
      rw [hn] at h2
      rw [norm_smul]
      simp only [B']
      calc ‖u‖ * ‖deriv (deriv e) ((t : ℂ) * u)‖ ≤ ‖u‖ * (2 * K / (ρ - t * ‖u‖) ^ 2) := by
            gcongr
        _ = 2 * K * ‖u‖ / (ρ - t * ‖u‖) ^ 2 := by ring) (x := 1) ⟨zero_le_one, le_rfl⟩
  have hρne := hρ.ne'
  have hune : ρ - ‖u‖ ≠ 0 := (sub_pos.2 hu).ne'
  calc ‖deriv e u - deriv e 0‖ = ‖f 1‖ := by simp [hf]
    _ ≤ B 1 := hmain
    _ = 2 * K * ‖u‖ / (ρ * (ρ - ‖u‖)) := by
      simp only [B, one_mul]
      field_simp
      ring

/-- **A2, the form of the note.** `‖R(u)‖ ≤ (K/ρ) [(1 - |u|/ρ)⁻² - 1]`. -/
theorem norm_deriv_sub_deriv_zero_le_note {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {u : ℂ}
    (hu : ‖u‖ < ρ) :
    ‖deriv e u - deriv e 0‖ ≤ K / ρ * (((1 - ‖u‖ / ρ) ^ 2)⁻¹ - 1) := by
  refine (norm_deriv_sub_deriv_zero_le hρ hd hK hu).trans ?_
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  set x := ‖u‖ / ρ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one hρ]; exact hu
  have h1 : 0 < 1 - x := by linarith
  have hu' : ‖u‖ = ρ * x := by rw [hx]; field_simp
  have hkey : ((1 - x) ^ 2)⁻¹ - 1 - 2 * x / (1 - x) = x ^ 2 / (1 - x) ^ 2 := by
    field_simp; ring
  have hnn : 0 ≤ x ^ 2 / (1 - x) ^ 2 := by positivity
  have heq : 2 * K * ‖u‖ / (ρ * (ρ - ‖u‖)) = K / ρ * (2 * x / (1 - x)) := by
    rw [hu']
    have : ρ - ρ * x = ρ * (1 - x) := by ring
    rw [this]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **A3, first corollary.** For `q = 1/ρ ≤ 1/2` and `|u| ≤ 1`: `‖R(u)‖ ≤ 4 K q² ≤ 6 K q²`. -/
theorem norm_deriv_sub_deriv_zero_le_four {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hq : ρ⁻¹ ≤ 1 / 2) (hd : DifferentiableOn ℂ e (ball 0 ρ))
    (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖deriv e u - deriv e 0‖ ≤ 4 * K * (ρ⁻¹) ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  have hρ2 : 2 ≤ ρ := by
    exact le_of_inv_le_one_div hρ (by norm_num) hq
  have hlt : ‖u‖ < ρ := by linarith
  refine (norm_deriv_sub_deriv_zero_le hρ hd hK hlt).trans ?_
  have hs0 := norm_nonneg u
  set s := ‖u‖
  have h1 : 0 < ρ - s := by linarith
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 2 * s * ρ ≤ 4 * ρ - 4 * s := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 hρ.le)]

/-- **A3, first corollary, note constant.** `‖R(u)‖ ≤ 6 K q²` for `q ≤ 1/2`, `0 ≤ u ≤ 1`
(in fact for `|u| ≤ 1`). -/
theorem norm_deriv_sub_deriv_zero_le_six {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hq : ρ⁻¹ ≤ 1 / 2) (hd : DifferentiableOn ℂ e (ball 0 ρ))
    (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {u : ℂ} (hu : ‖u‖ ≤ 1) :
    ‖deriv e u - deriv e 0‖ ≤ 6 * K * (ρ⁻¹) ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  refine (norm_deriv_sub_deriv_zero_le_four hρ hq hd hK hu).trans ?_
  have : 0 ≤ K * (ρ⁻¹) ^ 2 := by positivity
  nlinarith

/-- **A3, second corollary.** For `q = 1/ρ ≤ 1/4` and `|u| < 3/2`: `‖R(u)‖ ≤ 5 K q² ≤ 8 K q²`. -/
theorem norm_deriv_sub_deriv_zero_le_five {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hq : ρ⁻¹ ≤ 1 / 4) (hd : DifferentiableOn ℂ e (ball 0 ρ))
    (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {u : ℂ} (hu : ‖u‖ < 3 / 2) :
    ‖deriv e u - deriv e 0‖ ≤ 5 * K * (ρ⁻¹) ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  have hρ4 : 4 ≤ ρ := by
    exact le_of_inv_le_one_div hρ (by norm_num) hq
  have hlt : ‖u‖ < ρ := by linarith
  refine (norm_deriv_sub_deriv_zero_le hρ hd hK hlt).trans ?_
  have hs0 := norm_nonneg u
  set s := ‖u‖
  have h1 : 0 < ρ - s := by linarith
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 2 * s * ρ ≤ 5 * ρ - 5 * s := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0 hρ.le)]

/-- **A3, second corollary, note constant.** `‖R(u)‖ ≤ 8 K q²` for `q ≤ 1/4`, `|u| < 3/2`. -/
theorem norm_deriv_sub_deriv_zero_le_eight {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ)
    (hq : ρ⁻¹ ≤ 1 / 4) (hd : DifferentiableOn ℂ e (ball 0 ρ))
    (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) {u : ℂ} (hu : ‖u‖ < 3 / 2) :
    ‖deriv e u - deriv e 0‖ ≤ 8 * K * (ρ⁻¹) ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  refine (norm_deriv_sub_deriv_zero_le_five hρ hq hd hK hu).trans ?_
  have : 0 ≤ K * (ρ⁻¹) ^ 2 := by positivity
  nlinarith

open Classical in
/-- The remainder `R(u) = e'(u) - e'(0)` on the disc `|u| < 3/2`, extended by zero. -/
noncomputable def remExt (e : ℂ → E) (u : ℂ) : E :=
  if ‖u‖ < 3 / 2 then deriv e u - deriv e 0 else 0

omit [CompleteSpace E] in
theorem remExt_eq_of_lt (e : ℂ → E) {u : ℂ} (hu : ‖u‖ < 3 / 2) :
    remExt e u = deriv e u - deriv e 0 := by
  simp [remExt, hu]

omit [CompleteSpace E] in
theorem remExt_eq_zero_of_le (e : ℂ → E) {u : ℂ} (hu : 3 / 2 ≤ ‖u‖) : remExt e u = 0 := by
  simp [remExt, not_lt.2 hu]

/-- **A4.** The zero extension is bounded by `8 K q²` for every `u : ℂ`. -/
theorem norm_remExt_le {e : ℂ → E} {ρ K : ℝ} (hρ : 0 < ρ) (hq : ρ⁻¹ ≤ 1 / 4)
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) (hK : ∀ u ∈ ball (0 : ℂ) ρ, ‖e u‖ ≤ K) (u : ℂ) :
    ‖remExt e u‖ ≤ 8 * K * (ρ⁻¹) ^ 2 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_ball_self hρ))
  by_cases hu : ‖u‖ < 3 / 2
  · rw [remExt_eq_of_lt e hu]
    exact norm_deriv_sub_deriv_zero_le_eight hρ hq hd hK hu
  · rw [remExt_eq_zero_of_le e (not_lt.1 hu)]
    simp only [norm_zero]; positivity

/-- **A4.** The zero extension is holomorphic on the disc `|u| < 3/2`. -/
theorem differentiableOn_remExt {e : ℂ → E} {ρ : ℝ} (hρ : 0 < ρ) (hq : ρ⁻¹ ≤ 1 / 4)
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) :
    DifferentiableOn ℂ (remExt e) (ball 0 (3 / 2)) := by
  have hρ4 : 4 ≤ ρ := by
    exact le_of_inv_le_one_div hρ (by norm_num) hq
  have hsub : ball (0 : ℂ) (3 / 2) ⊆ ball 0 ρ := ball_subset_ball (by linarith)
  have h1 : DifferentiableOn ℂ (fun u => deriv e u - deriv e 0) (ball 0 (3 / 2)) :=
    ((differentiableOn_deriv_disc hd).mono hsub).sub_const _
  refine h1.congr fun u hu => ?_
  exact remExt_eq_of_lt e (by simpa using hu)

/-- **A4.** The zero extension is analytic on a neighbourhood of every point of the disc
`|u| < 3/2`. -/
theorem analyticOnNhd_remExt {e : ℂ → E} {ρ : ℝ} (hρ : 0 < ρ) (hq : ρ⁻¹ ≤ 1 / 4)
    (hd : DifferentiableOn ℂ e (ball 0 ρ)) :
    AnalyticOnNhd ℂ (remExt e) (ball 0 (3 / 2)) :=
  (differentiableOn_remExt hρ hq hd).analyticOnNhd isOpen_ball

/-- **A5.** The estimates for a family `e_Y` with `K_Y = K exp(-κ d_Y)`: the first coefficient,
and the global bound of the zero extension of the remainder. -/
theorem family_norm_deriv_zero_le {ι : Type*} {e : ι → ℂ → E} {ρ K κ : ℝ} {d : ι → ℝ}
    (hρ : 0 < ρ) (hd : ∀ Y, DifferentiableOn ℂ (e Y) (ball 0 ρ))
    (hK : ∀ Y, ∀ u ∈ ball (0 : ℂ) ρ, ‖e Y u‖ ≤ K * Real.exp (-κ * d Y)) (Y : ι) :
    ‖deriv (e Y) 0‖ ≤ K * (ρ⁻¹) * Real.exp (-κ * d Y) := by
  have := norm_deriv_zero_le hρ (hd Y) (hK Y)
  rw [div_eq_mul_inv] at this
  linarith

theorem family_norm_remExt_le {ι : Type*} {e : ι → ℂ → E} {ρ K κ : ℝ} {d : ι → ℝ}
    (hρ : 0 < ρ) (hq : ρ⁻¹ ≤ 1 / 4) (hd : ∀ Y, DifferentiableOn ℂ (e Y) (ball 0 ρ))
    (hK : ∀ Y, ∀ u ∈ ball (0 : ℂ) ρ, ‖e Y u‖ ≤ K * Real.exp (-κ * d Y)) (Y : ι) (u : ℂ) :
    ‖remExt (e Y) u‖ ≤ 8 * K * (ρ⁻¹) ^ 2 * Real.exp (-κ * d Y) := by
  have := norm_remExt_le hρ hq (hd Y) (hK Y) u
  linarith

end Balaban.Fluctuation
