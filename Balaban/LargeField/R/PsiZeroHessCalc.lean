/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Second-order touching (calculus for the Hessian lower bound)

If `g` has a derivative `g'` near `0` which is itself differentiable at `0`, and is sandwiched between two
parabolas `g 0 + b t + c t²`, `g 0 + b t + C t²` that touch at `0`, then `g'(0) = b` and `2 c ≤ g''(0)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Filter Topology

theorem hasDerivAt_parab {g : ℝ → ℝ} {g' x g0 b M : ℝ} (hx : HasDerivAt g g' x) :
    HasDerivAt (fun y => g y - g0 - b * y - M * y ^ 2) (g' - b - M * (2 * x)) x := by
  have h1 := ((hx.sub_const g0).sub ((hasDerivAt_id' x).const_mul b)).sub
    ((hasDerivAt_pow 2 x).const_mul M)
  refine h1.congr_deriv ?_
  simp

theorem deriv_eq_of_upper {g g' : ℝ → ℝ} {b C : ℝ}
    (hd : HasDerivAt g (g' 0) 0) (hup : ∀ᶠ t in 𝓝 (0 : ℝ), g t ≤ g 0 + b * t + C * t ^ 2) :
    g' 0 = b := by
  have h1 : IsLocalMax (fun t => g t - g 0 - b * t - C * t ^ 2) 0 := by
    filter_upwards [hup] with t ht
    simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    linarith
  have hder := hasDerivAt_parab (g0 := g 0) (b := b) (M := C) hd
  have := h1.hasDerivAt_eq_zero hder
  simp at this
  linarith

theorem hess_of_sandwich {g g' : ℝ → ℝ} {g2 b c C : ℝ}
    (hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (g' t) t) (hd2 : HasDerivAt g' g2 0)
    (hup : ∀ᶠ t in 𝓝 (0 : ℝ), g t ≤ g 0 + b * t + C * t ^ 2)
    (hlo : ∀ᶠ t in 𝓝 (0 : ℝ), g 0 + b * t + c * t ^ 2 ≤ g t) : g' 0 = b ∧ 2 * c ≤ g2 := by
  have h0 : HasDerivAt g (g' 0) 0 := hd.self_of_nhds
  have hb := deriv_eq_of_upper h0 hup
  refine ⟨hb, ?_⟩
  by_contra hlt
  push Not at hlt
  -- `h2' = g' - b - 2 c t` has slope `g2 - 2c < 0` at 0 and vanishes there
  set s := g2 - 2 * c with hs
  have hneg : s < 0 := by linarith
  have hh2 : HasDerivAt (fun t => g' t - b - 2 * c * t) s 0 := by
    refine ((hd2.sub_const b).sub ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * c))).congr_deriv ?_
    simp [hs]
  have hz : g' 0 - b - 2 * c * 0 = 0 := by rw [hb]; ring
  -- eventually `h2' t < 0` for `t > 0` small
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), g' t - b - 2 * c * t < 0 := by
    have hslope := hh2.tendsto_slope_zero_right
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • ((g' (0 + t) - b - 2 * c * (0 + t)) -
        (g' 0 - b - 2 * c * 0)) < 0 := hslope.eventually (gt_mem_nhds hneg)
    filter_upwards [this, self_mem_nhdsWithin] with t ht htpos
    have htpos' : (0 : ℝ) < t := htpos
    simp only [zero_add, hz, sub_zero, smul_eq_mul] at ht
    by_contra hge
    push Not at hge
    have : 0 ≤ t⁻¹ * (g' t - b - 2 * c * t) := mul_nonneg (inv_nonneg.2 htpos'.le) hge
    linarith
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, ∀ t, 0 < t → t < ε →
      g' t - b - 2 * c * t < 0 ∧ HasDerivAt g (g' t) t := by
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), HasDerivAt g (g' t) t := nhdsWithin_le_nhds hd
    have h3 := hev.and h2
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h3
    obtain ⟨ε, hε, h⟩ := h3
    refine ⟨ε, hε, fun t ht0 htε => h ?_ ht0⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htε
  have hlow : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ g t - g 0 - b * t - c * t ^ 2 := by
    filter_upwards [nhdsWithin_le_nhds hlo] with t ht
    linarith
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlow
  obtain ⟨ρ, hρ, hρ'⟩ := hlow
  set t := min (ε / 2) (ρ / 2) with ht
  have htpos : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htρ : t < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hge := hρ' (by rw [Real.dist_eq, sub_zero, abs_of_pos htpos]; exact htρ) htpos
  -- mean value theorem for `h2 t = g t - g 0 - b t - c t²` on `[0, t]`
  have hderiv : ∀ x ∈ Set.Ioo 0 t, HasDerivAt (fun y => g y - g 0 - b * y - c * y ^ 2)
      (g' x - b - 2 * c * x) x := by
    intro x hx
    have hx' := (hεsub x hx.1 (lt_trans hx.2 htε)).2
    refine (hasDerivAt_parab (g0 := g 0) (b := b) (M := c) hx').congr_deriv ?_
    ring
  have hcont : ContinuousOn (fun y => g y - g 0 - b * y - c * y ^ 2) (Set.Icc 0 t) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      have : ContinuousAt g 0 := h0.continuousAt
      exact (((this.sub continuousAt_const).sub (continuousAt_const.mul continuousAt_id)).sub
        (continuousAt_const.mul (continuousAt_id.pow 2))).continuousWithinAt
    · have hx' := (hεsub x h (lt_of_le_of_lt hx.2 htε)).2
      exact (((hx'.continuousAt.sub continuousAt_const).sub (continuousAt_const.mul continuousAt_id)).sub
        (continuousAt_const.mul (continuousAt_id.pow 2))).continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun y => g y - g 0 - b * y - c * y ^ 2)
    (fun x => g' x - b - 2 * c * x) htpos hcont hderiv
  have hξneg := (hεsub ξ hξ.1 (lt_trans hξ.2 htε)).1
  simp only [sub_self, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hξe
  have : g t - g 0 - b * t - c * t ^ 2 = (g' ξ - b - 2 * c * ξ) * t := by
    field_simp at hξe
    linarith
  nlinarith [mul_pos_of_neg_of_neg hξneg (neg_neg_of_pos htpos)]

end Balaban.LargeField
