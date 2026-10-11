/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic


/-!
# Infinite products `∏ (1 + ξ_j)⁻¹` with geometric decay

`exists_tendsto_prod_inv_one_add`: if `‖ξ_k‖ ≤ c q^k`, `q < 1`, `c ≤ (1 - q)/4`, then
`γ_k = ∏_{j ≤ k} (1 + ξ_j)⁻¹` converges to `γ_∞` with `‖γ_∞ - 1‖ ≤ 2c/(1-q)` and
`‖γ_k - γ_∞‖ ≤ 2 c q^{k+1}/(1-q)` (Balaban P4 (5.31)–(5.33)).
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Analysis

theorem exp_sub_one_le_of_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    Real.exp x - 1 ≤ 4 * x / 3 := by
  have h := Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  have h3 : 1 / (1 - x) ≤ 1 + 4 * x / 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

section Product

variable {ξ : ℕ → ℂ} {c q : ℝ}

theorem sum_norm_Ico_le (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c) (hξ : ∀ k, ‖ξ k‖ ≤ c * q ^ k)
    (a b : ℕ) : ∑ j ∈ Ico a b, ‖ξ j‖ ≤ c * q ^ a / (1 - q) := by
  have h1 : ∑ j ∈ Ico a b, ‖ξ j‖ ≤ ∑ j ∈ Ico a b, c * q ^ j := sum_le_sum fun j _ => hξ j
  refine h1.trans ?_
  rcases le_total a b with hab | hab
  · rw [Finset.sum_Ico_eq_sum_range]
    have hsum : Summable (fun i : ℕ => c * q ^ (a + i)) := by
      simp_rw [pow_add]
      exact ((summable_geometric_of_lt_one hq0 hq1).mul_left (q ^ a)).mul_left c |>.congr
        (fun i => by ring)
    have := hsum.sum_le_tsum (range (b - a)) (fun i _ => by positivity)
    refine this.trans_eq ?_
    simp_rw [pow_add]
    have : ∑' i : ℕ, c * (q ^ a * q ^ i) = c * q ^ a * (1 - q)⁻¹ := by
      simp_rw [← mul_assoc]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    rw [this]; ring
  · rw [Ico_eq_empty_of_le hab]; simp only [sum_empty]; positivity

/-- Partial products of `1 + ξ j`. -/
theorem norm_prod_range_sub_one_le (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c)
    (hξ : ∀ k, ‖ξ k‖ ≤ c * q ^ k) (hs : c ≤ (1 - q) / 4) (n : ℕ) :
    ‖∏ j ∈ range n, (1 + ξ j) - 1‖ ≤ 4 * (c / (1 - q)) / 3 := by
  have h1 := Finset.norm_prod_one_add_sub_one_le (range n) ξ
  have h2 := sum_norm_Ico_le hq0 hq1 hc hξ 0 n
  rw [← range_eq_Ico] at h2
  have hq : 0 < 1 - q := by linarith
  have h3 : c * q ^ 0 / (1 - q) = c / (1 - q) := by simp
  rw [h3] at h2
  have h4 : c / (1 - q) ≤ 1 / 4 := by rw [div_le_iff₀ hq]; linarith
  have h5 : Real.exp (∑ j ∈ range n, ‖ξ j‖) ≤ Real.exp (c / (1 - q)) := Real.exp_le_exp.mpr h2
  have h6 := exp_sub_one_le_of_le (div_nonneg hc hq.le) h4
  linarith

/-- Increments of partial products. -/
theorem norm_prod_range_sub_le (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c)
    (hξ : ∀ k, ‖ξ k‖ ≤ c * q ^ k) (hs : c ≤ (1 - q) / 4) {m n : ℕ} (hmn : m ≤ n) :
    ‖∏ j ∈ range n, (1 + ξ j) - ∏ j ∈ range m, (1 + ξ j)‖ ≤
      ‖∏ j ∈ range m, (1 + ξ j)‖ * (4 * (c * q ^ m / (1 - q)) / 3) := by
  have hq : 0 < 1 - q := by linarith
  have e : ∏ j ∈ range n, (1 + ξ j) - ∏ j ∈ range m, (1 + ξ j) =
      (∏ j ∈ range m, (1 + ξ j)) * (∏ j ∈ Ico m n, (1 + ξ j) - 1) := by
    rw [mul_sub, mul_one, Finset.prod_range_mul_prod_Ico _ hmn]
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := Finset.norm_prod_one_add_sub_one_le (Ico m n) ξ
  have h2 := sum_norm_Ico_le hq0 hq1 hc hξ m n
  have ht0 : 0 ≤ c * q ^ m / (1 - q) := by positivity
  have ht1 : c * q ^ m / (1 - q) ≤ 1 / 4 := by
    have : c * q ^ m ≤ c := mul_le_of_le_one_right hc (pow_le_one₀ hq0 hq1.le)
    rw [div_le_iff₀ hq]; linarith
  have h5 := Real.exp_le_exp.mpr h2
  have h6 := exp_sub_one_le_of_le ht0 ht1
  linarith

/-- **Infinite products** (P4 (5.31)–(5.33)).  If `|ξ_k| ≤ c q^k` with `q < 1` and
`c ≤ (1 - q)/4`, then `γ_k = ∏_{j ≤ k} (1 + ξ_j)⁻¹` converges to some `γ_∞` with
`|γ_∞ - 1| ≤ 2c/(1-q)` and `|γ_k - γ_∞| ≤ 2 c q^{k+1}/(1-q)`. -/
theorem exists_tendsto_prod_inv_one_add (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c)
    (hξ : ∀ k, ‖ξ k‖ ≤ c * q ^ k) (hs : c ≤ (1 - q) / 4) :
    ∃ γ : ℂ, Tendsto (fun k => ∏ j ∈ range (k + 1), (1 + ξ j)⁻¹) atTop (𝓝 γ) ∧
      ‖γ - 1‖ ≤ 2 * c / (1 - q) ∧
      ∀ k, ‖(∏ j ∈ range (k + 1), (1 + ξ j)⁻¹) - γ‖ ≤ 2 * c * q ^ (k + 1) / (1 - q) := by
  have hq : 0 < 1 - q := by linarith
  set P : ℕ → ℂ := fun n => ∏ j ∈ range n, (1 + ξ j) with hP
  have hs4 : c / (1 - q) ≤ 1 / 4 := by rw [div_le_iff₀ hq]; linarith
  have hP1 : ∀ n, ‖P n - 1‖ ≤ 1 / 3 := fun n => by
    have := norm_prod_range_sub_one_le hq0 hq1 hc hξ hs n
    linarith
  have hPlow : ∀ n, 2 / 3 ≤ ‖P n‖ := fun n => by
    have := hP1 n
    have := norm_sub_norm_le 1 (P n)
    rw [norm_sub_rev] at this
    simp at this; linarith
  have hPup : ∀ n, ‖P n‖ ≤ 4 / 3 := fun n => by
    have := hP1 n
    have := norm_le_norm_add_norm_sub' (P n) 1
    simp at this; linarith
  set t : ℕ → ℝ := fun m => c * q ^ m / (1 - q) with ht
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul c |>.div_const (1 - q)
    simpa [ht] using this
  have hinc : ∀ {m n}, m ≤ n → ‖P n - P m‖ ≤ ‖P m‖ * (4 * t m / 3) := fun {m n} hmn =>
    norm_prod_range_sub_le hq0 hq1 hc hξ hs hmn
  have hcau : CauchySeq P := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ((4 / 3) * (4 * t N / 3))) (fun n m N hn hm => ?_) ?_
    · have t0 : 0 ≤ t N := by positivity
      have h1 : dist (P n) (P N) ≤ (4 / 3) * (4 * t N / 3) := by
        rw [dist_eq_norm]
        exact (hinc hn).trans (mul_le_mul_of_nonneg_right (hPup N) (by positivity))
      have h2 : dist (P m) (P N) ≤ (4 / 3) * (4 * t N / 3) := by
        rw [dist_eq_norm]
        exact (hinc hm).trans (mul_le_mul_of_nonneg_right (hPup N) (by positivity))
      calc dist (P n) (P m) ≤ dist (P n) (P N) + dist (P m) (P N) := dist_triangle_right _ _ _
        _ ≤ _ := by linarith
    · simpa using ((ht0.const_mul 4).div_const 3).const_mul (4 / 3) |>.const_mul 2
  obtain ⟨Pi, hPlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hinf1 : ‖Pi - 1‖ ≤ 1 / 3 :=
    le_of_tendsto ((hPlim.sub_const 1).norm) (Eventually.of_forall hP1)
  have hinflow : 2 / 3 ≤ ‖Pi‖ :=
    ge_of_tendsto hPlim.norm (Eventually.of_forall hPlow)
  have hne : Pi ≠ 0 := by
    intro h; rw [h] at hinflow; simp at hinflow; linarith
  have hinf1' : ‖Pi - 1‖ ≤ 4 * (c / (1 - q)) / 3 :=
    le_of_tendsto ((hPlim.sub_const 1).norm)
      (Eventually.of_forall (norm_prod_range_sub_one_le hq0 hq1 hc hξ hs))
  refine ⟨Pi⁻¹, ?_, ?_, fun k => ?_⟩
  · have h1 : Tendsto (fun k => P (k + 1)) atTop (𝓝 Pi) :=
      (tendsto_add_atTop_iff_nat 1).mpr hPlim
    have h2 := h1.inv₀ hne
    refine h2.congr fun k => ?_
    simp [hP, Finset.prod_inv_distrib]
  · have : Pi⁻¹ - 1 = (1 - Pi) / Pi := by field_simp
    rw [this, norm_div, norm_sub_rev, div_le_iff₀ (by linarith)]
    have : 2 * c / (1 - q) = 2 * (c / (1 - q)) := by ring
    rw [this]
    nlinarith [div_nonneg hc hq.le]
  · have hk : (∏ j ∈ range (k + 1), (1 + ξ j)⁻¹) = (P (k + 1))⁻¹ := by
      simp [hP, Finset.prod_inv_distrib]
    rw [hk]
    have hnm : P (k + 1) ≠ 0 := by
      intro h; have := hPlow (k + 1); rw [h] at this; simp at this; linarith
    have hd : ‖Pi - P (k + 1)‖ ≤ ‖P (k + 1)‖ * (4 * t (k + 1) / 3) := by
      refine le_of_tendsto ((hPlim.sub_const (P (k + 1))).norm) ?_
      filter_upwards [eventually_ge_atTop (k + 1)] with n hn
      exact hinc hn
    have e : (P (k + 1))⁻¹ - Pi⁻¹ = (Pi - P (k + 1)) / (P (k + 1) * Pi) := by
      field_simp
    rw [e, norm_div, norm_mul, div_le_iff₀ (by positivity)]
    have t0 : 0 ≤ t (k + 1) := by positivity
    have : 2 * c * q ^ (k + 1) / (1 - q) = 2 * t (k + 1) := by rw [ht]; ring
    rw [this]
    calc ‖Pi - P (k + 1)‖ ≤ ‖P (k + 1)‖ * (4 * t (k + 1) / 3) := hd
      _ ≤ 2 * t (k + 1) * (‖P (k + 1)‖ * ‖Pi‖) := by
          have : 0 ≤ ‖P (k + 1)‖ * t (k + 1) := by positivity
          nlinarith [hinflow]

end Product

end Balaban.Analysis
