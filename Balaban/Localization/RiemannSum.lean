/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Riemann sums of Lipschitz functions

For `g : ℝ → ℂ` that is `L`-Lipschitz on `[0,1]`, the left Riemann sum with `n` pieces
approximates `∫_0^1 g` up to `L / n` (`norm_integral_sub_riemann_le`).
-/

@[expose] public section

namespace Balaban.Localization

open MeasureTheory intervalIntegral Set

theorem norm_integral_sub_riemann_le {g : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖g t - g t'‖ ≤ L * |t - t'|)
    (n : ℕ) (hn : 0 < n) :
    ‖(∫ t in (0 : ℝ)..1, g t) - (1 / (n : ℝ)) • ∑ k ∈ Finset.range n, g (k / n)‖ ≤ L / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcont : ContinuousOn g (Icc 0 1) := by
    have : LipschitzOnWith L.toNNReal g (Icc 0 1) := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hL]
      exact hg x hx y hy
    exact this.continuousOn
  have hmem : ∀ k : ℕ, k ≤ n → (k : ℝ) / n ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hn']; exact_mod_cast hk
  have hint : ∀ k < n, IntervalIntegrable g volume ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) := by
    intro k hk
    refine (hcont.mono ?_).intervalIntegrable
    rw [uIcc_of_le (by gcongr; simp)]
    exact Icc_subset_Icc (hmem k hk.le).1 (hmem (k + 1) hk).2
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (μ := volume) (a := fun k : ℕ => (k : ℝ) / n) (n := n) hint
  simp only [Nat.cast_zero, zero_div, div_self hn'.ne'] at hsum
  rw [← hsum, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hpiece : ∀ k ∈ Finset.range n,
      ‖(∫ t in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), g t) - (1 / (n : ℝ)) • g (k / n)‖
        ≤ L / n * (1 / n) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hlen : ((k + 1 : ℕ) : ℝ) / n - k / n = 1 / n := by push_cast; field_simp; ring
    have hc : (∫ _ in ((k : ℝ) / n)..(((k + 1 : ℕ) : ℝ) / n), g (k / n)) =
        (1 / (n : ℝ)) • g (k / n) := by
      rw [intervalIntegral.integral_const, hlen]
    rw [← hc, ← intervalIntegral.integral_sub (hint k hk') intervalIntegrable_const]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k : ℝ) / n)
      (b := ((k + 1 : ℕ) : ℝ) / n) (C := L / n)
      (f := fun t => g t - g (k / n)) (fun t ht => ?_)
    · rw [hlen] at this
      simpa [abs_of_pos (one_div_pos.mpr hn')] using this
    · have hab : (k : ℝ) / n ≤ ((k + 1 : ℕ) : ℝ) / n := by gcongr; simp
      rw [uIoc_of_le hab] at ht
      have h1 := hg t ⟨le_trans (hmem k hk'.le).1 ht.1.le, le_trans ht.2 (hmem (k + 1) hk').2⟩
        (k / n) (hmem k hk'.le)
      refine h1.trans ?_
      have : |t - k / n| ≤ 1 / n := by
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2]
      calc L * |t - k / n| ≤ L * (1 / n) := mul_le_mul_of_nonneg_left this hL
        _ = L / n := by ring
  refine (Finset.sum_le_sum hpiece).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  exact le_rfl

end Balaban.Localization
