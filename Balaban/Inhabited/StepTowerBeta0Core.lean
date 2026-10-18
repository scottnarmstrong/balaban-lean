/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.MarkCorrBudgetTMargin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Two elementary thresholds uniform in the step radius

For the scale `b = β L^{k(d-2)}`, the radii `t ≥ c L^{-α(k+1)}` and `2 α < d - 2`:

* `exists_beta0_pLog_le_t_sqrt`: one `β₀` gives `p₁ ≤ c' t √b` for every cutoff
  `p₁ ≤ A₁ (log b)^p` (the `t^{-2}` form of the threshold `pLogThreshold`);
* `exists_beta0_inv_t_le`: one `β₀` gives `(M₁ / t + M₂) (log b)^q / √b ≤ η`.
-/

@[expose] public section

namespace Balaban.Inhabited

private theorem beta0Core_scale_eq {d L : ℕ} (k : ℕ) :
    (L : ℝ) ^ (k * (d - 2)) = ((L : ℝ) ^ (d - 2)) ^ k := by
  rw [mul_comm, pow_mul]

private theorem beta0Core_radius_eq {d L : ℕ} (hL : 3 ≤ L) (hd : 3 ≤ d) (α : ℝ) (k : ℕ) :
    (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) =
      ((L : ℝ) ^ (d - 2)) ^ (-((α / ((d - 2 : ℕ) : ℝ)) * ((k : ℝ) + 1))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hd0 : ((d - 2 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this.ne'
  rw [← Real.rpow_natCast (L : ℝ) (d - 2), ← Real.rpow_mul hL0.le]
  congr 1
  field_simp

private theorem beta0Core_base_gt {d L : ℕ} (hL : 3 ≤ L) (hd : 3 ≤ d) :
    (1 : ℝ) < (L : ℝ) ^ (d - 2) :=
  one_lt_pow₀ (by exact_mod_cast (by omega : 1 < L)) (by omega)

/-- **`p₁ ≤ c' t √b` uniformly in the step radius.**  For `2 α < d - 2`, `c, c' > 0` there is
`β₀ ≥ 3` such that for every `k`, `β ≥ β₀`, `t ≥ c L^{-α(k+1)}` and every
`0 < p₁ ≤ A₁ (log b)^p`, `b = β L^{k(d-2)}`: `p₁ ≤ c' t √b`. -/
theorem exists_beta0_pLog_le_t_sqrt {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) {A₁ : ℝ} (hA : 0 ≤ A₁)
    (p : ℕ) {c α c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (k : ℕ) (β t p₁ : ℝ), β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t → 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      p₁ ≤ c' * t * Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) := by
  have hd0 : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this
  have hrate : 2 * (α / ((d - 2 : ℕ) : ℝ)) < 1 := by
    rw [← mul_div_assoc, div_lt_one hd0]; exact hα
  obtain ⟨β₀, h3, H⟩ := exists_beta0_marginB_pLog (Λ := (L : ℝ) ^ (d - 2)) (a := 2) (s := 1)
    (α := α / ((d - 2 : ℕ) : ℝ)) (c := c) (C := 1 / c' ^ 2) (A₁ := A₁) p 2
    (beta0Core_base_gt hL hd) hc (by norm_num) one_pos hrate (by positivity) hA
  refine ⟨β₀, h3, fun k β t p₁ hβ hct hp hp₁ => ?_⟩
  have hβ0 : 0 < β := by linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hct
  have hmar := H k β t p₁ hβ (by rw [← beta0Core_radius_eq hL hd α k]; exact hct) hp
    (by rw [← beta0Core_scale_eq k]; exact hp₁)
  rw [← beta0Core_scale_eq k, Real.rpow_one, Real.rpow_two] at hmar
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hs0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have h1 : p₁ ^ 2 ≤ (c' * t * Real.sqrt b) ^ 2 := by
    have h2 : p₁ ^ 2 ≤ c' ^ 2 * (t ^ 2 * b) := by
      rw [one_div, inv_mul_le_iff₀ (by positivity)] at hmar
      exact hmar
    calc p₁ ^ 2 ≤ c' ^ 2 * (t ^ 2 * b) := h2
      _ = (c' * t * Real.sqrt b) ^ 2 := by rw [mul_pow, mul_pow, hsq]; ring
  exact le_of_sq_le_sq h1 (by positivity)

/-- **The `1/t` smallness.**  For `M₁, M₂ ≥ 0`, `η > 0`, `q : ℕ` and `2 α < d - 2` there is
`β₀ ≥ 3` with `(M₁ / t + M₂) (log b)^q / √b ≤ η` for every `k`, `β ≥ β₀`,
`t ≥ c L^{-α(k+1)}`, `b = β L^{k(d-2)}`. -/
theorem exists_beta0_inv_t_le {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) {M₁ M₂ η c α : ℝ}
    (q : ℕ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hη : 0 < η) (hc : 0 < c)
    (hα : 2 * α < ((d - 2 : ℕ) : ℝ)) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ (k : ℕ) (β t : ℝ), β₀ ≤ β →
      c * (L : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ t →
      (M₁ / t + M₂) * Real.log (β * (L : ℝ) ^ (k * (d - 2))) ^ q /
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) ≤ η := by
  have hd0 : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by
    have : 0 < d - 2 := by omega
    exact_mod_cast this
  have hr1 : 1 * (α / ((d - 2 : ℕ) : ℝ)) < 1 / 2 := by
    rw [one_mul, div_lt_iff₀ hd0]; linarith
  have hr0 : 0 * (α / ((d - 2 : ℕ) : ℝ)) < 1 / 2 := by norm_num
  obtain ⟨β₁, h31, H1⟩ := exists_beta0_marginB (Λ := (L : ℝ) ^ (d - 2)) (a := 1) (s := 1 / 2)
    (α := α / ((d - 2 : ℕ) : ℝ)) (c := c) (C := 2 * M₁ / η) q (beta0Core_base_gt hL hd) hc
    zero_le_one (by norm_num) hr1 (by positivity)
  obtain ⟨β₂, h32, H2⟩ := exists_beta0_marginB (Λ := (L : ℝ) ^ (d - 2)) (a := 0) (s := 1 / 2)
    (α := α / ((d - 2 : ℕ) : ℝ)) (c := c) (C := 2 * M₂ / η) q (beta0Core_base_gt hL hd) hc
    le_rfl (by norm_num) hr0 (by positivity)
  refine ⟨max β₁ β₂, h31.trans (le_max_left _ _), fun k β t hβ hct => ?_⟩
  have hβ0 : 0 < β := by have := (le_max_left β₁ β₂).trans hβ; linarith
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by positivity
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hct
  have hrad : c * ((L : ℝ) ^ (d - 2)) ^ (-((α / ((d - 2 : ℕ) : ℝ)) * ((k : ℝ) + 1))) ≤ t := by
    rw [← beta0Core_radius_eq hL hd α k]; exact hct
  have m1 := H1 k β t ((le_max_left _ _).trans hβ) hrad
  have m2 := H2 k β t ((le_max_right _ _).trans hβ) hrad
  rw [← beta0Core_scale_eq k, Real.rpow_one, ← Real.sqrt_eq_rpow] at m1
  rw [← beta0Core_scale_eq k, Real.rpow_zero, one_mul, ← Real.sqrt_eq_rpow] at m2
  set b := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hs0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  rw [div_le_iff₀ hs0, add_mul]
  have e1 : M₁ / t * Real.log b ^ q ≤ η / 2 * Real.sqrt b := by
    rw [div_mul_eq_mul_div, div_le_iff₀ ht0]
    have h' : 2 * M₁ / η * Real.log b ^ q ≤ t * Real.sqrt b := m1
    rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h'
    nlinarith
  have e2 : M₂ * Real.log b ^ q ≤ η / 2 * Real.sqrt b := by
    have h' : 2 * M₂ / η * Real.log b ^ q ≤ Real.sqrt b := m2
    rw [div_mul_eq_mul_div, div_le_iff₀ hη] at h'
    nlinarith
  nlinarith

end Balaban.Inhabited
