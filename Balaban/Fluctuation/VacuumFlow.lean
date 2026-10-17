/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The flow of the vacuum constant `E_k` and its normalization (package `VacuumFlow`)

One renormalization step changes the vacuum constant of the class by
`E_{k+1} = L^d E_k + g_k` (P4 (2.1), (2.41), (2.63), (4.21); `vacuumEnergy_succ_of_absorb`), where the
increment `g_k = L^d (E'''_k - E_k) - e₀ / |T^{(k+1)}_1|` does not depend on `E_k`.  This file
proves the facts about such a recursion, for a general factor `q` (`q = L^d` in the application).

* `vacuum_sub_eq`: two solutions with the same increments differ by `q^k (E'_0 - E_0)`.  So a
  solution started from a fixed `E_0` grows like `q^k` (`E_k |T^{(k)}_1|` is the vacuum free
  energy accumulated over all scales below `k`, extensive in the volume of the finest lattice).
* `vacuum_backward_eq`: `E_k = E_K / q^{K-k} - ∑_{i < K - k} g_{k+i} / q^{i+1}` for `k ≤ K`.
* `abs_vacuum_backward_le`: if `|g_j| ≤ A λ_j + B` and `λ_{k+i} ≤ λ_k + i θ`, then
  `|E_k - E_K / q^{K-k}| ≤ (A λ_k + B)/(q - 1) + A θ/(q - 1)²`, uniformly in `k ≤ K`.
* `abs_vacuum_le_of_final_eq_zero`: the solution with `E_K = 0` (the normalization in which the
  vacuum energy of all scales below `K` is a global constant) satisfies
  `|E_k| ≤ C' λ_k + C'`, `C' = (A + B)/(q - 1) + A θ/(q - 1)²`.
* `vacuum_sub_backward_eq`, `abs_vacuum_init_sub_le`: the deviation of any solution from the
  backward solution is `q^k` times its deviation at `k = 0`, and a bound `|E_K| ≤ M` at the last
  scale forces `|E_0 - E*_0| ≤ M / q^K`: the bound `|E_k| ≤ C' λ_k + C'` holds for one value of
  the initial constant only (up to `q^{-K}`).
-/

@[expose] public section

namespace Balaban.Fluctuation.VacuumFlow

open Finset

variable {q : ℝ} {E E' g : ℕ → ℝ} {K : ℕ}

/-- **Two solutions of the recursion differ by `q^k (E'_0 - E_0)`.** -/
theorem vacuum_sub_eq (hE : ∀ j, j < K → E (j + 1) = q * E j + g j)
    (hE' : ∀ j, j < K → E' (j + 1) = q * E' j + g j) :
    ∀ k, k ≤ K → E' k - E k = q ^ k * (E' 0 - E 0) := by
  intro k hk
  induction k with
  | zero => simp
  | succ n ih =>
    have hn : n < K := hk
    rw [hE n hn, hE' n hn, pow_succ]
    have := ih hn.le
    calc q * E' n + g n - (q * E n + g n) = q * (E' n - E n) := by ring
      _ = q * (q ^ n * (E' 0 - E 0)) := by rw [this]
      _ = q ^ n * q * (E' 0 - E 0) := by ring

/-- **The backward form of the recursion**: for `k ≤ K`,
`E_k = E_K / q^{K-k} - ∑_{i < K - k} g_{k+i} / q^{i+1}`. -/
theorem vacuum_backward_eq (hq : q ≠ 0) (hE : ∀ j, j < K → E (j + 1) = q * E j + g j) {k : ℕ}
    (hk : k ≤ K) :
    E k = E K / q ^ (K - k) - ∑ i ∈ range (K - k), g (k + i) / q ^ (i + 1) := by
  suffices H : ∀ n k, k + n = K →
      E k = E (k + n) / q ^ n - ∑ i ∈ range n, g (k + i) / q ^ (i + 1) by
    have h := H (K - k) k (by omega)
    rwa [show k + (K - k) = K by omega] at h
  intro n
  induction n with
  | zero => intro k _; simp
  | succ n ih =>
    intro k hkn
    have hrec := hE k (by omega)
    have h1 := ih (k + 1) (by omega)
    rw [show k + 1 + n = k + (n + 1) by omega] at h1
    rw [sum_range_succ']
    have hsum : ∑ i ∈ range n, g (k + (i + 1)) / q ^ (i + 1 + 1) =
        (∑ i ∈ range n, g (k + 1 + i) / q ^ (i + 1)) / q := by
      rw [Finset.sum_div]
      refine sum_congr rfl fun i _ => ?_
      rw [show k + (i + 1) = k + 1 + i by omega, pow_succ]
      field_simp
    have hEk : E k = (E (k + 1) - g k) / q := by
      rw [hrec]; field_simp; ring
    rw [hsum, hEk, h1, pow_succ]
    simp only [add_zero, zero_add, pow_one]
    field_simp
    ring

/-- `∑_{i < n} q^{-(i+1)} ≤ 1/(q - 1)` for `q > 1`. -/
theorem sum_inv_pow_le (hq : 1 < q) (n : ℕ) :
    ∑ i ∈ range n, 1 / q ^ (i + 1) ≤ 1 / (q - 1) := by
  have hq0 : 0 < q := by linarith
  set x : ℝ := q⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq
  have hterm : ∀ i : ℕ, 1 / q ^ (i + 1) = x * x ^ i := fun i => by
    rw [hx, ← pow_succ', inv_pow, one_div]
  simp_rw [hterm]
  rw [← mul_sum]
  have hs : ∑ i ∈ range n, x ^ i ≤ (1 - x)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hx0 hx1]
    exact (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ (fun i _ => pow_nonneg hx0 i)
  calc x * ∑ i ∈ range n, x ^ i ≤ x * (1 - x)⁻¹ := mul_le_mul_of_nonneg_left hs hx0
    _ = 1 / (q - 1) := by
      rw [hx]
      have : q - 1 ≠ 0 := by linarith
      field_simp

/-- `∑_{i < n} i q^{-(i+1)} ≤ 1/(q - 1)²` for `q > 1`. -/
theorem sum_mul_inv_pow_le (hq : 1 < q) (n : ℕ) :
    ∑ i ∈ range n, (i : ℝ) / q ^ (i + 1) ≤ 1 / (q - 1) ^ 2 := by
  have hq0 : 0 < q := by linarith
  set x : ℝ := q⁻¹ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ hq
  have hxn : ‖x‖ < 1 := by rw [Real.norm_of_nonneg hx0]; exact hx1
  have hterm : ∀ i : ℕ, (i : ℝ) / q ^ (i + 1) = x * ((i : ℝ) * x ^ i) := fun i => by
    rw [hx, inv_pow, pow_succ]
    field_simp
  simp_rw [hterm]
  rw [← mul_sum]
  have hs : ∑ i ∈ range n, (i : ℝ) * x ^ i ≤ x / (1 - x) ^ 2 := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hxn]
    have hsum : Summable (fun i : ℕ => (i : ℝ) * x ^ i) := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hxn
    exact hsum.sum_le_tsum _ (fun i _ => mul_nonneg (Nat.cast_nonneg i) (pow_nonneg hx0 i))
  calc x * ∑ i ∈ range n, (i : ℝ) * x ^ i ≤ x * (x / (1 - x) ^ 2) :=
        mul_le_mul_of_nonneg_left hs hx0
    _ = 1 / (q - 1) ^ 2 := by
      rw [hx]
      have : q - 1 ≠ 0 := by linarith
      field_simp

/-- **The backward sum is bounded by the size of the increments at the scale `k`**: if
`|g_{k+i}| ≤ A λ_{k+i} + B` and `λ_{k+i} ≤ λ_k + i θ` for `i < n`, then
`|∑_{i<n} g_{k+i} / q^{i+1}| ≤ (A λ_k + B)/(q - 1) + A θ/(q - 1)²`. -/
theorem abs_backward_sum_le (hq : 1 < q) {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ)
    {lam : ℕ → ℝ} {k : ℕ} (hl0 : 0 ≤ lam k) (n : ℕ)
    (hg : ∀ i, i < n → |g (k + i)| ≤ A * lam (k + i) + B)
    (hl : ∀ i, i < n → lam (k + i) ≤ lam k + i * θ) :
    |∑ i ∈ range n, g (k + i) / q ^ (i + 1)| ≤
      (A * lam k + B) / (q - 1) + A * θ / (q - 1) ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hterm : ∀ i ∈ range n, |g (k + i) / q ^ (i + 1)| ≤
      (A * lam k + B) * (1 / q ^ (i + 1)) + A * θ * ((i : ℝ) / q ^ (i + 1)) := by
    intro i hi
    have hi' : i < n := mem_range.1 hi
    have hp : 0 < q ^ (i + 1) := pow_pos hq0 _
    rw [abs_div, abs_of_pos hp]
    have h1 := hg i hi'
    have h2 := hl i hi'
    have h3 : |g (k + i)| ≤ A * lam k + B + A * θ * i := by
      have := mul_le_mul_of_nonneg_left h2 hA
      nlinarith
    calc |g (k + i)| / q ^ (i + 1) ≤ (A * lam k + B + A * θ * i) / q ^ (i + 1) :=
          div_le_div_of_nonneg_right h3 hp.le
      _ = _ := by field_simp
  calc |∑ i ∈ range n, g (k + i) / q ^ (i + 1)|
      ≤ ∑ i ∈ range n, |g (k + i) / q ^ (i + 1)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, ((A * lam k + B) * (1 / q ^ (i + 1)) +
          A * θ * ((i : ℝ) / q ^ (i + 1))) := sum_le_sum hterm
    _ = (A * lam k + B) * ∑ i ∈ range n, 1 / q ^ (i + 1) +
          A * θ * ∑ i ∈ range n, (i : ℝ) / q ^ (i + 1) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ (A * lam k + B) * (1 / (q - 1)) + A * θ * (1 / (q - 1) ^ 2) := by
        have hc1 : 0 ≤ A * lam k + B := by positivity
        have hc2 : 0 ≤ A * θ := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left (sum_inv_pow_le hq n) hc1)
          (mul_le_mul_of_nonneg_left (sum_mul_inv_pow_le hq n) hc2)
    _ = _ := by ring

/-- **The bound for the solution measured from the last scale**: for a solution of
`E_{j+1} = q E_j + g_j` on `[k, K)`, with `|g_j| ≤ A λ_j + B` and `λ_j ≤ λ_k + (j - k) θ`,
`|E_k - E_K / q^{K-k}| ≤ (A λ_k + B)/(q - 1) + A θ/(q - 1)²`. -/
theorem abs_vacuum_backward_le (hq : 1 < q) (hE : ∀ j, j < K → E (j + 1) = q * E j + g j)
    {k : ℕ} (hk : k ≤ K) {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ) {lam : ℕ → ℝ}
    (hl0 : 0 ≤ lam k) (hg : ∀ j, k ≤ j → j < K → |g j| ≤ A * lam j + B)
    (hl : ∀ j, k ≤ j → j < K → lam j ≤ lam k + ((j - k : ℕ) : ℝ) * θ) :
    |E k - E K / q ^ (K - k)| ≤ (A * lam k + B) / (q - 1) + A * θ / (q - 1) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hb := vacuum_backward_eq hq0 hE hk
  have hS := abs_backward_sum_le (g := g) hq hA hB hθ hl0 (K - k)
    (fun i hi => hg (k + i) (by omega) (by omega))
    (fun i hi => by
      have := hl (k + i) (by omega) (by omega)
      rwa [show k + i - k = i by omega] at this)
  have : E k - E K / q ^ (K - k) = -∑ i ∈ range (K - k), g (k + i) / q ^ (i + 1) := by
    rw [hb]; ring
  rw [this, abs_neg]
  exact hS

/-- **The vacuum bound in the normalization `E_K = 0`**: `|E_k| ≤ C' λ_k + C'` for every
`k ≤ K`, with `C' = (A + B)/(q - 1) + A θ/(q - 1)²` independent of `k` and `K`. -/
theorem abs_vacuum_le_of_final_eq_zero (hq : 1 < q)
    (hE : ∀ j, j < K → E (j + 1) = q * E j + g j) (hEK : E K = 0) {k : ℕ} (hk : k ≤ K)
    {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ) {lam : ℕ → ℝ} (hl0 : 0 ≤ lam k)
    (hg : ∀ j, k ≤ j → j < K → |g j| ≤ A * lam j + B)
    (hl : ∀ j, k ≤ j → j < K → lam j ≤ lam k + ((j - k : ℕ) : ℝ) * θ) :
    |E k| ≤ ((A + B) / (q - 1) + A * θ / (q - 1) ^ 2) * lam k +
      ((A + B) / (q - 1) + A * θ / (q - 1) ^ 2) := by
  have h := abs_vacuum_backward_le hq hE hk hA hB hθ hl0 hg hl
  rw [hEK, zero_div, sub_zero] at h
  have hq1 : 0 < q - 1 := by linarith
  have ha : 0 ≤ A / (q - 1) := div_nonneg hA hq1.le
  have hb : 0 ≤ B / (q - 1) := div_nonneg hB hq1.le
  have hc : 0 ≤ A * θ / (q - 1) ^ 2 := by positivity
  have hsplit : (A * lam k + B) / (q - 1) = A / (q - 1) * lam k + B / (q - 1) := by
    field_simp
  rw [hsplit] at h
  have hsplit2 : (A + B) / (q - 1) = A / (q - 1) + B / (q - 1) := by rw [add_div]
  rw [hsplit2]
  nlinarith [mul_nonneg hb hl0, mul_nonneg hc hl0]

/-- **The deviation from the backward solution grows like `q^k`**: for every solution,
`E_k + ∑_{i<K-k} g_{k+i}/q^{i+1} = q^k (E_0 + ∑_{i<K} g_i/q^{i+1})` for `k ≤ K`. -/
theorem vacuum_sub_backward_eq (hq : q ≠ 0) (hE : ∀ j, j < K → E (j + 1) = q * E j + g j)
    {k : ℕ} (hk : k ≤ K) :
    E k + ∑ i ∈ range (K - k), g (k + i) / q ^ (i + 1) =
      q ^ k * (E 0 + ∑ i ∈ range K, g i / q ^ (i + 1)) := by
  have h1 := vacuum_backward_eq hq hE hk
  have h0 := vacuum_backward_eq hq hE (Nat.zero_le K)
  simp only [zero_add, Nat.sub_zero] at h0
  have e1 : E k + ∑ i ∈ range (K - k), g (k + i) / q ^ (i + 1) = E K / q ^ (K - k) := by
    rw [h1]; ring
  have e0 : E 0 + ∑ i ∈ range K, g i / q ^ (i + 1) = E K / q ^ K := by
    rw [h0]; ring
  rw [e1, e0]
  have hK : q ^ K = q ^ k * q ^ (K - k) := by rw [← pow_add]; congr 1; omega
  rw [hK]
  have : q ^ k ≠ 0 := pow_ne_zero _ hq
  have : q ^ (K - k) ≠ 0 := pow_ne_zero _ hq
  field_simp

/-- **A bound at the last scale pins the initial constant**: if `|E_K| ≤ M` then
`|E_0 - E*_0| ≤ M / q^K`, `E*_0 = -∑_{i<K} g_i / q^{i+1}` the initial value of the backward
solution (`E*_K = 0`). -/
theorem abs_vacuum_init_sub_le (hq : 0 < q) (hE : ∀ j, j < K → E (j + 1) = q * E j + g j)
    {M : ℝ} (hM : |E K| ≤ M) :
    |E 0 - -∑ i ∈ range K, g i / q ^ (i + 1)| ≤ M / q ^ K := by
  have h0 := vacuum_backward_eq hq.ne' hE (Nat.zero_le K)
  simp only [zero_add, Nat.sub_zero] at h0
  have : E 0 - -∑ i ∈ range K, g i / q ^ (i + 1) = E K / q ^ K := by rw [h0]; ring
  rw [this, abs_div, abs_of_pos (pow_pos hq K)]
  exact div_le_div_of_nonneg_right hM (pow_pos hq K).le

end Balaban.Fluctuation.VacuumFlow
