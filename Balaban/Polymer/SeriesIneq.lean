module

public import Mathlib

/-!
# An exponential inequality for sequences with a convolution recursion

If `s ≥ 0` and `z` solves `(n+1) z_{n+1} = ∑_{m ≤ n} (m+1) s_{m+1} z_{n-m}`, `z_0 = 1`, then
`∑_{n ≤ M} z_n ≤ exp (∑_{m ≤ M} s_m)`.  This is the inequality half of the exponential formula.
-/

@[expose] public section

noncomputable section

open Polynomial Finset

namespace Balaban.Polymer

theorem eval_le_of_coeff_le {p q : ℝ[X]} (h : ∀ n, p.coeff n ≤ q.coeff n) {x : ℝ} (hx : 0 ≤ x) :
    p.eval x ≤ q.eval x := by
  have hN : ∃ N, p.natDegree < N ∧ q.natDegree < N := ⟨max p.natDegree q.natDegree + 1, by omega, by omega⟩
  obtain ⟨N, hp, hq⟩ := hN
  rw [eval_eq_sum_range' hp, eval_eq_sum_range' hq]
  exact sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (h n) (pow_nonneg hx n))

theorem exp_ineq (s z : ℕ → ℝ) (hs : ∀ m, 0 ≤ s m) (hz0 : z 0 = 1)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 1) * z (n + 1) =
      ∑ m ∈ range (n + 1), ((m : ℝ) + 1) * s (m + 1) * z (n - m)) (M : ℕ) :
    ∑ n ∈ range (M + 1), z n ≤ Real.exp (∑ m ∈ range M, s (m + 1)) := by
  have hz : ∀ n, 0 ≤ z n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · rw [hz0]; exact zero_le_one
      · have h1 : 0 ≤ ((n : ℝ) + 1) * z (n + 1) := by
          rw [hrec n]
          refine sum_nonneg (fun m hm => ?_)
          have := ih (n - m) (by omega)
          have := hs (m + 1)
          positivity
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        exact nonneg_of_mul_nonneg_right h1 hn
  set Q : ℝ[X] := ∑ n ∈ range (M + 1), C (z n) * X ^ n with hQ
  set S : ℝ[X] := ∑ m ∈ range M, C (s (m + 1)) * X ^ (m + 1) with hS
  have hQc : ∀ k, Q.coeff k = if k ≤ M then z k else 0 := by
    intro k
    rw [hQ, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hk : k ≤ M
    · rw [sum_eq_single k]
      · simp [hk]
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    · simp only [hk, ↓reduceIte]
      exact sum_eq_zero (fun b hb => by
        have : b ≠ k := by have := mem_range.mp hb; omega
        simp [Ne.symm this])
  have hSc : ∀ k, S.coeff k = if 1 ≤ k ∧ k ≤ M then s k else 0 := by
    intro k
    rw [hS, finsetSum_coeff]
    simp only [coeff_C_mul, coeff_X_pow]
    by_cases hk : 1 ≤ k ∧ k ≤ M
    · rw [sum_eq_single (k - 1)]
      · simp [hk, Nat.sub_add_cancel hk.1]
      · intro b _ hb
        have : k ≠ b + 1 := by omega
        simp [this]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    · simp only [hk, ↓reduceIte]
      refine sum_eq_zero (fun b hb => ?_)
      have : k ≠ b + 1 := by have := mem_range.mp hb; omega
      simp [this]
  have hQnn : ∀ k, 0 ≤ Q.coeff k := by
    intro k; rw [hQc]; split_ifs
    · exact hz k
    · exact le_refl _
  have hSnn : ∀ k, 0 ≤ S.coeff k := by
    intro k; rw [hSc]; split_ifs
    · exact hs k
    · exact le_refl _
  have hcoef : ∀ n, (derivative Q).coeff n ≤ (derivative S * Q).coeff n := by
    intro n
    rw [coeff_derivative, coeff_mul]
    have hprod : ∀ p ∈ antidiagonal n, 0 ≤ (derivative S).coeff p.1 * Q.coeff p.2 := by
      intro p _
      rw [coeff_derivative]
      exact mul_nonneg (mul_nonneg (hSnn _) (by positivity)) (hQnn _)
    by_cases hn : n + 1 ≤ M
    · have : Q.coeff (n + 1) * ((n : ℝ) + 1) =
          ∑ p ∈ antidiagonal n, (derivative S).coeff p.1 * Q.coeff p.2 := by
        rw [hQc, ite_eq_left_of_eq_true _ _ (eq_true hn), mul_comm, hrec n, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        refine sum_congr rfl (fun m hm => ?_)
        have hm' := mem_range.mp hm
        rw [coeff_derivative, hSc, hQc, ite_eq_left_of_eq_true _ _ (eq_true (⟨by omega, by omega⟩ : 1 ≤ m + 1 ∧ m + 1 ≤ M)),
          ite_eq_left_of_eq_true _ _ (eq_true (by omega : n - m ≤ M))]
        push_cast; ring
      rw [this]
    · have : Q.coeff (n + 1) = 0 := by rw [hQc]; simp only [hn, ↓reduceIte]
      rw [this, zero_mul]
      exact sum_nonneg hprod
  have hder : ∀ x, 0 ≤ x → (derivative Q).eval x ≤ (derivative S).eval x * Q.eval x := by
    intro x hx
    rw [mul_comm, ← eval_mul]
    exact eval_le_of_coeff_le (by simpa [mul_comm] using hcoef) hx
  set g : ℝ → ℝ := fun x => Q.eval x * Real.exp (-S.eval x) with hg
  have hgd : ∀ x, HasDerivAt g ((derivative Q).eval x * Real.exp (-S.eval x) +
      Q.eval x * (Real.exp (-S.eval x) * (-(derivative S).eval x))) x := by
    intro x
    exact (Q.hasDerivAt x).mul ((S.hasDerivAt x).neg.exp)
  have hanti : AntitoneOn g (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun x _ => (hgd x).continuousAt.continuousWithinAt)
      (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hgd x).deriv]
    have h1 := hder x (le_of_lt hx)
    have h2 := Real.exp_pos (-S.eval x)
    nlinarith
  have h10 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  have hQ0 : Q.eval 0 = 1 := by rw [← coeff_zero_eq_eval_zero, hQc]; simp [hz0]
  have hS0 : S.eval 0 = 0 := by rw [← coeff_zero_eq_eval_zero, hSc]; simp
  have hQ1 : Q.eval 1 = ∑ n ∈ range (M + 1), z n := by simp [hQ, eval_finsetSum]
  have hS1 : S.eval 1 = ∑ m ∈ range M, s (m + 1) := by simp [hS, eval_finsetSum]
  simp only [hg, hQ0, hS0, hQ1, hS1, neg_zero, Real.exp_zero, mul_one] at h10
  have h3 := Real.exp_pos (∑ m ∈ range M, s (m + 1))
  have h4 : (∑ n ∈ range (M + 1), z n) * Real.exp (-∑ m ∈ range M, s (m + 1)) ≤ 1 := h10
  rw [Real.exp_neg] at h4
  rwa [← div_eq_mul_inv, div_le_one h3] at h4

end Balaban.Polymer
