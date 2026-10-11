/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The summation lemma (CORRELATIONS.md, Lemma 1.3)

Conditional development of Root-C: the series estimate used by the consequences of the clauses of
Root-F.  For `σ, a > 0` and `L > 1` there is `C` with
`∑_{j<J} L^{-jσ} exp(-a r / L^j) ≤ C (1 + r)^{-σ}` for all `J` and `r ≥ 0`.  The proof is an
induction on `J` through the shift `F_{J+1}(r) = e^{-a r} + L^{-σ} F_J(r / L)`.
-/

@[expose] public section

open Filter Topology

namespace Balaban.Correlations

/-- `(1 + r)^p e^{-a r}` is bounded on `r ≥ 0`. -/
theorem exists_bound_rpow_mul_exp (p a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ r : ℝ, 0 ≤ r → (1 + r) ^ p * Real.exp (-(a * r)) ≤ K := by
  set f : ℝ → ℝ := fun r => (1 + r) ^ p * Real.exp (-(a * r)) with hf
  have hcont : ContinuousOn f (Set.Ici 0) := by
    refine ContinuousOn.mul ?_ (by fun_prop)
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    exact ((Real.continuousAt_rpow_const (1 + x) p (Or.inl (by positivity))).comp
      (show ContinuousAt (fun x : ℝ => 1 + x) x by fun_prop)).continuousWithinAt
  have ht : Tendsto f atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have h2 := h1.const_mul (Real.exp a)
    rw [mul_zero] at h2
    refine h2.congr fun r => ?_
    simp only [Function.comp, hf]
    rw [mul_left_comm, ← Real.exp_add]
    simp only [id]
    congr 2
    ring_nf
  obtain ⟨R, hR⟩ := eventually_atTop.1 ((ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max R 0)).exists_bound_of_continuousOn
    (hcont.mono (fun x hx => hx.1))
  refine ⟨max C 1, le_max_right _ _, fun r hr => ?_⟩
  by_cases hrR : r ≤ max R 0
  · exact (le_trans (le_abs_self _) (hC r ⟨hr, hrR⟩)).trans (le_max_left _ _)
  · have := hR r (le_of_lt (lt_of_le_of_lt (le_max_left _ _) (not_le.1 hrR)))
    exact this.le.trans (le_max_right _ _)

/-- `1 - y^σ ≥ c₀ (1 - y)` on `[0, 1]`, with `c₀ = min 1 σ`. -/
theorem one_sub_rpow_ge {σ : ℝ} (hσ : 0 < σ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    min 1 σ * (1 - y) ≤ 1 - y ^ σ := by
  rcases le_or_gt 1 σ with h | h
  · rw [min_eq_left h]
    rcases hy0.eq_or_lt with rfl | hy
    · simp [Real.zero_rpow hσ.ne']
    · have := Real.rpow_le_rpow_of_exponent_ge hy hy1 h
      rw [Real.rpow_one] at this
      linarith
  · rw [min_eq_right h.le]
    have := rpow_one_add_le_one_add_mul_self (s := y - 1) (by linarith) hσ.le h.le
    simp only [add_sub_cancel] at this
    nlinarith

/-- Lemma 1.3 (summation lemma). -/
theorem sum_pow_exp_le {σ a L : ℝ} (hσ : 0 < σ) (ha : 0 < a) (hL : 1 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : ℕ) (r : ℝ), 0 ≤ r →
      ∑ j ∈ Finset.range J, L ^ (-((j : ℝ) * σ)) * Real.exp (-(a * r / L ^ j)) ≤
        C * (1 + r) ^ (-σ) := by
  obtain ⟨K, hK1, hK⟩ := exists_bound_rpow_mul_exp (σ + 1) a ha
  have hL0 : 0 < L := by linarith
  set c0 := min 1 σ with hc0
  have hc0pos : 0 < c0 := lt_min one_pos hσ
  set C := L * K / (c0 * (L - 1)) with hC
  have hCnn : 0 ≤ C := by
    have : 0 < L - 1 := by linarith
    positivity
  refine ⟨C, hCnn, fun J => ?_⟩
  induction J with
  | zero => intro r hr; simp; positivity
  | succ J ih =>
    intro r hr
    rw [Finset.sum_range_succ']
    have hshift : ∑ j ∈ Finset.range J, L ^ (-(((j + 1 : ℕ) : ℝ) * σ)) *
          Real.exp (-(a * r / L ^ (j + 1))) =
        L ^ (-σ) * ∑ j ∈ Finset.range J, L ^ (-((j : ℝ) * σ)) *
          Real.exp (-(a * (r / L) / L ^ j)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : L ^ (-(((j + 1 : ℕ) : ℝ) * σ)) = L ^ (-σ) * L ^ (-((j : ℝ) * σ)) := by
        rw [← Real.rpow_add hL0]
        congr 1
        push_cast
        ring
      rw [this, mul_assoc]
      congr 3
      field_simp
      ring
    rw [hshift]
    have h1 := ih (r / L) (by positivity)
    have h2 : L ^ (-σ) * (C * (1 + r / L) ^ (-σ)) = C * (L + r) ^ (-σ) := by
      have : (1 + r / L) = (L + r) / L := by field_simp
      rw [this, Real.div_rpow (by positivity) hL0.le]
      have : L ^ (-σ) ≠ 0 := (Real.rpow_pos_of_pos hL0 _).ne'
      field_simp
    have h3 : L ^ (-σ) * ∑ j ∈ Finset.range J, L ^ (-((j : ℝ) * σ)) *
          Real.exp (-(a * (r / L) / L ^ j)) ≤ C * (L + r) ^ (-σ) := by
      rw [← h2]
      exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hL0.le _)
    -- the key inequality
    have hr1 : 0 < 1 + r := by linarith
    have hLr : 0 < L + r := by linarith
    set y := (1 + r) / (L + r) with hy
    have hy0 : 0 ≤ y := by positivity
    have hy1 : y ≤ 1 := by rw [hy, div_le_one hLr]; linarith
    have hyσ : (L + r) ^ (-σ) = (1 + r) ^ (-σ) * y ^ σ := by
      rw [hy, Real.div_rpow hr1.le hLr.le, Real.rpow_neg hLr.le, Real.rpow_neg hr1.le]
      field_simp
    have h4 := one_sub_rpow_ge hσ hy0 hy1
    have h5 : 1 - y = (L - 1) / (L + r) := by rw [hy]; field_simp; ring
    have hexp : Real.exp (-(a * r)) * ((1 + r) ^ σ * (L + r)) ≤ L * K := by
      have : (L + r) ≤ L * (1 + r) := by nlinarith
      have h6 := hK r hr
      have h7 : (1 + r) ^ (σ + 1) = (1 + r) ^ σ * (1 + r) := by
        rw [Real.rpow_add hr1, Real.rpow_one]
      calc Real.exp (-(a * r)) * ((1 + r) ^ σ * (L + r))
          ≤ Real.exp (-(a * r)) * ((1 + r) ^ σ * (L * (1 + r))) := by gcongr
        _ = L * ((1 + r) ^ (σ + 1) * Real.exp (-(a * r))) := by rw [h7]; ring
        _ ≤ L * K := by gcongr
    have hgoal : Real.exp (-(a * r)) ≤ C * ((1 + r) ^ (-σ) - (L + r) ^ (-σ)) := by
      have hD : (1 + r) ^ (-σ) - (L + r) ^ (-σ) = (1 + r) ^ (-σ) * (1 - y ^ σ) := by
        rw [hyσ]; ring
      rw [hD]
      have hpos : 0 < (1 + r) ^ (-σ) := Real.rpow_pos_of_pos hr1 _
      have hL1 : 0 < L - 1 := by linarith
      have h8 : c0 * ((L - 1) / (L + r)) ≤ 1 - y ^ σ := by rw [h5] at h4; exact h4
      calc Real.exp (-(a * r)) = Real.exp (-(a * r)) * ((1 + r) ^ σ * (L + r)) *
            ((1 + r) ^ (-σ) * (1 / (L + r))) := by
              rw [Real.rpow_neg hr1.le]; field_simp
        _ ≤ L * K * ((1 + r) ^ (-σ) * (1 / (L + r))) := by gcongr
        _ = C * ((1 + r) ^ (-σ) * (c0 * ((L - 1) / (L + r)))) := by
              rw [hC]; field_simp
        _ ≤ C * ((1 + r) ^ (-σ) * (1 - y ^ σ)) := by gcongr
    have h9 : L ^ (-((0 : ℕ) : ℝ) * σ) = 1 := by simp
    have h10 : L ^ (-(((0 : ℕ) : ℝ) * σ)) * Real.exp (-(a * r / L ^ 0)) = Real.exp (-(a * r)) := by
      simp
    rw [h10]
    linarith

end Balaban.Correlations
