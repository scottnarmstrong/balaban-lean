/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Xi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scale ratio of P7 (2.11) (P631-INPUTS-2 §2.1)

For `ε_j = α₀ q_j L^{-αj}` (`epsSeq`, `1 ≤ q_j < 3`) and couplings
`β_m = B L^{(d-2)m} g_m` (P4 (H.6), `Flow.betaSeq_eq`) with `e^{-η} ≤ g_m ≤ e^{η}`
(`Flow.norm_gammaSeq_le`), and `d - 2 - 2α = 2γ`,
`β_{j+1} ε_{j+1}² / (β_n ε_n²) ≤ 9 e^{2η} (L^{-2γ})^{n-j-1}` (`p631_ratio_free`), while the
constant `1` is false (`p631_ratio_one_counterexample`, `j = 1`, `n = 3`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.SmallField

theorem one_le_epsTail (j : ℕ) : 1 ≤ epsTail j := by
  unfold epsTail
  have : 0 ≤ ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
    tsum_nonneg fun m => by split_ifs <;> positivity
  linarith

theorem epsTail_lt_three (j : ℕ) : epsTail j < 3 := by
  unfold epsTail
  have hz : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hle : ∑' m : ℕ, (if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0) ≤ Real.pi ^ 2 / 6 := by
    rw [← hz.tsum_eq]
    refine Summable.tsum_le_tsum (fun m => ?_) (summable_epsTail j) hz.summable
    split_ifs <;> simp
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

theorem epsTail_two_sub_three : epsTail 2 - epsTail 3 = 1 / 4 := by
  unfold epsTail
  have h := (summable_epsTail 2).hasSum.sub (summable_epsTail 3).hasSum
  have h2 : (fun m : ℕ => (if 2 ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0) -
      (if 3 ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0)) = fun m => if m = 2 then (1 / 4 : ℝ) else 0 := by
    funext m
    by_cases h2 : m = 2
    · subst h2; norm_num
    · by_cases h3 : 3 ≤ m
      · have : 2 ≤ m := by omega
        simp [h2, h3, this]
      · have : ¬ 2 ≤ m := by omega
        simp [h2, h3, this]
  rw [h2] at h
  have := h.tsum_eq
  rw [tsum_ite_eq] at this
  linarith

/-- The pure scale factor: with `d - 2 - 2α = 2γ`,
`L^{(d-2)(j+1)} L^{-2α(j+1)} / (L^{(d-2)n} L^{-2αn}) = (L^{-2γ})^{n-j-1}`. -/
theorem scale_factor (L d : ℕ) (hL : 1 < L) (hd : 2 ≤ d) (α γ : ℝ)
    (hγ : (d : ℝ) - 2 - 2 * α = 2 * γ) (m : ℕ) :
    ((L : ℝ) ^ ((d - 2) * (m)) * ((L : ℝ) ^ (-α)) ^ (2 * m))⁻¹ =
      ((L : ℝ) ^ (-(2 * γ))) ^ m := by
  have hx : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have e : (L : ℝ) ^ (-(2 * γ)) =
      ((L : ℝ) ^ (d - 2) * ((L : ℝ) ^ (-α)) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast ((L : ℝ) ^ (-α)), ← Real.rpow_mul hx.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hx]
    · rw [← Real.rpow_mul (by positivity)]
      congr 1
      have : (((d - 2 : ℕ) : ℝ)) = (d : ℝ) - 2 := by
        rw [Nat.cast_sub hd]; norm_num
      push_cast [this]
      linarith
  rw [e, inv_pow, mul_pow, ← pow_mul, ← pow_mul]

/-- The free-flow coupling `β_m = B L^{(d-2)m} g_m` (P4 (H.6)). -/
theorem ratio_eq (L d : ℕ) (hL : 1 < L) (hd : 2 ≤ d) (α α₀ γ B : ℝ) (hα₀ : 0 < α₀) (hB : 0 < B)
    (hγ : (d : ℝ) - 2 - 2 * α = 2 * γ) (g : ℕ → ℝ) (hg : ∀ m, 0 < g m) (j m : ℕ) :
    (B * (L : ℝ) ^ ((d - 2) * (j + 1)) * g (j + 1) * epsSeq L α α₀ (j + 1) ^ 2) /
      (B * (L : ℝ) ^ ((d - 2) * (j + 1 + m)) * g (j + 1 + m) * epsSeq L α α₀ (j + 1 + m) ^ 2) =
    (g (j + 1) / g (j + 1 + m)) * (epsTail (j + 1) / epsTail (j + 1 + m)) ^ 2 *
      ((L : ℝ) ^ (-(2 * γ))) ^ m := by
  have hx : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  rw [← scale_factor L d hL hd α γ hγ m]
  have hu : (0 : ℝ) < (L : ℝ) ^ (-α) := Real.rpow_pos_of_pos hx _
  have h1 := epsTail_pos (j + 1)
  have h2 := epsTail_pos (j + 1 + m)
  have h3 := hg (j + 1)
  have h4 := hg (j + 1 + m)
  unfold epsSeq
  have e1 : (L : ℝ) ^ ((d - 2) * (j + 1 + m)) =
      (L : ℝ) ^ ((d - 2) * (j + 1)) * (L : ℝ) ^ ((d - 2) * m) := by
    rw [← pow_add]; congr 1; ring
  have e2 : ((L : ℝ) ^ (-α)) ^ (j + 1 + m) = ((L : ℝ) ^ (-α)) ^ (j + 1) * ((L : ℝ) ^ (-α)) ^ m :=
    pow_add _ _ _
  have e3 : ((L : ℝ) ^ (-α)) ^ (2 * m) = (((L : ℝ) ^ (-α)) ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm]
  rw [e1, e2, e3]
  have hX : 0 < (L : ℝ) ^ ((d - 2) * (j + 1)) := by positivity
  have hY : 0 < (L : ℝ) ^ ((d - 2) * m) := by positivity
  have hU : 0 < ((L : ℝ) ^ (-α)) ^ (j + 1) := by positivity
  have hV : 0 < ((L : ℝ) ^ (-α)) ^ m := by positivity
  field_simp

/-- **The true ratio** (P7 (2.11) second inequality, P631-INPUTS-2 (2.1)): for
`β_m = B L^{(d-2)m} g_m`, `e^{-η} ≤ g_m ≤ e^{η}`, `ε = epsSeq L α α₀`, `d - 2 - 2α = 2γ`, `j + 1 ≤ n`:
`β_{j+1} ε_{j+1}² / (β_n ε_n²) ≤ 9 e^{2η} (L^{-2γ})^{n-j-1}`. -/
theorem p631_ratio_free (L d : ℕ) (hL : 1 < L) (hd : 2 ≤ d) (α α₀ γ B η : ℝ) (hα₀ : 0 < α₀)
    (hB : 0 < B) (hγ : (d : ℝ) - 2 - 2 * α = 2 * γ) (g : ℕ → ℝ)
    (hg : ∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η) {j n : ℕ} (hjn : j + 1 ≤ n) :
    (B * (L : ℝ) ^ ((d - 2) * (j + 1)) * g (j + 1) * epsSeq L α α₀ (j + 1) ^ 2) /
      (B * (L : ℝ) ^ ((d - 2) * n) * g n * epsSeq L α α₀ n ^ 2) ≤
    9 * Real.exp (2 * η) * ((L : ℝ) ^ (-(2 * γ))) ^ (n - j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + 1 + m := ⟨n - (j + 1), by omega⟩
  have hgp : ∀ m, 0 < g m := fun m => lt_of_lt_of_le (Real.exp_pos _) (hg m).1
  rw [ratio_eq L d hL hd α α₀ γ B hα₀ hB hγ g hgp j m, show j + 1 + m - j - 1 = m by omega]
  have hx : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hq : 0 < ((L : ℝ) ^ (-(2 * γ))) ^ m := by positivity
  have hq1 := epsTail_pos (j + 1)
  have hq2 := one_le_epsTail (j + 1 + m)
  have hgr : g (j + 1) / g (j + 1 + m) ≤ Real.exp (2 * η) := by
    rw [div_le_iff₀ (hgp _)]
    have h1 := (hg (j + 1)).2
    have h2 := (hg (j + 1 + m)).1
    have : Real.exp (2 * η) * Real.exp (-η) = Real.exp η := by
      rw [← Real.exp_add]; congr 1; ring
    calc g (j + 1) ≤ Real.exp η := h1
      _ = Real.exp (2 * η) * Real.exp (-η) := this.symm
      _ ≤ Real.exp (2 * η) * g (j + 1 + m) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hqr : (epsTail (j + 1) / epsTail (j + 1 + m)) ^ 2 ≤ 9 := by
    have h3 := epsTail_lt_three (j + 1)
    have : epsTail (j + 1) / epsTail (j + 1 + m) ≤ 3 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have : 0 ≤ epsTail (j + 1) / epsTail (j + 1 + m) := by positivity
    nlinarith
  have hgpos : 0 ≤ g (j + 1) / g (j + 1 + m) := (div_pos (hgp _) (hgp _)).le
  have hqpos : 0 ≤ (epsTail (j + 1) / epsTail (j + 1 + m)) ^ 2 := by positivity
  calc g (j + 1) / g (j + 1 + m) * (epsTail (j + 1) / epsTail (j + 1 + m)) ^ 2 *
        ((L : ℝ) ^ (-(2 * γ))) ^ m
      ≤ (Real.exp (2 * η) * 9) * ((L : ℝ) ^ (-(2 * γ))) ^ m := by
        apply mul_le_mul_of_nonneg_right _ hq.le
        exact mul_le_mul hgr hqr hqpos (Real.exp_pos _).le
    _ = _ := by ring

/-- **The constant-one ratio is false** (P631-INPUTS-2 §2.1; `j = 1`, `n = 3`): for the free flow
`β_m = B L^{(d-2)m}` and `ε = epsSeq L α α₀`, the ratio strictly exceeds `(L^{-2γ})^{n-j-1}`. So
the retired field `p7_ratio` (constant `1`) is unsatisfiable at the actual sequences. -/
theorem p631_ratio_one_counterexample (L d : ℕ) (hL : 1 < L) (hd : 2 ≤ d) (α α₀ γ B : ℝ)
    (hα₀ : 0 < α₀) (hB : 0 < B) (hγ : (d : ℝ) - 2 - 2 * α = 2 * γ) :
    ((L : ℝ) ^ (-(2 * γ))) ^ (3 - 1 - 1) <
    (B * (L : ℝ) ^ ((d - 2) * (1 + 1)) * 1 * epsSeq L α α₀ (1 + 1) ^ 2) /
      (B * (L : ℝ) ^ ((d - 2) * (1 + 1 + 1)) * 1 * epsSeq L α α₀ (1 + 1 + 1) ^ 2) := by
  have h := ratio_eq L d hL hd α α₀ γ B hα₀ hB hγ (fun _ => 1) (fun _ => one_pos) 1 1
  have hx : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  simp only [show 3 - 1 - 1 = 1 by rfl]
  rw [h]
  have hq : 0 < ((L : ℝ) ^ (-(2 * γ))) := by positivity
  have h23 : epsTail 2 - epsTail 3 = 1 / 4 := epsTail_two_sub_three
  have h3 := epsTail_pos 3
  have : 1 < epsTail (1 + 1) / epsTail (1 + 1 + 1) := by
    rw [lt_div_iff₀ (by simpa using h3)]; simpa using (by linarith : epsTail 3 < epsTail 2)
  simp only [div_self (one_pos.ne'), one_mul, pow_one]
  have h1 : 1 < (epsTail (1 + 1) / epsTail (1 + 1 + 1)) ^ 2 := by nlinarith
  nlinarith

end Balaban.LargeField.ActionConv
