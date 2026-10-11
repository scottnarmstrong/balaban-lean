/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.Loc
public import Balaban.Green.Lattice.LocSums

/-!
# Sums of the lattice Green's function over sets of bounded cardinality

For a finite set `A ⊂ ℤ^d` with at most as many points as the ball `B_R(0)`:

* `∑_{z ∈ A} C(-z) ≤ c_G (R + 1)²`,
* `∑_{z ∈ A} |C(-z + e_ν) - C(-z)| ≤ c_G (R + 1)`,

with `c_G = c_G(d)` (consequences of Lemma K and the rearrangement `sum_translate_le`).
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

theorem green_sum_le (hd : 3 ≤ d) :
    ∃ cG : ℝ, 0 ≤ cG ∧ ∀ (R : ℝ), 0 ≤ R → ∀ (A : Finset (Fin d → ℤ)),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card →
      (∑ z ∈ A, latticeGreen d (0 - z) ≤ cG * (R + 1) ^ 2) ∧
      (∀ ν : Fin d, ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)| ≤
        cG * (R + 1)) := by
  obtain ⟨c0, hc0, h0⟩ := latticeGreen_le hd
  obtain ⟨c1, hc1, h1⟩ := latticeGreen_diff1_le hd
  have hd1 : 1 ≤ d := by omega
  refine ⟨max c0 c1 * (d * 2 ^ d), by positivity, fun R hR A hA => ⟨?_, fun ν => ?_⟩⟩
  · have hφ := sum_translate_le (fun r => c0 * (1 / (1 + r) ^ (d - 2)))
      (fun r hr => by positivity)
      (fun r r' hr hrr => by
        have : (1 + r) ^ (d - 2) ≤ (1 + r') ^ (d - 2) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
        have h2 : 0 < (1 + r) ^ (d - 2) := by positivity
        have := one_div_le_one_div_of_le h2 this
        exact mul_le_mul_of_nonneg_left this hc0) hR A hA 0
    have hs := sum_ball_pow_le hd1 (p := 2) (by norm_num) (by omega) hR
    calc ∑ z ∈ A, latticeGreen d (0 - z) ≤ ∑ z ∈ A, c0 * (1 / (1 + ‖0 - z‖) ^ (d - 2)) :=
          Finset.sum_le_sum fun z _ => by
            rw [mul_one_div]; exact h0 _
      _ ≤ ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, c0 * (1 / (1 + ‖w‖) ^ (d - 2)) := hφ
      _ = c0 * ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, 1 / (1 + ‖w‖) ^ (d - 2) := by
          rw [Finset.mul_sum]
      _ ≤ c0 * (d * 2 ^ d * (R + 1) ^ 2) := mul_le_mul_of_nonneg_left hs hc0
      _ ≤ _ := by
          have : c0 ≤ max c0 c1 := le_max_left _ _
          have h3 : 0 ≤ (d : ℝ) * 2 ^ d * (R + 1) ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right this h3]
  · have hφ := sum_translate_le (fun r => c1 * (1 / (1 + r) ^ (d - 1)))
      (fun r hr => by positivity)
      (fun r r' hr hrr => by
        have : (1 + r) ^ (d - 1) ≤ (1 + r') ^ (d - 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
        have h2 : 0 < (1 + r) ^ (d - 1) := by positivity
        have := one_div_le_one_div_of_le h2 this
        exact mul_le_mul_of_nonneg_left this hc1) hR A hA 0
    have hs := sum_ball_pow_le hd1 (p := 1) le_rfl (by omega) hR
    calc ∑ z ∈ A, |latticeGreen d (0 - z + Pi.single ν 1) - latticeGreen d (0 - z)|
        ≤ ∑ z ∈ A, c1 * (1 / (1 + ‖0 - z‖) ^ (d - 1)) :=
          Finset.sum_le_sum fun z _ => by
            rw [mul_one_div]; exact h1 _ ν
      _ ≤ ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, c1 * (1 / (1 + ‖w‖) ^ (d - 1)) := hφ
      _ = c1 * ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, 1 / (1 + ‖w‖) ^ (d - 1) := by
          rw [Finset.mul_sum]
      _ ≤ c1 * (d * 2 ^ d * (R + 1) ^ 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hc1
          simpa using hs
      _ ≤ _ := by
          have : c1 ≤ max c0 c1 := le_max_right _ _
          have h3 : 0 ≤ (d : ℝ) * 2 ^ d * (R + 1) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right this h3]

end Balaban.LatticeGreen
