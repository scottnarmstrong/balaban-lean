/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectWholeSum

/-!
# Weighted polymer counts in the winding-tail estimate

The existing rooted count controls the weight `|X|² (1+t)⁶ exp(-(κ-1)t)`.
Using half the covering radius in `norm_sum_winding_le` converts that count into its
exponential counting premise while retaining the original decay rate `κ`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.SmallField

/-- A rooted polymer of nonnegative covering size has counting weight at least its
exponential factor. -/
theorem exp_le_wt_of_root {d : ℕ} (X : Finset (Site d)) {t κ : ℝ}
    (hroot : X.Nonempty) (ht : 0 ≤ t) :
    Real.exp (-(κ - 1) * t) ≤ wt κ X t := by
  have hc : (1 : ℝ) ≤ X.card := by
    exact_mod_cast Finset.card_pos.mpr hroot
  have hc2 : (1 : ℝ) ≤ (X.card : ℝ) ^ 2 := by nlinarith
  have ht6 : (1 : ℝ) ≤ (1 + t) ^ 6 := one_le_pow₀ (by linarith)
  have hprod : (1 : ℝ) ≤ (X.card : ℝ) ^ 2 * (1 + t) ^ 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sub_nonneg.mpr ht6)]
  unfold wt
  simpa only [one_mul, mul_assoc] using
    (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le)

/-- The weighted count closes the exact numerical hypotheses of `norm_sum_winding_le`.
The polynomial factor costs `16` under the half-radius substitution; the final threshold
is `exp(-τ/2)`. -/
theorem norm_sum_winding_le_of_wt_count {d : ℕ}
    (S : Finset (Finset (Site d))) (t : Finset (Site d) → ℝ)
    (f : Finset (Site d) → ℂ) {M E₀ κ τ K₀ : ℝ}
    (hM : 0 ≤ M) (hE₀ : 0 ≤ E₀)
    (ht₀ : ∀ X ∈ S, 0 ≤ t X) (htτ : ∀ X ∈ S, τ ≤ t X)
    (hroot : ∀ X ∈ S, X.Nonempty)
    (hf : ∀ X ∈ S,
      ‖f X‖ ≤ M * E₀ * (1 + t X) ^ 4 * Real.exp (-κ * t X))
    (hcount : ∑ X ∈ S, wt κ X (t X) ≤ K₀) :
    ‖∑ X ∈ S, f X‖ ≤
      24 * Real.exp 1 * (16 * M) * E₀ * Real.exp (-(τ / 2)) * K₀ := by
  apply norm_sum_winding_le S (fun X => t X / 2) f
    (M := 16 * M) (E₀ := E₀) (κ := 2 * κ) (κ₀ := 2 * (κ - 1))
    (τ := τ / 2) (K₀ := K₀) (by positivity) hE₀ (by nlinarith)
  · intro X hX
    have := ht₀ X hX
    linarith
  · intro X hX
    have := htτ X hX
    linarith
  · intro X hX
    have ht := ht₀ X hX
    have hp : (1 + t X) ^ 4 ≤ 16 * (1 + t X / 2) ^ 4 := by
      have h : 1 + t X ≤ 2 * (1 + t X / 2) := by linarith
      have h' := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + t X) h 4
      convert h' using 1
      ring
    have he : Real.exp (-κ * t X) = Real.exp (-(2 * κ) * (t X / 2)) := by
      congr 1
      ring
    calc
      ‖f X‖ ≤ M * E₀ * (1 + t X) ^ 4 * Real.exp (-κ * t X) := hf X hX
      _ ≤ (16 * M) * E₀ * (1 + t X / 2) ^ 4 *
          Real.exp (-(2 * κ) * (t X / 2)) := by
        rw [← he]
        have h' : (M * E₀) * ((1 + t X) ^ 4 * Real.exp (-κ * t X)) ≤
            (M * E₀) * (16 * (1 + t X / 2) ^ 4 * Real.exp (-κ * t X)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hp (Real.exp_pos (-κ * t X)).le)
            (mul_nonneg hM hE₀)
        calc
          M * E₀ * (1 + t X) ^ 4 * Real.exp (-κ * t X) =
              (M * E₀) * ((1 + t X) ^ 4 * Real.exp (-κ * t X)) := by ring
          _ ≤ (M * E₀) *
              (16 * (1 + t X / 2) ^ 4 * Real.exp (-κ * t X)) := h'
          _ = 16 * M * E₀ * (1 + t X / 2) ^ 4 * Real.exp (-κ * t X) := by ring
  · calc
      ∑ X ∈ S, Real.exp (-(2 * (κ - 1)) * (t X / 2)) =
          ∑ X ∈ S, Real.exp (-(κ - 1) * t X) := by
            refine Finset.sum_congr rfl fun X _ => ?_
            congr 1
            ring
      _ ≤ ∑ X ∈ S, wt κ X (t X) :=
        Finset.sum_le_sum fun X hX => exp_le_wt_of_root X (hroot X hX) (ht₀ X hX)
      _ ≤ K₀ := hcount

end Balaban.SmallField.Def6
