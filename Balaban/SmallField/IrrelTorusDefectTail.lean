/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.Def6InfTail

/-!
# Finite sums of winding contributions

The numerical part of the winding estimate: a polynomial factor of degree four is paid for by
one unit of the decay-rate gap, and the remaining rate controls the sum by the rooted-polymer
count. This lemma applies to either the finite-volume or infinite-volume tail once its terms
have been identified and their anisotropic Cauchy estimates established.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

/-- The finite-tail estimate with all constants visible. `κ₀ + 2 ≤ κ` is the rate gap used in
`poly_exp_tail`; the threshold `τ` need not be positive. -/
theorem norm_sum_winding_le {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (t : ι → ℝ) (f : ι → ℂ) {M E₀ κ κ₀ τ K₀ : ℝ}
    (hM : 0 ≤ M) (hE₀ : 0 ≤ E₀) (hκ : κ₀ + 2 ≤ κ)
    (ht₀ : ∀ X ∈ S, 0 ≤ t X) (htτ : ∀ X ∈ S, τ ≤ t X)
    (hf : ∀ X ∈ S, ‖f X‖ ≤ M * E₀ * (1 + t X) ^ 4 * Real.exp (-κ * t X))
    (hcount : ∑ X ∈ S, Real.exp (-κ₀ * t X) ≤ K₀) :
    ‖∑ X ∈ S, f X‖ ≤ 24 * Real.exp 1 * M * E₀ * Real.exp (-τ) * K₀ := by
  have hME : 0 ≤ M * E₀ := mul_nonneg hM hE₀
  calc
    ‖∑ X ∈ S, f X‖ ≤ ∑ X ∈ S, ‖f X‖ := norm_sum_le _ _
    _ ≤ ∑ X ∈ S, M * E₀ * (1 + t X) ^ 4 * Real.exp (-κ * t X) :=
      Finset.sum_le_sum fun X hX => hf X hX
    _ ≤ ∑ X ∈ S, (24 * Real.exp 1 * M * E₀ * Real.exp (-τ)) *
        Real.exp (-κ₀ * t X) := by
      refine Finset.sum_le_sum fun X hX => ?_
      have h := mul_le_mul_of_nonneg_left
        (poly_exp_tail (ht₀ X hX) (htτ X hX) hκ) hME
      convert h using 1 <;> ring
    _ = (24 * Real.exp 1 * M * E₀ * Real.exp (-τ)) *
        ∑ X ∈ S, Real.exp (-κ₀ * t X) := by rw [Finset.mul_sum]
    _ ≤ (24 * Real.exp 1 * M * E₀ * Real.exp (-τ)) * K₀ :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = 24 * Real.exp 1 * M * E₀ * Real.exp (-τ) * K₀ := rfl

end Balaban.SmallField.Def6
