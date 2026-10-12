/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The finite reductions of P631-INPUTS-2 (§1.2 and §3)

* `wall_bond_le`, `wall_sum_le`: (3.1), complex Cauchy-Schwarz bond by bond, and the sum over the
  crossing bonds of a wall;
* `wall_scalar`: (3.3), `c_E (K₃ ε η)(K₄ ε) = c_E K₃ K₄ B₆ K₅ / β` for `η = B₆ K₅/(β ε²)`;
  `wall_mixed_scalar`: the factor `17/16` of the `β_{n,u}` rescaling (P631 (L));
* `window_margin`: (1.4), `2 a_j - D_j ≥ 3M[R̂_j] - M - 2M₁`;
* `sup_linear_sub_sq`: `x - A x² ≤ 1/(4A)`, the supremum used for (1.5).

The open targets (WINDOW-PAIR, WINDOW-NORMALIZATION, RELATIVE-SOURCE, WALL-CUT) stay inputs of
`ActionConvInput`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Finset

/-- (3.1) for one bond: if `∑ |a_i|² ≤ A²` and `∑ |d_i|² ≤ D²` then `|∑ a_i d_i| ≤ A D`. -/
theorem wall_bond_le {N : ℕ} (a d : Fin N → ℂ) {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : ∑ i, ‖a i‖ ^ 2 ≤ A ^ 2) (hd : ∑ i, ‖d i‖ ^ 2 ≤ D ^ 2) :
    ‖∑ i, a i * d i‖ ≤ A * D := by
  have h1 : ‖∑ i, a i * d i‖ ≤ ∑ i, ‖a i‖ * ‖d i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  have h2 : (∑ i, ‖a i‖ * ‖d i‖) ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖d i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : (∑ i, ‖a i‖ * ‖d i‖) ^ 2 ≤ (A * D) ^ 2 := by
    refine h2.trans ?_
    rw [mul_pow]
    exact mul_le_mul ha hd (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
  exact h1.trans (abs_le_of_sq_le_sq' h3 (by positivity)).2 |>.trans (le_refl _)

/-- (3.1) for a wall: `|∑_{b ∈ E} ∑_i a_{b,i} d_{b,i}| ≤ |E| A D`, if each bond obeys the
bond-wise Euclidean bounds `A`, `D`. -/
theorem wall_sum_le {ι : Type*} {N : ℕ} (E : Finset ι) (a d : ι → Fin N → ℂ) {A D : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D)
    (ha : ∀ b ∈ E, ∑ i, ‖a b i‖ ^ 2 ≤ A ^ 2) (hd : ∀ b ∈ E, ∑ i, ‖d b i‖ ^ 2 ≤ D ^ 2) :
    ‖∑ b ∈ E, ∑ i, a b i * d b i‖ ≤ E.card * (A * D) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b ∈ E, ‖∑ i, a b i * d b i‖ ≤ ∑ _b ∈ E, A * D :=
        Finset.sum_le_sum fun b hb => wall_bond_le _ _ hA hD (ha b hb) (hd b hb)
    _ = _ := by simp

/-- (3.3): `c_E (K₃ ε η)(K₄ ε) = c_E K₃ K₄ B₆ K₅ β⁻¹` for `η = B₆ K₅/(β ε²)`. -/
theorem wall_scalar (cE K3 K4 B6 K5 β ε : ℝ) (hβ : β ≠ 0) (hε : ε ≠ 0) :
    cE * (K3 * ε * (B6 * K5 / (β * ε ^ 2))) * (K4 * ε) = cE * K3 * K4 * B6 * K5 / β := by
  field_simp

/-- The factor of P631 (L): if `|β_{n,u}| ≤ (17/16) β` then
`|β_{n,u}| · (c_E K₃ K₄ B₆ K₅ β⁻¹) ≤ (17/16) c_E K₃ K₄ B₆ K₅`. -/
theorem wall_mixed_scalar {βu β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) (h : |βu| ≤ 17 / 16 * β) :
    |βu| * (C / β) ≤ 17 / 16 * C := by
  rw [mul_div_assoc', div_le_iff₀ hβ]
  nlinarith [abs_nonneg βu]

/-- (1.4): with `a_j = 2M R̂_j - M - 2M₁`, `D_j = M(R̂_{j-1} - 1) - 2M₁`, `M ≥ 0`, `R̂_{j-1} ≤ R̂_j`:
`2 a_j - D_j ≥ 3 M R̂_j - M - 2 M₁`. -/
theorem window_margin {M M₁ R Rp : ℝ} (hM : 0 ≤ M) (hR : Rp ≤ R) :
    3 * M * R - M - 2 * M₁ ≤ 2 * (2 * M * R - M - 2 * M₁) - (M * (Rp - 1) - 2 * M₁) := by
  nlinarith [mul_le_mul_of_nonneg_left hR hM]

/-- `x - A x² ≤ 1/(4A)` for `A > 0` (the supremum used for (1.5)). -/
theorem sup_linear_sub_sq {A : ℝ} (hA : 0 < A) (x : ℝ) : x - A * x ^ 2 ≤ 1 / (4 * A) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * A * x - 1)]

end Balaban.LargeField.ActionConv
