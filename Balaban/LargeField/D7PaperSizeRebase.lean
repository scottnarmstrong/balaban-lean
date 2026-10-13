/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7FineSize
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity

/-!
# Rebasing a bound in the papers' size to the fine size (VMOD-43 §5.3)

This is algebra.  If a size `D_P` satisfies `D_P ≥ a D - b` (`a > 0`, `b ≥ 0`), then a bound
`B₀ e^{-κ D_P}` gives `B₀ e^{κ b} e^{-κ a D}`, and `B₀ e^{-(3κ/2) D_P}` gives
`B₀ e^{3κ b/2} e^{-(3κ/2) a D}`.

* `paperRebase`, `paperRebase_threeHalves`: the real statements.
* `paperRebase_of_paperFineRealization`, `paperRebase_threeHalves_of_paperFineRealization`:
  the same for `D = d7SizeAt F k Om X`, under the hypothesis
  `hPaper : D_P ≥ a * d7SizeAt F k Om X - b`.  This hypothesis is the open assertion
  `OPEN-PAPER-FINE-REALIZATION` (`Def7FineSize.lean`); it is NOT proved here.  Neither is the
  comparison of the fine surrogate `dcovModAll` with the papers' continuum size, the aligned lift
  of the open cubes, or the component compatibility.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban

/-- **Rate rebase.** From `D_P ≥ a D - b` and `κ ≥ 0`, `B₀ ≥ 0`:
`B₀ e^{-κ D_P} ≤ B₀ e^{κ b} e^{-κ a D}`. -/
theorem paperRebase {a b D DP κ B₀ : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B₀) (hD : a * D - b ≤ DP) :
    B₀ * Real.exp (-κ * DP) ≤ B₀ * Real.exp (κ * b) * Real.exp (-(κ * a) * D) := by
  have h1 : -κ * DP ≤ κ * b + -(κ * a) * D := by nlinarith [mul_le_mul_of_nonneg_left hD hκ]
  calc B₀ * Real.exp (-κ * DP) ≤ B₀ * Real.exp (κ * b + -(κ * a) * D) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hB
    _ = _ := by rw [Real.exp_add]; ring

/-- **Rate rebase at rate `3κ/2`**: `B₀ e^{-(3κ/2) D_P} ≤ B₀ e^{(3κ/2) b} e^{-(3κ/2) a D}`. -/
theorem paperRebase_threeHalves {a b D DP κ B₀ : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B₀)
    (hD : a * D - b ≤ DP) :
    B₀ * Real.exp (-(3 * κ / 2) * DP) ≤
      B₀ * Real.exp ((3 * κ / 2) * b) * Real.exp (-((3 * κ / 2) * a) * D) :=
  paperRebase (by positivity) hB hD

section Instance

variable {S : Setting} {n : ℕ → ℕ} {M K m₀ m₁ : ℕ}

/-- The rebase for the fine size `d7SizeAt`, under the open assertion
`hPaper` (`OPEN-PAPER-FINE-REALIZATION`). -/
theorem paperRebase_of_paperFineRealization (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ)
    (Om : Set (Torus S.d (n k))) (X : Finset (Torus S.d (n k))) {a b DP κ B₀ : ℝ}
    (hκ : 0 ≤ κ) (hB : 0 ≤ B₀) (hPaper : a * d7SizeAt F k Om X - b ≤ DP) :
    B₀ * Real.exp (-κ * DP) ≤
      B₀ * Real.exp (κ * b) * Real.exp (-(κ * a) * d7SizeAt F k Om X) :=
  paperRebase hκ hB hPaper

/-- The rebase at rate `3κ/2` for the fine size, under `hPaper`. -/
theorem paperRebase_threeHalves_of_paperFineRealization (F : FineSizeFrame S n M K m₀ m₁)
    (k : ℕ) (Om : Set (Torus S.d (n k))) (X : Finset (Torus S.d (n k))) {a b DP κ B₀ : ℝ}
    (hκ : 0 ≤ κ) (hB : 0 ≤ B₀) (hPaper : a * d7SizeAt F k Om X - b ≤ DP) :
    B₀ * Real.exp (-(3 * κ / 2) * DP) ≤
      B₀ * Real.exp ((3 * κ / 2) * b) * Real.exp (-((3 * κ / 2) * a) * d7SizeAt F k Om X) :=
  paperRebase_threeHalves hκ hB hPaper

end Instance

end Balaban.LargeField.Def7
