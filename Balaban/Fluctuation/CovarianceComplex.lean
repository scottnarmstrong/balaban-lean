/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Covariance
public import Balaban.Analysis.MatrixDetExp

/-!
# Lemma 2.4 (c): the determinant identity for complex data (FLUCTUATION.md §2.4)

For complex data in the domain of Theorem I-4c, `𝕃 = decLog = logMat 𝒜` satisfies
`exp 𝕃 = 𝒜` (landed `exp_logMat`), hence `det 𝒜 = exp (tr 𝕃)` by `det (exp A) = exp (tr A)`.
So `∑_y tr 𝕃(y,y)` is a logarithm of `det 𝒜` and `det C^{(k)} = exp (-∑_y tr 𝕃(y,y))`: the
identity `½ log det C = -½ ∑_y tr 𝕃(y,y)` holds with `log det C` *defined* as the branch
`-∑_y tr 𝕃(y,y)`, the branch that is analytic in the data and equals the real logarithm for
real data (`lemma24_c_logdet`).
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Matrix

namespace Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- **Lemma 2.4 (c), logarithm and determinant, complex data.** With `𝕃 = decLog = log 𝒜`,
`det 𝒜 = exp (∑_y tr 𝕃(y,y))` and `det C^{(k)} = exp (-∑_y tr 𝕃(y,y))`. -/
theorem lemma24_c_logdet_complex (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) :
    (covOp G a aT ν α φ (unitQ G) (unitP G)).det =
        Complex.exp (∑ y : unitPts G, ∑ i : Fin N,
          decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (y, i) (y, i)) ∧
      (covOp G a aT ν α φ (unitQ G) (unitP G))⁻¹.det =
        Complex.exp (-∑ y : unitPts G, ∑ i : Fin N,
          decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (y, i) (y, i)) := by
  have hU := isUnitLatticeB_unit (G := G)
  have hR := resOK_covOp hfam hφ hδ hsm hU
  have hL := decLog_one_eq_logMat hfam hφ hδ hsm hU
  have hsum : (∑ y : unitPts G, ∑ i : Fin N,
      decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (y, i) (y, i)) =
      (logMat (covOp G a aT ν α φ (unitQ G) (unitP G))).trace := by
    rw [hL, Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [Fintype.sum_prod_type]
  have hdet : (covOp G a aT ν α φ (unitQ G) (unitP G)).det =
      Complex.exp (logMat (covOp G a aT ν α φ (unitQ G) (unitP G))).trace := by
    rcases isEmpty_or_nonempty (unitPts G × Fin N) with h | h
    · simp [Matrix.det_isEmpty, Matrix.trace]
    · rw [← det_exp_eq_exp_trace, exp_logMat hR]
  refine ⟨by rw [hsum]; exact hdet, ?_⟩
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdet, hsum, ← Complex.exp_neg]

end Balaban.Fluctuation
