/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Operators.KerBound
public import Balaban.LargeField.Budget.Exponents
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-!
# The small factor of the removed outcome of `R` (P7 (3.10′)): the exponent assembly (W876)

`notes/phase1/LF4R-PLAN.md`, first leaf.  Theorem III.8.9 (c) of the reconstruction: the removed
operator `T^rem` of a ripe component `Z` with localized history `𝔞` satisfies
`∫ |T^rem e^{E_k|Z|}| ≤ e^{-A₂ λ̂_k^{p₂} - H_k |Z|_k}`.  The proof combines the window integral
(III.8.5) at `γ = 0`, the ripeness lower bound `G^pre_k ≥ 2 A₂ λ̂_k^{p₂} + 1` and the arithmetic
`C_R λ̂_k^{2d+1} ≤ A₂ λ̂_k^{p₂}`.

This file does the assembly.  The window integral (III.8.5) is the **hypothesis** `hwin`, in the
form of the landed bound predicate `KerBound` with the exponent `κ^pre - C_R λ̂^{2d+1}` (the
window-proportional terms having been absorbed into `κ^pre` by `c₁ ≥ C_W`, `c₂ ≥ C'_W`, as in
the proof of Theorem III.8.9 (a)); it is the content of Lemma III.8.7, not proved here.

* `KerBound.mono`: `KerBound` with a larger exponent implies it with a smaller one.
* `CR_pow_le_A2_pow`: `C_R x^{2d+1} ≤ A₂ x^{p₂}` for `x ≥ 1` from `C_R ≤ A₂ x^{p₂ - 2d - 1}`.
  The landed condition (Λ10) (`LamConditions.l10`) does **not** give this: it bounds
  `C_R x^{2d+1}` by `A'₃ x^{p_R}` with `p_R > p₂ + 2d`.
* `removed_kerBound_logC_of_window`: the exponent assembly, for the removed operator `T`, with the
  history weight `log C(𝔞)` kept in the exponent (needed for the sum over histories).
-/

@[expose] public section

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Mono

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

/-- The bound (1.26) with a larger exponent implies the bound with a smaller one. -/
theorem KerBound.mono {a : LocalHistory S n M K} {k : ℕ} {A : Set (InternalVars a k)}
    {T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)}
    {κ κ' : ℝ} (h : KerBound a k T κ') (hκ : κ ≤ κ') : KerBound a k T κ := by
  intro hv g hg par
  refine (h hv g hg par).trans (ENNReal.ofReal_le_ofReal ?_)
  exact Real.exp_le_exp.2 (by linarith)

/-- **The removed operator, exponent assembly (P7 (3.10′))**, with the history weight kept: the
exponent is `A₂ λ^{p₂} + H_k M^d c + 1 + log C(𝔞)`.  Hypotheses: `G^pre = κ^pre - log C - H_k M^d c`,
ripeness `G^pre ≥ 2 A₂ λ^{p₂} + 1`, `C_R λ^{2d+1} ≤ A₂ λ^{p₂}`, and the window bound (III.8.5)
at `γ = 0` as `KerBound … (κ^pre - C_R λ^{2d+1})`. -/
theorem removed_kerBound_logC_of_window {a : LocalHistory S n M K} {k : ℕ}
    {A : Set (InternalVars a k)}
    {T : LFKernel (OutT N R a k) (SubCfg N a k A) (EuclideanSpace ℝ (Fin N)) (GIdx S n M K N)}
    {P : BudgetConsts} {c : ℕ} {κpre logC Gp : ℝ}
    (hG : Gp = P.budgetG S k κpre logC c)
    (hrip : 2 * S.A2 * S.lam k ^ S.p2 + 1 ≤ Gp)
    (hCR : S.CR * S.lam k ^ (2 * S.d + 1) ≤ S.A2 * S.lam k ^ S.p2)
    (hwin : KerBound a k T (κpre - S.CR * S.lam k ^ (2 * S.d + 1))) :
    KerBound a k T
      (S.A2 * S.lam k ^ S.p2 + HRun P.H0 P.beta k * BudgetConsts.cubeVol S c + 1 + logC) := by
  refine hwin.mono ?_
  have h : Gp = κpre - logC - HRun P.H0 P.beta k * BudgetConsts.cubeVol S c := hG
  linarith

end Mono

/-- `C_R x^{2d+1} ≤ A₂ x^{p₂}` from `C_R ≤ A₂ x^{p₂ - (2d+1)}` (`x ≥ 0`, `2d+1 ≤ p₂`). -/
theorem CR_pow_le_A2_pow {S : Setting} {x : ℝ} (hx : 0 ≤ x) (hp : 2 * S.d + 1 ≤ S.p2)
    (h : S.CR ≤ S.A2 * x ^ (S.p2 - (2 * S.d + 1))) :
    S.CR * x ^ (2 * S.d + 1) ≤ S.A2 * x ^ S.p2 := by
  calc S.CR * x ^ (2 * S.d + 1) ≤ S.A2 * x ^ (S.p2 - (2 * S.d + 1)) * x ^ (2 * S.d + 1) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = S.A2 * x ^ S.p2 := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hp]

end Balaban.LargeField
