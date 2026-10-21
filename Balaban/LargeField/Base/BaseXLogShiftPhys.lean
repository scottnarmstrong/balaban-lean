/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXLogShiftInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The shifted logarithm at the physical point (item 3)

At `s ≡ 1` and `φ₀·φ₀ = 1` the large-`x` coefficient is the identity, `c = 1`
(`baseCovXCoef_one`), the shifted integrand is `(1+x)⁻¹ - C_x`, and `baseCovXLogShift` is the
logarithm `logMat A_e` of the first step's operator `A_e = Q_e (H ⊗ I) Q_e + P_e`
(`baseCovXLogShift_physical`, from `baseCovX_log`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Multiscale Balaban.Localization MeasureTheory Set

section Phys

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}

/-- At the physical parameters `s ≡ 1` the multiplier `σ_s` is the identity. -/
theorem cubeSigma_one (S : Dec2.XCover (coverOf G) G a aT ν Cx) :
    cubeSigma G (fun _ => 1) = fun _ => 1 := by
  funext y
  unfold cubeSigma
  simp only [(coverOf G).sProd_one, one_mul]
  have := S.sum_chi y y.2
  exact_mod_cast this

/-- **At the physical point the large-`x` coefficient is the identity**: `c = 1` when `s ≡ 1`
and `φ₀·φ₀ = 1`. -/
theorem baseCovXCoef_one (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
    (hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1) :
    baseCovXCoef G (fun _ => 1) φ = 1 := by
  have hQ : fieldProj G φ = basePart (restrictField G φ) := by
    unfold fieldProj basePart
    have : (fun y : G.Ω 1 => (∑ i, φ y i * φ y i)⁻¹) = fun _ => 1 := by
      funext y; rw [hsq y]; simp
    rw [this, Matrix.diagonal_one, Matrix.mul_one]
  unfold baseCovXCoef
  rw [hQ, cubeSigma_one S, Matrix.diagonal_one, liftOp_one, Matrix.one_mul]
  abel

/-- **At the physical point the shifted logarithm is `logMat A_e`** (item 3): for `s ≡ 1` and
`φ₀·φ₀ = 1`, `∫₀^∞ ((1+x)⁻¹ - C_x) dx = log A_e`, the principal logarithm of the first step's
operator `A_e = Q_e (H ⊗ I) Q_e + P_e` (`baseCovX_log`). -/
theorem baseCovXLogShift_physical [Nonempty (G.Ω 1 × Fin N)]
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx)
    (ha0 : a 0 = 2) (ha1 : 0 ≤ a 1) (ha1' : a 1 ≤ 2)
    (haT : aT = 2 * a 1 * (L : ℝ) ^ 2 / (2 * (L : ℝ) ^ 2 - a 1))
    {α : G.Ω 1 → ℂ} (hα : AdmPot G α) (hM : Dec2.cstarX d L Cx ≤ (L : ℝ) ^ m₁)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
    (hφ : IsConstraintField G δ φ) (hsq : ∀ z : G.Ω 1, ∑ i, φ z i * φ z i = 1)
    (y z : G.Ω 1 × Fin N) :
    baseCovXLogShift G a aT ν α (fun _ => 1) φ y z =
      Localization.logMat (baseOp N (restrictField G φ)
        (baseHamiltonian G a ν α (fun _ => 1))) y z := by
  obtain ⟨B, hB, H⟩ := baseCovX_log d L N
  obtain ⟨-, -, -, hd, -⟩ := H S hCx ha0 ha1 ha1' haT hα hM hδ hsm hφ hsq
  rw [← hd y z, ← integral_neg]
  unfold baseCovXLogShift
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
  have hc : ((((1 + x)⁻¹ : ℝ)) : ℂ) = (1 + (x : ℂ))⁻¹ := by push_cast; ring
  simp only [baseCovXShiftIntegrand, baseCovXCoef_one S hsq, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, hc]
  ring

end Phys

end Balaban.LargeField.Base
