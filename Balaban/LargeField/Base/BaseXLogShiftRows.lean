/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseXLogShiftPhys
public import Balaban.LargeField.Base.BaseXLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact core agreement of the rows of the shifted logarithm (item 4)

The coefficient `c(s) = P_e + σ_s (1 - Q_φ)` is site-diagonal: its entry at `((y,i),(z,j))` is
`δ_{yz}` times an expression in `φ₀(y)` and `σ_s(y)`.  Under the hypotheses of `baseCovX_exact`
(every active cube inside `Sr` or disjoint from `Y ⊇ Sr`, parameters agreeing on the cubes inside
`Sr`), `σ_s(y)` for `y ∈ Y` only reads the cubes inside `Sr`, so the rows of `c(s)` at `Y` do not
depend on `s`; with `baseCovX_exact` for `C_x(s)` the integrands, hence the rows of
`baseCovXLogShift`, agree.

* `fieldProj_apply`, `baseCovXCoef_apply`: entry formulas;
* `cubeSigma_eq_of_dich`, `baseCovXCoef_rows_exact`: rows of `σ_s` and `c(s)`;
* `baseCovXShiftIntegrand_rows_exact`, `baseCovXLogShift_rows_exact`: rows of the integrand (every
  `x ≥ 0`) and of its integral.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Matrix Balaban Balaban.Multiscale Balaban.Localization MeasureTheory Set

section Entries

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}

theorem fieldProj_apply (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ)
    (p q : G.Ω 1) (i j : Fin N) :
    fieldProj G φ (p, i) (q, j) =
      if p = q then φ p i * (∑ r, φ p r * φ p r)⁻¹ * φ p j else 0 := by
  unfold fieldProj
  by_cases h : p = q
  · subst h
    simp [fieldMul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, restrictField]
  · simp [fieldMul, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, h]

/-- **Entries of the large-`x` coefficient.** -/
theorem baseCovXCoef_apply (s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ)
    (φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ) (p q : G.Ω 1 × Fin N) :
    baseCovXCoef G s φ p q = basePart (restrictField G φ) p q +
      cubeSigma G s p.1 * ((1 : Matrix (G.Ω 1 × Fin N) (G.Ω 1 × Fin N) ℂ) p q - fieldProj G φ p q) := by
  unfold baseCovXCoef
  rw [Matrix.add_apply]
  congr 1
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single p]
  · simp [liftOp]
  · intro r _ hr
    have : liftOp N (Matrix.diagonal (cubeSigma G s)) p r = 0 := by
      simp only [liftOp, Matrix.diagonal_apply]
      split_ifs with h1 h2 <;> first | rfl | (exfalso; apply hr; exact Prod.ext h2.symm h1.symm)
    rw [this, zero_mul]
  · simp

theorem baseCovXCoef_apply_eq {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} {p : G.Ω 1 × Fin N}
    (h : cubeSigma G s p.1 = cubeSigma G s' p.1) (q : G.Ω 1 × Fin N) :
    baseCovXCoef G s φ p q = baseCovXCoef G s' φ p q := by
  rw [baseCovXCoef_apply, baseCovXCoef_apply, h]

end Entries

section Exact

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ} {aT ν Cx : ℝ}
  {s s' : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
  {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}

/-- **Rows of `σ_s`.**  If every active cube lies inside `Sr` or is disjoint from `Y ⊇ Sr` and the
products agree on the cubes inside `Sr`, then `σ_s(y) = σ_{s'}(y)` for `y ∈ Y`. -/
theorem cubeSigma_eq_of_dich (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
      (coverOf G).sProd s q = (coverOf G).sProd s' q)
    {y : G.Ω 1} (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    cubeSigma G s y = cubeSigma G s' y := by
  unfold cubeSigma
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases hc : (coverOf G).chi q y = 0
  · simp [hc]
  · have hb := mem_intBox_of_chi_ne_zero S hq hc
    by_cases h0 : (coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0
    · rcases hdich q hq h0 with h | h
      · rw [hagree q hq h]
      · exact absurd hy (h y hb)
    · push Not at h0
      rw [h0.1, h0.2]

/-- **Rows of the large-`x` coefficient** at `Y` do not depend on `s`. -/
theorem baseCovXCoef_rows_exact (S : Dec2.XCover (coverOf G) G a aT ν Cx)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
      (coverOf G).sProd s q = (coverOf G).sProd s' q)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (y z : G.Ω 1 × Fin N)
    (hy : (y.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    baseCovXCoef G s φ y z = baseCovXCoef G s' φ y z :=
  baseCovXCoef_apply_eq (cubeSigma_eq_of_dich S hdich hagree hy) z

/-- **Exact core agreement of the rows of the shifted logarithm** (item 4).  Under the hypotheses
of `baseCovX_exact` (every active cube inside `Sr` or disjoint from `Y ⊇ Sr`, parameters agreeing
on the cubes inside `Sr`, `Y` containing the neighbours of `Sr`), the integrand
`(1+x)⁻¹ c(s) - C_x(s)` has the same rows at the sites of `Y` for `s` and `s'`, for every
`x ≥ 0`; hence so do the rows of `baseCovXLogShift`. -/
theorem baseCovXLogShift_rows_exact {κ δ : ℝ} {α : G.Ω 1 → ℂ}
    (S : Dec2.XCover (coverOf G) G a aT ν Cx) (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
    (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hα : AdmPot G α)
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ) (hSY : Sr ⊆ Y)
    (hdich : ∀ q ∈ (coverOf G).cubeIdx,
      ((coverOf G).sProd s q ≠ 0 ∨ (coverOf G).sProd s' q ≠ 0) →
      SubI G (intBox q) Sr ∨ DisjI G (intBox q) Y)
    (hagree : ∀ q ∈ (coverOf G).cubeIdx, SubI G (intBox q) Sr →
      (coverOf G).sProd s q = (coverOf G).sProd s' q)
    (hnbr : ∀ p q : G.Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
      ((q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
        (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
            (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
          (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
            (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
          G.blk (G.layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) →
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ} (hφ : IsConstraintField G δ φ)
    (y z : G.Ω 1 × Fin N) (hy : (y.1 : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    (∀ x : ℝ, 0 ≤ x → baseCovXShiftIntegrand G a aT ν α s φ x y z =
      baseCovXShiftIntegrand G a aT ν α s' φ x y z) ∧
    baseCovXLogShift G a aT ν α s φ y z = baseCovXLogShift G a aT ν α s' φ y z := by
  have hpt : ∀ x : ℝ, 0 ≤ x → baseCovXShiftIntegrand G a aT ν α s φ x y z =
      baseCovXShiftIntegrand G a aT ν α s' φ x y z := by
    intro x hx
    have h := baseCovX_exact (xCover_add_mass S hx) hCx hκ hM hδ hsm hα hs hs' hSY hdich hagree
      hnbr hφ y z hy
    unfold baseCovXShiftIntegrand
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    rw [baseCovXCoef_rows_exact S hdich hagree y z hy, h]
  refine ⟨hpt, ?_⟩
  unfold baseCovXLogShift
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => hpt x (mem_Ioi.mp hx).le

end Exact

end Balaban.LargeField.Base
