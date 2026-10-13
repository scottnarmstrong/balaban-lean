/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecSqrtCutFactor
public import Balaban.Localization.Decoupled2FpX
public import Balaban.Localization.Decoupled2Self

/-!
# The decoupled covariance and its square root for a pair `(C, H)`

For a cover `C` and a separate operator generating set `H` (namespace `Dec2`), this file writes
down the constraint matrices `decM`, `decN`, `decPi`, the covariance `decCov`, the integrand
`decSqrtInt` and the square root `decCovSqrt`: the formulas of the one-generating-set chain
(`DecoupledCovariance.lean`, `DecoupledCovBound.lean`, `DecoupledSqrt.lean`) with the Green's
operator `Gsx G ...` replaced by `Dec2.Gsx C H ...`; the Dirichlet operator is that of `H`.

* `decM_self`, ..., `decCovSqrt_self`: at `C = coverOf G`, `H = G` they are the landed objects.
* `decCov_BD_of_GsxBD`, `decCovSqrt_BD_of_GsxBD`: block diagonality of the covariance and of its
  square root, from block diagonality of `Dec2.Gsx C H` (explicit hypothesis) and the condition
  `HRespects` that the operator of `H` does not connect the core of `C` across the blocks.
* `Gsx_BD`: block diagonality of `Dec2.Gsx C H` for a union of nearest-neighbour components of
  `Yreg C H s`, under `XFootLocal C H` and `HatConn C H`.

The physical statement `OPEN-P6-MIXED-COV-ROWS` of `notes/phase1/VMOD-34.md` (bounds, locality in
the data with two backgrounds, the `unitQ/unitP` splitting) is NOT proved here.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Defs

variable (C : DecCover d L N₁ m₁ (k + 1)) (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
  (a : ℕ → ℝ) (aT x ν : ℝ) (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
  (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)

/-- `M_{x,s} = φ₀² - K_x(φ₀) G_{k,x,s} φ₀` for the pair `(C, H)`. -/
noncomputable def decM : Matrix (H.Ω 1) (H.Ω 1) ℂ :=
  constraintM (xDirichletOperator H a aT x ν α) (Gsx C H a aT x ν α s) (restrictField H φ)

/-- `N_{x,s} f = φ₀ f - K_x(φ₀) G_{k,x,s} f` for the pair `(C, H)`. -/
noncomputable def decN : Matrix (H.Ω 1) (H.Ω 1 × Fin N) ℂ :=
  constraintN (xDirichletOperator H a aT x ν α) (Gsx C H a aT x ν α s) (restrictField H φ)

/-- `Π_{x,s} = G_{k,x,s} φ₀ M_{x,s}⁻¹ N_{x,s}` for the pair `(C, H)`. -/
noncomputable def decPi : Matrix (H.Ω 1 × Fin N) (H.Ω 1 × Fin N) ℂ :=
  liftOp N (Gsx C H a aT x ν α s) * fieldMul (restrictField H φ) *
    (decM C H a aT x ν α s φ)⁻¹ * decN C H a aT x ν α s φ

variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- The decoupled constrained covariance of the pair `(C, H)`. -/
noncomputable def decCov (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) +
    (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
      (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
        (liftOp N (Gsx C H a aT x ν α s) - decPi C H a aT x ν α s φ) * (liftRect N Q)ᵀ *
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))

end Defs

/-- The integrand `x^{-1/2} C_x(s)` of `C^{1/2}` for the pair `(C, H)`. -/
noncomputable def decSqrtInt (C : DecCover d L N₁ m₁ (k + 1))
    (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ) (x : ℝ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • decCov C H a aT x ν α s φ Q P

/-- The square root `C^{1/2}(s) = π⁻¹ ∫₀^∞ x^{-1/2} C_x(s) dx` for the pair `(C, H)`. -/
noncomputable def decCovSqrt (C : DecCover d L N₁ m₁ (k + 1))
    (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ) (α : H.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    {κι : Type*} [Fintype κι] [DecidableEq κι]
    (Q : Matrix κι (H.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    Matrix (κι × Fin N) (κι × Fin N) ℂ :=
  ((1 / Real.pi : ℝ) : ℂ) •
    intMat (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (decSqrtInt C H a aT ν α s φ Q P)

/-! ### Reduction to the single generating set -/

section Self

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (a : ℕ → ℝ) (aT x ν : ℝ)
  (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
  (φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
  {κι : Type*} [Fintype κι] [DecidableEq κι]

theorem decM_self :
    decM (coverOf G) G a aT x ν α s φ = Balaban.Localization.decM G a aT x ν α s φ := rfl

theorem decN_self :
    decN (coverOf G) G a aT x ν α s φ = Balaban.Localization.decN G a aT x ν α s φ := rfl

theorem decPi_self :
    decPi (coverOf G) G a aT x ν α s φ = Balaban.Localization.decPi G a aT x ν α s φ := rfl

theorem decCov_self (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decCov (coverOf G) G a aT x ν α s φ Q P =
      Balaban.Localization.decCov G a aT x ν α s φ Q P := rfl

theorem decSqrtInt_self (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decSqrtInt (coverOf G) G a aT ν α s φ Q P x =
      Balaban.Localization.decSqrtInt G a aT ν α s φ Q P x := rfl

theorem decCovSqrt_self (Q : Matrix κι (G.Ω 1) ℂ) (P : Matrix κι κι ℂ) :
    decCovSqrt (coverOf G) G a aT ν α s φ Q P =
      Balaban.Localization.decCovSqrt G a aT ν α s φ Q P := rfl

end Self

end Balaban.Localization.Dec2
