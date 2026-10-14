/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetRotation
public import Balaban.Fluctuation.LocalHatTerm

/-!
# Rotation covariance of the local class (clause `rotE`), real rotations

The square root of the decoupled covariance is covariant under spin rotations
(`decCovSqrt_rot_cover`, in the cover form of the integrability theorem
`integrable_decSqrtInt_cover`; `decCovSqrt_rot` for `CovStanding`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Localization.DecEquiv MeasureTheory
  Finset Matrix

section Sqrt

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]

/-- **Covariance of the square root `C^{1/2}(s)` under spin rotations** (cover form): the
hypotheses are those of `integrable_decSqrtInt_cover`, so that the entrywise integral commutes with
the two-sided constant factor. -/
theorem decCovSqrt_rot_cover {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {a : ℕ → ℝ}
    {aT ν : ℝ} {α : G.Ω 1 → ℂ} {κ Cx : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hU : IsUnitLattice G Q P) :
    decCovSqrt G a aT ν α s (rotSite R φ) Q P =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * decCovSqrt G a aT ν α s φ Q P *
        rotLift Rᵀ := by
  have hint := fun p q => integrable_decSqrtInt_cover hfam hφ hδ hsm hU p q
  have hfun : decSqrtInt G a aT ν α s (rotSite R φ) Q P =
      fun x => (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) *
        decSqrtInt G a aT ν α s φ Q P x * rotLift Rᵀ := by
    funext x
    unfold decSqrtInt
    rw [decCov_rot hR, Matrix.mul_smul, Matrix.smul_mul]
  unfold decCovSqrt
  rw [hfun, intMat_conj hint, Matrix.mul_smul, Matrix.smul_mul]

/-- **Covariance of the square root `C^{1/2}(s)` under spin rotations**, under `CovStanding`. -/
theorem decCovSqrt_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) {a : ℕ → ℝ}
    {aT ν : ℝ} {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {δ : ℝ}
    {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
    (H : CovStanding G a aT ν α κ s δ φ Q P) :
    decCovSqrt G a aT ν α s (rotSite R φ) Q P =
      (rotLift R : Matrix (κι × Fin N) (κι × Fin N) ℂ) * decCovSqrt G a aT ν α s φ Q P *
        rotLift Rᵀ :=
  decCovSqrt_rot_cover hR (fun x hx => (H.fam x hx).toCover) H.field H.nonneg H.small H.unit

end Sqrt

end Balaban.Fluctuation
